
/*--------------------------------------------------------------------*/
/*--- Cache simulation                                    cg_sim.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Cachegrind, a Valgrind tool for cache
   profiling programs.

   Copyright (C) 2002-2017 Nicholas Nethercote
      njn@valgrind.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.

   The GNU General Public License is contained in the file COPYING.
*/

/* Notes:
  - simulates a write-allocate cache
  - (block --> set) hash function uses simple bit selection
  - handling of references straddling two cache blocks:
      - counts as only one cache access (not two)
      - both blocks hit                  --> one hit
      - one block hits, the other misses --> one miss
      - both blocks miss                 --> one miss (not two)
*/

// #include "cg_page.h"
// #include "hashmap.h"
// #include "vg_libciface.h"
#include <stdint.h>
#include <stdbool.h>
#include "pub_tool_basics.h"

#define PAGE_PROF

#ifdef PAGE_PROF

// global performance metric
static ULong n_local_page_acc_cnt = 0;
static ULong n_remote_page_acc_cnt = 0;
static ULong n_local_page_allocate_cnt = 0;
static ULong n_remote_page_allocate_cnt = 0;
static ULong migrate_cnt = 0;


static ULong n_local_page = 0;
static ULong n_remote_page = 0;
static ULong n_global_page = 0;

static const Long page_offset = 12;

struct hashmap page_table;
static ULong tik = 0;
static int strategy = 0;

static void *hashmap_get(struct hashmap *map, const void *key);
static bool hashmap_scan(struct hashmap *map, bool (*iter)(const void *item, void *udata), void *udata);

void strategy_init(int clo_strategy){
    strategy = clo_strategy;
}

typedef struct lru_entry{
    ULong vpage;
    ULong cnt;
} LRU_ENTRY;

typedef struct page_info{
    ULong phys_page; // physical page id
    ULong acc_cnt_tlb;  // how many times this page has been accessed at pte, increase after each true access
    ULong acc_cnt_llc;  // how many times this page has been accessed after last miss

    // period info and epoch info, used for hot table updater
    // we temporarily use these counters to simulate the function of cm-sketch
    ULong acc_cnt_tlb_period;  
    ULong acc_cnt_llc_period;  

    ULong acc_cnt_tlb_epoch;  
    ULong acc_cnt_llc_epoch;  
    
    // for linux page management policies
    ULong age;          // increase after each scan if a bit is 0
    ULong acc_cnt_a_bit; 
    Bool a_bit;         // access bit
    Bool is_local;      // is this page local or remote

} PAGE_INFO;

typedef struct page_entry {
    ULong virt_page; // virtual page id
    PAGE_INFO pg_info;  // page info
}PAGE_ENTRY;

// BitMap table
#define BITMAP_TABLE_SIZE 1024
#define TIMESLICE 1000000  // how many instructions are a timeslice stand for

#define CM_SKETCH_TABLE_SIZE (16*1024)
#define CM_SKETCH_TABLE_NUM 3
#define EPOCH (2*64*TIMESLICE)

typedef struct _bitmap_table_entry{
    bool valid;
    Addr ppn; // hot pages address
    ULong access_bitmap; // access bitmap in 64 time slices
    uint64_t acc_cnt_llc_epoch; // this term is not in the hardware, but we add it for the convience of software realization
} BITMAP_ENTRY;

typedef struct _bitmap_table{
    BITMAP_ENTRY _bitmap_table[BITMAP_TABLE_SIZE];  // we organize this array as a queue
    uint64_t used;  // number of entries in the table
} BITMAP_TABLE;

BITMAP_TABLE bitmap_table;


void print_bitmap_table(int len){
    if (len > bitmap_table.used)
        len = bitmap_table.used;
    VG_(printf)("start profiling the bitmap table at tik %lu, used item %lu\n", tik, bitmap_table.used);
    for (int i = 0; i < len; i++){
        VG_(printf)("valid: %d  ppn: %llx  access_bitmap: %llx  acc_cnt_llc_epoch: %llu\n", bitmap_table._bitmap_table[i].valid, bitmap_table._bitmap_table[i].ppn,
                                                                                          bitmap_table._bitmap_table[i].access_bitmap, bitmap_table._bitmap_table[i].acc_cnt_llc_epoch);
    }
    VG_(printf)("end profiling\n");
}

void bitmap_table_refresh(){
    bitmap_table.used = 0;
    for (int i = 0; i < BITMAP_TABLE_SIZE; i++){
        bitmap_table._bitmap_table[i].valid = False;
        bitmap_table._bitmap_table[i].ppn = 0;
        bitmap_table._bitmap_table[i].access_bitmap = 0;
        bitmap_table._bitmap_table[i].acc_cnt_llc_epoch = 0;
    }
}

void bitmap_table_pop_enrty(){
    if (bitmap_table.used == 0){
        VG_(tool_panic)("can't pop element from an empty bitmap table!");
    }
    else{
        for (int i = 0; i < bitmap_table.used && i < BITMAP_TABLE_SIZE; i++){
            if (i == BITMAP_TABLE_SIZE - 1){
                bitmap_table._bitmap_table[i].valid = False;
                bitmap_table._bitmap_table[i].ppn = 0;
                bitmap_table._bitmap_table[i].access_bitmap = 0;
                bitmap_table._bitmap_table[i].acc_cnt_llc_epoch = 0;
            }
            else
                bitmap_table._bitmap_table[i] = bitmap_table._bitmap_table[i+1];
        }
        bitmap_table.used--;
        
    }
}

void bitmap_table_add_entry(Addr x){
    Addr vpage = x >> page_offset; 
    PAGE_ENTRY* entry = hashmap_get(&page_table, &vpage); 
    if (entry == NULL){
        VG_(tool_panic)("page inserted is never accessed, that's strange!"); 
    }
    uint64_t acc_cnt_llc_epoch = entry->pg_info.acc_cnt_llc_epoch;

    bitmap_table._bitmap_table[bitmap_table.used].valid = True;
    bitmap_table._bitmap_table[bitmap_table.used].ppn = x >> page_offset; 
    bitmap_table._bitmap_table[bitmap_table.used].access_bitmap = 1;
    bitmap_table._bitmap_table[bitmap_table.used].acc_cnt_llc_epoch = acc_cnt_llc_epoch;
}

inline void bitmap_table_delete_entry(int position){
    if (position >= bitmap_table.used)
        VG_(tool_panic)("position >= bitmap_table.used when delete element!"); 

    for(int i = position; i < bitmap_table.used; i++){
        if (i == BITMAP_TABLE_SIZE - 1){
            bitmap_table._bitmap_table[i].valid = False;
            bitmap_table._bitmap_table[i].ppn = 0;
            bitmap_table._bitmap_table[i].access_bitmap = 0;
            bitmap_table._bitmap_table[i].acc_cnt_llc_epoch = 0;
        }
        else{
            bitmap_table._bitmap_table[i] = bitmap_table._bitmap_table[i+1];
        }
    }
    bitmap_table.used -= 1;

    bitmap_table._bitmap_table[bitmap_table.used].valid = False;
    bitmap_table._bitmap_table[bitmap_table.used].ppn = 0;
    bitmap_table._bitmap_table[bitmap_table.used].access_bitmap = 0;
    bitmap_table._bitmap_table[bitmap_table.used].acc_cnt_llc_epoch = 0;
}

inline void bitmap_table_insert_entry(Addr ppn, uint64_t acc_cnt_llc_epoch, int position){

    // clamp
    if (position > BITMAP_TABLE_SIZE - 1){
        return ;
    }
    
    Addr vpage = ppn; 
    ULong _bitmap = 1;
    for (int i = 0; i < bitmap_table.used; i++){
        if (bitmap_table._bitmap_table[i].ppn == vpage){  // this means the address is already in the table
            _bitmap = (bitmap_table._bitmap_table[i].access_bitmap | 1);
            bitmap_table_delete_entry(i);
        }
    }

    // the table is full, delete the last one
    if (bitmap_table.used > BITMAP_TABLE_SIZE - 1){
        bitmap_table.used = BITMAP_TABLE_SIZE - 1;
    }

    if (position > bitmap_table.used){
        position = bitmap_table.used;
    }

    // insert at position
    for (int i = bitmap_table.used; i > position; i--){
        bitmap_table._bitmap_table[i] = bitmap_table._bitmap_table[i-1];
    }

    bitmap_table._bitmap_table[position].valid = True;
    bitmap_table._bitmap_table[position].ppn = vpage; 
    bitmap_table._bitmap_table[position].access_bitmap = _bitmap;
    bitmap_table._bitmap_table[position].acc_cnt_llc_epoch = acc_cnt_llc_epoch;

    bitmap_table.used += 1;
}


void bitmap_table_add_entry_sorted_by_cnt_epoch(Addr ppn){  // Dichotomous search, decreasing

    Addr vpage = ppn; 
    PAGE_ENTRY* entry = hashmap_get(&page_table, &vpage); 
    if (entry == NULL){
        VG_(tool_panic)("page inserted is never accessed, that's strange!"); 
    }
    uint64_t acc_cnt_llc_epoch = entry->pg_info.acc_cnt_llc_epoch;

    if (bitmap_table.used == 0){
        bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, 0);
    }
    else if (bitmap_table.used == 1){
        uint64_t acc_cnt_llc_epoch0 = bitmap_table._bitmap_table[0].acc_cnt_llc_epoch;
        if (acc_cnt_llc_epoch0 >= acc_cnt_llc_epoch){
            bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, 1);
        }
        else{
            bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, 0);
        }
    }
    else{
        int start = 0;
        int end = bitmap_table.used - 1;
        int mid = (start + end) / 2;
        if (bitmap_table._bitmap_table[start].acc_cnt_llc_epoch < acc_cnt_llc_epoch){
            bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, 0);
        }
        else if (bitmap_table._bitmap_table[end].acc_cnt_llc_epoch > acc_cnt_llc_epoch){
            bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, bitmap_table.used);
        }
        else{
            while (start < end - 1){
                if (acc_cnt_llc_epoch > bitmap_table._bitmap_table[mid].acc_cnt_llc_epoch)
                    end = mid;
                else
                    start = mid;
                mid = (start + end) / 2;
            }
            bitmap_table_insert_entry(ppn, acc_cnt_llc_epoch, end);
        }
    }
    
}

#define THRESHOLD 0

typedef struct _hot_page_selector{
    uint64_t threshold;
} HOT_PAGE_SELECTOR;

HOT_PAGE_SELECTOR hot_page_selector;

void hot_page_selector_init(){
    hot_page_selector.threshold = THRESHOLD;
}

bool select_hot_pages_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    if (entry->pg_info.acc_cnt_llc_epoch > THRESHOLD)
        bitmap_table_add_entry_sorted_by_cnt_epoch(entry->virt_page);
    return true;
}

void select_hot_pages(){
    hashmap_scan(&page_table, select_hot_pages_iter, NULL);
}

bool reset_acc_cnt_period_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    entry->pg_info.acc_cnt_llc_period = 0;
    entry->pg_info.acc_cnt_tlb_period = 0;
    return true;
}

// hot table updater
void hot_page_update_bitmap_table(){
    for (int i = 0; i < bitmap_table.used; i++){
        bitmap_table._bitmap_table[i].access_bitmap = (bitmap_table._bitmap_table[i].access_bitmap << 1);

        Addr vpage = bitmap_table._bitmap_table[i].ppn;
        PAGE_ENTRY * entry = hashmap_get(&page_table, &vpage);
        if (entry == NULL){
            VG_(tool_panic)("page in the bitmap is never accessed, that's strange!");
        }
        else{
            if (entry->pg_info.acc_cnt_llc_period > 0)  // we only regard these pages which is missed in the llc as accessed
                bitmap_table._bitmap_table[i].access_bitmap = (bitmap_table._bitmap_table[i].access_bitmap | 1);
        }
    }
    // reset the period counters
    hashmap_scan(&page_table, reset_acc_cnt_period_iter, NULL);
}



// CM-Sketch


typedef uint64_t (*cm_sketch_hash_f[CM_SKETCH_TABLE_NUM])(Addr item);

typedef struct _cm_sketch{
    uint64_t hash_table[CM_SKETCH_TABLE_NUM][CM_SKETCH_TABLE_SIZE];
    cm_sketch_hash_f hash;
} CM_SKETCH;

CM_SKETCH cm_sketch;

void cm_sketch_add(Addr item){
    for (int i = 0; i < CM_SKETCH_TABLE_NUM; i++){
        uint64_t loc = cm_sketch.hash[i](item);
        cm_sketch.hash_table[i][loc] += 1;
    }
}

uint64_t cm_sketch_query(Addr item){
    uint64_t min_ = -1;
    for (int i = 0; i < CM_SKETCH_TABLE_NUM; i++){
        uint64_t loc = cm_sketch.hash[i](item);
        if (min_ == -1 || min_ > cm_sketch.hash_table[i][loc])
            min_ = cm_sketch.hash_table[i][loc];
    }
    return min_;
}

// three hash functions

uint64_t hash1(Addr x) {
    uint64_t a = 0x12345678; // a random number
    return ((x ^ a) >> 1) % CM_SKETCH_TABLE_SIZE;
}

uint64_t hash2(Addr x) {
    uint64_t p = 1000000007; // a large prime number
    return (x * p) % CM_SKETCH_TABLE_SIZE;
}

uint64_t hash3(Addr x) {
    uint64_t b = 0x87654321; // a random number
    uint64_t sum = 0;
    for (int i = 0; i < 8; i++) { // assume x is a 32-bit integer
        sum += ((x & 0xF) ^ (b & 0xF)); // xor the last four bits of x and b
        x >>= 4; // right shift x by four bits
        b >>= 4; // right shift b by four bits
    }
    return sum % CM_SKETCH_TABLE_SIZE;
}

void cm_sketch_init(){
    cm_sketch.hash[0] = hash1;
    cm_sketch.hash[1] = hash2;
    cm_sketch.hash[2] = hash3;
    // maybe there is an instruction like "VG_(memset)", but nerver mind, its cost is minus
    for (int i = 0; i < CM_SKETCH_TABLE_NUM; i++)
        for (int j = 0; j < CM_SKETCH_TABLE_SIZE; j++)
            cm_sketch.hash_table[i][j] = 0;
}

int epoch_state = 0; // 0 -- beigin, 1 -- mid

bool reset_acc_cnt_epoch_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    entry->pg_info.acc_cnt_llc_epoch = 0;
    entry->pg_info.acc_cnt_tlb_epoch = 0;
    return true;
}

int cnt_epoch = 0;

void bitmap_state_update_epoch_by_epoch(){
    if (tik % EPOCH == 0){  // at the beginning of an epoch, we need to clear all the epoch counters
        epoch_state = 0;
        hashmap_scan(&page_table, reset_acc_cnt_epoch_iter, NULL);
    }
    else if (tik % (EPOCH / 2) == 0){ // if in the middle of an epoch, we need to choose hot pages and put them into the bitmap tables
        epoch_state = 1;
        select_hot_pages();
        
        cnt_epoch += 1;
        if (cnt_epoch % 10 == 0){
            print_bitmap_table(10);
        }
    }
    
    if (tik % TIMESLICE == 0 && epoch_state == 1){
        hot_page_update_bitmap_table();
    }
}

void bitmap_state_update_slide_window(){
    if (tik % EPOCH == 0){

    }
    if (tik % TIMESLICE == 0){

    }
}


// we need a struct to store information of which pages are in the local and which are in the local
// the struct should have the features like LRU (maybe useful in ), fast insert and delete (we need to do migrate)
// we only get physical address, theoretically we can't do migrate because we can't affect page table
// but we can add an additional mapping, from 'fake physical address' to 'true physical address', by doing this, we can simulate the change of page table
// so, the 'fake physical address' is just the address we get, and the 'true physical address' is phys_page we record in page_info


// Pase hashtable here



int page_compare(const void *a, const void *b, void *udata)
{
    struct page_entry *pa = (struct page_entry *)a;
    struct page_entry *pb = (struct page_entry *)b;
    if (pa->virt_page < pb->virt_page)
        return -1;
    else if (pa->virt_page > pb->virt_page)
        return 1;
    else
        return 0;
}

ULong page_hash(const void *item, ULong seed0, ULong seed1)
{
   //  const struct page_entry *pe = (struct page_entry *)item;
    return *((ULong *)(item)) * 2654435761ULL; // A simple hash function
}


void* vg_realloc(void *ptr, SizeT size)
{
   return VG_(realloc)("vg_realloc", ptr, size);
}
void* vg_malloc(SizeT size)
{
    void * ptr = VG_(malloc)("vg_malloc", size);
    return ptr;
}

void vg_free(void* ptr)
{
   return VG_(free)(ptr);
}


static void *(*_malloc)(SizeT) = vg_malloc;
static void *(*_realloc)(void *, SizeT) = vg_realloc;
static void (*_free)(void *) = vg_free;

#define vg_assert(expr)                                                 \
  ((void) (LIKELY(expr) ? 0 :                                           \
           (VG_(assert_fail) (/*isCore*/True, #expr,                    \
                              __FILE__, __LINE__, __PRETTY_FUNCTION__,  \
                              ""),                                      \
                              0)))

// hashmap_set_allocator allows for configuring a custom allocator for
// all hashmap library operations. This function, if needed, should be called
// only once at startup and a prior to calling hashmap_new().
void hashmap_set_allocator(void *(*malloc)(SizeT), void (*free)(void*)) 
{
    _malloc = malloc;
    _free = free;
}

#define panic(_msg_) { \
    VG_(fprintf(stderr, "panic: %s (%s:%d)\n", (_msg_), __FILE__, __LINE__)); \
    vg_assert(0); \
}

static struct bucket {
    uint64_t hash:48;
    uint64_t dib:16;
};

// hashmap is an open addressed hash map using robinhood hashing.
static struct hashmap {
    void *(*malloc)(SizeT);
    void *(*realloc)(void *, SizeT);
    void (*free)(void *);
    bool oom;
    SizeT elsize;
    SizeT cap;
    uint64_t seed0;
    uint64_t seed1;
    uint64_t (*hash)(const void *item, uint64_t seed0, uint64_t seed1);
    int (*compare)(const void *a, const void *b, void *udata);
    void (*elfree)(void *item);
    void *udata;
    SizeT bucketsz;
    SizeT nbuckets;
    SizeT count;
    SizeT mask;
    SizeT growat;
    SizeT shrinkat;
    void *buckets;
    void *spare;
    void *edata;
};

static struct bucket *bucket_at(struct hashmap *map, SizeT index) {
    return (struct bucket*)(((char*)map->buckets)+(map->bucketsz*index));
}

static void *bucket_item(struct bucket *entry) {
    return ((char*)entry)+sizeof(struct bucket);
}

static uint64_t get_hash(struct hashmap *map, const void *key) {
    return map->hash(key, map->seed0, map->seed1) << 16 >> 16;
}

// hashmap_new_with_allocator returns a new hash map using a custom allocator.
// See hashmap_new for more information
struct hashmap *hashmap_new_with_allocator(
                            void *(*_malloc)(SizeT), 
                            void *(*_realloc)(void*, SizeT), 
                            void (*_free)(void*),
                            SizeT elsize, SizeT cap, 
                            uint64_t seed0, uint64_t seed1,
                            uint64_t (*hash)(const void *item, 
                                             uint64_t seed0, uint64_t seed1),
                            int (*compare)(const void *a, const void *b, 
                                           void *udata),
                            void (*elfree)(void *item),
                            void *udata)
{
   //  _malloc = _malloc ? _malloc : malloc;
   //  _realloc = _realloc ? _realloc : realloc;
   //  _free = _free ? _free : free;
    int ncap = 16;
    if (cap < ncap) {
        cap = ncap;
    } else {
        while (ncap < cap) {
            ncap *= 2;
        }
        cap = ncap;
    }
    SizeT bucketsz = sizeof(struct bucket) + elsize;
    while (bucketsz & (sizeof(uintptr_t)-1)) {
        bucketsz++;
    }
    // hashmap + spare + edata
    SizeT size = sizeof(struct hashmap)+bucketsz*2;
    struct hashmap *map = _malloc(size);
    if (!map) {
        return NULL;
    }
    VG_(memset)(map, 0, sizeof(struct hashmap));
    map->elsize = elsize;
    map->bucketsz = bucketsz;
    map->seed0 = seed0;
    map->seed1 = seed1;
    map->hash = hash;
    map->compare = compare;
    map->elfree = elfree;
    map->udata = udata;
    map->spare = ((char*)map)+sizeof(struct hashmap);
    map->edata = (char*)map->spare+bucketsz;
    map->cap = cap;
    map->nbuckets = cap;
    map->mask = map->nbuckets-1;
    map->buckets = _malloc(map->bucketsz*map->nbuckets);
    if (!map->buckets) {
        _free(map);
        return NULL;
    }
    VG_(memset)(map->buckets, 0, map->bucketsz*map->nbuckets);
    map->growat = map->nbuckets*0.75;
    map->shrinkat = map->nbuckets*0.10;
    map->malloc = _malloc;
    map->realloc = _realloc;
    map->free = _free;
    return map;  
}


// hashmap_new returns a new hash map. 
// Param `elsize` is the size of each element in the tree. Every element that
// is inserted, deleted, or retrieved will be this size.
// Param `cap` is the default lower capacity of the hashmap. Setting this to
// zero will default to 16.
// Params `seed0` and `seed1` are optional seed values that are passed to the 
// following `hash` function. These can be any value you wish but it's often 
// best to use randomly generated values.
// Param `hash` is a function that generates a hash value for an item. It's
// important that you provide a good hash function, otherwise it will perform
// poorly or be vulnerable to Denial-of-service attacks. This implementation
// comes with two helper functions `hashmap_sip()` and `hashmap_murmur()`.
// Param `compare` is a function that compares items in the tree. See the 
// qsort stdlib function for an example of how this function works.
// The hashmap must be freed with hashmap_free(). 
// Param `elfree` is a function that frees a specific item. This should be NULL
// unless you're storing some kind of reference data in the hash.
static  struct hashmap *hashmap_new(SizeT elsize, SizeT cap, 
                            uint64_t seed0, uint64_t seed1,
                            uint64_t (*hash)(const void *item, 
                                             uint64_t seed0, uint64_t seed1),
                            int (*compare)(const void *a, const void *b, 
                                           void *udata),
                            void (*elfree)(void *item),
                            void *udata)
{
    return hashmap_new_with_allocator(
        (_malloc),
        (_realloc),
        (_free),
        elsize, cap, seed0, seed1, hash, compare, elfree, udata
    );
}

static void free_elements(struct hashmap *map) {
    if (map->elfree) {
        for (SizeT i = 0; i < map->nbuckets; i++) {
            struct bucket *bucket = bucket_at(map, i);
            if (bucket->dib) map->elfree(bucket_item(bucket));
        }
    }
}


// hashmap_clear quickly clears the map. 
// Every item is called with the element-freeing function given in hashmap_new,
// if present, to free any data referenced in the elements of the hashmap.
// When the update_cap is provided, the map's capacity will be updated to match
// the currently number of allocated buckets. This is an optimization to ensure
// that this operation does not perform any allocations.
static  void hashmap_clear(struct hashmap *map, bool update_cap) {
    map->count = 0;
    free_elements(map);
    if (update_cap) {
        map->cap = map->nbuckets;
    } else if (map->nbuckets != map->cap) {
        void *new_buckets = map->malloc(map->bucketsz*map->cap);
        if (new_buckets) {
            map->free(map->buckets);
            map->buckets = new_buckets;
        }
        map->nbuckets = map->cap;
    }
    VG_(memset)(map->buckets, 0, map->bucketsz*map->nbuckets);
    map->mask = map->nbuckets-1;
    map->growat = map->nbuckets*0.75;
    map->shrinkat = map->nbuckets*0.10;
}


static bool resize(struct hashmap *map, SizeT new_cap) {
    struct hashmap *map2 = hashmap_new_with_allocator(map->malloc, map->realloc, map->free,
                                                      map->elsize, new_cap, map->seed0, 
                                                      map->seed1, map->hash, map->compare,
                                                      map->elfree, map->udata);
    if (!map2) {
        return false;
    }
    for (SizeT i = 0; i < map->nbuckets; i++) {
        struct bucket *entry = bucket_at(map, i);
        if (!entry->dib) {
            continue;
        }
        entry->dib = 1;
        SizeT j = entry->hash & map2->mask;
        for (;;) {
            struct bucket *bucket = bucket_at(map2, j);
            if (bucket->dib == 0) {
                VG_(memcpy)(bucket, entry, map->bucketsz);
                break;
            }
            if (bucket->dib < entry->dib) {
                VG_(memcpy)(map2->spare, bucket, map->bucketsz);
                VG_(memcpy)(bucket, entry, map->bucketsz);
                VG_(memcpy)(entry, map2->spare, map->bucketsz);
            }
            j = (j + 1) & map2->mask;
            entry->dib += 1;
        }
	}
    map->free(map->buckets);
    map->buckets = map2->buckets;
    map->nbuckets = map2->nbuckets;
    map->mask = map2->mask;
    map->growat = map2->growat;
    map->shrinkat = map2->shrinkat;
    map->free(map2);
    return true;
}

// hashmap_set inserts or replaces an item in the hash map. If an item is
// replaced then it is returned otherwise NULL is returned. This operation
// may allocate memory. If the system is unable to allocate additional
// memory then NULL is returned and hashmap_oom() returns true.
static  void *hashmap_set(struct hashmap *map, const void *item) {
    if (!item) {
      //   panic("item is null");
      vg_assert(0);
    }
    map->oom = false;
    if (map->count == map->growat) {
        if (!resize(map, map->nbuckets*2)) {
            map->oom = true;
            return NULL;
        }
    }

    
    struct bucket *entry = map->edata;
    entry->hash = get_hash(map, item);
    entry->dib = 1;
    VG_(memcpy)(bucket_item(entry), item, map->elsize);
    
    SizeT i = entry->hash & map->mask;
	for (;;) {
        struct bucket *bucket = bucket_at(map, i);
        if (bucket->dib == 0) {
            VG_(memcpy)(bucket, entry, map->bucketsz);
            map->count++;
			return NULL;
		}
        if (entry->hash == bucket->hash && 
            map->compare(bucket_item(entry), bucket_item(bucket), 
                         map->udata) == 0)
        {
            VG_(memcpy)(map->spare, bucket_item(bucket), map->elsize);
            VG_(memcpy)(bucket_item(bucket), bucket_item(entry), map->elsize);
            return map->spare;
		}
        if (bucket->dib < entry->dib) {
            VG_(memcpy)(map->spare, bucket, map->bucketsz);
            VG_(memcpy)(bucket, entry, map->bucketsz);
            VG_(memcpy)(entry, map->spare, map->bucketsz);
		}
		i = (i + 1) & map->mask;
        entry->dib += 1;
	}
}

// hashmap_get returns the item based on the provided key. If the item is not
// found then NULL is returned.
static  void *hashmap_get(struct hashmap *map, const void *key) {
    if (!key) {
      //   panic("key is null");
      vg_assert(0);

    }
   uint64_t hash = get_hash(map, key);
	SizeT i = hash & map->mask;
	for (;;) {
        struct bucket *bucket = bucket_at(map, i);
		if (!bucket->dib) {
			return NULL;
		}
		if (bucket->hash == hash && 
            map->compare(key, bucket_item(bucket), map->udata) == 0)
        {
            return bucket_item(bucket);
		}
		i = (i + 1) & map->mask;
	}
}

// hashmap_probe returns the item in the bucket at position or NULL if an item
// is not set for that bucket. The position is 'moduloed' by the number of 
// buckets in the hashmap.
static  void *hashmap_probe(struct hashmap *map, uint64_t position) {
    SizeT i = position & map->mask;
    struct bucket *bucket = bucket_at(map, i);
    if (!bucket->dib) {
		return NULL;
	}
    return bucket_item(bucket);
}


// hashmap_delete removes an item from the hash map and returns it. If the
// item is not found then NULL is returned.
static void *hashmap_delete(struct hashmap *map, void *key) {
    if (!key) {
      //   panic("key is null");
      vg_assert(0);

    }
    map->oom = false;
    uint64_t hash = get_hash(map, key);
	SizeT i = hash & map->mask;
	for (;;) {
        struct bucket *bucket = bucket_at(map, i);
		if (!bucket->dib) {
			return NULL;
		}
		if (bucket->hash == hash && 
            map->compare(key, bucket_item(bucket), map->udata) == 0)
        {
            VG_(memcpy)(map->spare, bucket_item(bucket), map->elsize);
            bucket->dib = 0;
            for (;;) {
                struct bucket *prev = bucket;
                i = (i + 1) & map->mask;
                bucket = bucket_at(map, i);
                if (bucket->dib <= 1) {
                    prev->dib = 0;
                    break;
                }
                VG_(memcpy)(prev, bucket, map->bucketsz);
                prev->dib--;
            }
            map->count--;
            if (map->nbuckets > map->cap && map->count <= map->shrinkat) {
                // Ignore the return value. It's ok for the resize operation to
                // fail to allocate enough memory because a shrink operation
                // does not change the integrity of the data.
                resize(map, map->nbuckets/2);
            }
			return map->spare;
		}
		i = (i + 1) & map->mask;
	}
}

// hashmap_count returns the number of items in the hash map.
SizeT hashmap_count(struct hashmap *map) {
    return map->count;
}

// hashmap_free frees the hash map
// Every item is called with the element-freeing function given in hashmap_new,
// if present, to free any data referenced in the elements of the hashmap.
static void hashmap_free(struct hashmap *map) {
    if (!map) return;
    free_elements(map);
    map->free(map->buckets);
    map->free(map);
}

// hashmap_oom returns true if the last hashmap_set() call failed due to the 
// system being out of memory.
static bool hashmap_oom(struct hashmap *map) {
    return map->oom;
}

// hashmap_scan iterates over all items in the hash map
// Param `iter` can return false to stop iteration early.
// Returns false if the iteration has been stopped early.
static bool hashmap_scan(struct hashmap *map, 
                  bool (*iter)(const void *item, void *udata), void *udata)
{
    for (SizeT i = 0; i < map->nbuckets; i++) {
        struct bucket *bucket = bucket_at(map, i);
        if (bucket->dib) {
            if (!iter(bucket_item(bucket), udata)) {
                return false;
            }
        }
    }
    return true;
}


// hashmap_iter iterates one key at a time yielding a reference to an
// entry at each iteration. Useful to write simple loops and avoid writing
// dedicated callbacks and udata structures, as in hashmap_scan.
//
// map is a hash map handle. i is a pointer to a SizeT cursor that
// should be initialized to 0 at the beginning of the loop. item is a void
// pointer pointer that is populated with the retrieved item. Note that this
// is NOT a copy of the item stored in the hash map and can be directly
// modified.
//
// Note that if hashmap_delete() is called on the hashmap being iterated,
// the buckets are rearranged and the iterator must be reset to 0, otherwise
// unexpected results may be returned after deletion.
//
// This function has not been tested for thread safety.
//
// The function returns true if an item was retrieved; false if the end of the
// iteration has been reached.
static bool hashmap_iter(struct hashmap *map, SizeT *i, void **item)
{
    struct bucket *bucket;

    do {
        if (*i >= map->nbuckets) return false;

        bucket = bucket_at(map, *i);
        (*i)++;
    } while (!bucket->dib);

    *item = bucket_item(bucket);

    return true;
}

static void init_page_table()
{
   page_table = *hashmap_new(sizeof(struct page_entry), 0, 0, 0,  page_hash, page_compare, NULL, NULL);
}

#endif


typedef struct {
   Long         size;                   /* bytes */
   Int          assoc;
   Int          line_size;              /* bytes */
   Int          sets;
   Int          sets_min_1;
   Int          line_size_bits;
   Int          tag_shift;
   HChar        desc_line[128];         /* large enough */
   UWord*       tags;
} cache_t2;


typedef struct {
   Int          page_size;              /* bytes */
   ULong        size;                   /* bytes */
   ULong        local_size;
   ULong        remote_size;
   ULong        local_page_num;
   void*        local_lru; 
   ULong        used;
} dram_t2;

static cache_t2 LL;
static cache_t2 I1;
static cache_t2 D1;
static dram_t2  DRAM;

/* By this point, the size/assoc/line_size has been checked. */
static void cachesim_initcache(cache_t config, cache_t2* c)
{
   Int i;

   c->size      = config.size;
   c->assoc     = config.assoc;
   c->line_size = config.line_size;

   c->sets           = (c->size / c->line_size) / c->assoc;
   c->sets_min_1     = c->sets - 1;
   c->line_size_bits = VG_(log2)(c->line_size);
   c->tag_shift      = c->line_size_bits + VG_(log2)(c->sets);

   if (c->assoc == 1) {
      VG_(sprintf)(c->desc_line, "%d B, %d B, direct-mapped", 
                                 c->size, c->line_size);
   } else {
      VG_(sprintf)(c->desc_line, "%d B, %d B, %d-way associative",
                                 c->size, c->line_size, c->assoc);
   }

   c->tags = VG_(malloc)("cg.sim.ci.1",
                         sizeof(UWord) * c->sets * c->assoc);

   for (i = 0; i < c->sets * c->assoc; i++)
      c->tags[i] = 0;
}


/* This attribute forces GCC to inline the function, getting rid of a
 * lot of indirection around the cache_t2 pointer, if it is known to be
 * constant in the caller (the caller is inlined itself).
 * Without inlining of simulator functions, cachegrind can get 40% slower.
 */
__attribute__((always_inline))
static __inline__
Bool cachesim_setref_is_miss(cache_t2* c, UInt set_no, UWord tag)
{
   int i, j;
   UWord *set;

   set = &(c->tags[set_no * c->assoc]);

   /* This loop is unrolled for just the first case, which is the most */
   /* common.  We can't unroll any further because it would screw up   */
   /* if we have a direct-mapped (1-way) cache.                        */
   if (tag == set[0])
      return False;

   /* If the tag is one other than the MRU, move it into the MRU spot  */
   /* and shuffle the rest down.                                       */
   for (i = 1; i < c->assoc; i++) {
      if (tag == set[i]) {
         for (j = i; j > 0; j--) {
            set[j] = set[j - 1];
         }
         set[0] = tag;

         return False;
      }
   }

   /* A miss;  install this tag as MRU, shuffle rest down. */
   for (j = c->assoc - 1; j > 0; j--) {
      set[j] = set[j - 1];
   }
   set[0] = tag;

   return True;
}

__attribute__((always_inline))
static __inline__
Bool cachesim_ref_is_miss(cache_t2* c, Addr a, UChar size)
{
   /* A memory block has the size of a cache line */
   UWord block1 =  a         >> c->line_size_bits;
   UWord block2 = (a+size-1) >> c->line_size_bits;
   UInt  set1   = block1 & c->sets_min_1;

   /* Tags used in real caches are minimal to save space.
    * As the last bits of the block number of addresses mapping
    * into one cache set are the same, real caches use as tag
    *   tag = block >> log2(#sets)
    * But using the memory block as more specific tag is fine,
    * and saves instructions.
    */
   UWord tag1   = block1;

   /* Access entirely within line. */
   if (block1 == block2)
      return cachesim_setref_is_miss(c, set1, tag1);

   /* Access straddles two lines. */
   else if (block1 + 1 == block2) {
      UInt  set2 = block2 & c->sets_min_1;
      UWord tag2 = block2;

      /* always do both, as state is updated as side effect */
      if (cachesim_setref_is_miss(c, set1, tag1)) {
         cachesim_setref_is_miss(c, set2, tag2);
         return True;
      }
      return cachesim_setref_is_miss(c, set2, tag2);
   }
   VG_(printf)("addr: %lx  size: %u  blocks: %lu %lu",
               a, size, block1, block2);
   VG_(tool_panic)("item straddles more than two cache sets");
   /* not reached */
   return True;
}


/**********************Hotness Tracking Strategy***********************/

#ifdef PAGE_PROF

// Page migration configs
enum migration_policy {
	MIG_POLICY_NOP = 0,
	MIG_POLICY_PURE_RANDOM,
	NUM_MIG_POLICIES
};


static Int interval = 10000000;
// static Int interval = 10000;
static Int n_dump_page = 500;
static float local_watermark_ratio = 0.75;
static hotness_thresh = 5;

static ULong useless_hot = 0;
static ULong tlb_hot = 0;
static ULong llc_hot = 0;
static ULong profiled_epochs = 0;
static Bool profiling_start = 0;
static Bool profiling_end = 0;



bool llc_miss_tracker_page_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    if(entry->pg_info.acc_cnt_llc > 0){
        llc_hot++;
    }
    entry->pg_info.acc_cnt_llc = 0;
    return true;
}

void llc_miss_tracker_scan(){
    // scan the page table and get modified pages
    hashmap_scan(&page_table, llc_miss_tracker_page_iter, NULL);
    // reset the hotness
    useless_hot = 0;
    tlb_hot = 0;
}

bool scan_and_reset_a_bit_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    if(entry->pg_info.a_bit)
      entry->pg_info.acc_cnt_a_bit ++;  

    entry->pg_info.a_bit = 0;
    return true;
}

void a_bit_based_hotness_profiling(){
  // scan the page table and get modified pages
  hashmap_scan(&page_table, scan_and_reset_a_bit_iter, NULL);
}

bool reset_acc_cnt_iter(const void *item, void * udata){
    struct page_entry * entry = item;
    entry->pg_info.acc_cnt_a_bit = 0;
    entry->pg_info.acc_cnt_llc = 0;
    entry->pg_info.acc_cnt_tlb = 0;
    return true;
}

void reset_acc_cnt_scan(){
    // scan the page table and get modified pages
    hashmap_scan(&page_table, reset_acc_cnt_iter, NULL);
}

void dump_hotness_info(int n_pages){
  int remaining_pages = n_pages;
  for (SizeT i = 0; i < page_table.nbuckets; i++) {
    struct bucket *bucket = bucket_at(&page_table, i);
    if (bucket->dib) {
      struct page_entry * entry = bucket_item(bucket); 
      if(entry->pg_info.acc_cnt_a_bit > hotness_thresh)
      {
        VG_(printf)("page: %lx  acc_cnt_a_bit: %lu  acc_cnt_llc: %lu  acc_cnt_tlb: %lu\n", entry->virt_page, entry->pg_info.acc_cnt_a_bit, entry->pg_info.acc_cnt_llc, entry->pg_info.acc_cnt_tlb);
        remaining_pages --;
      }      
    }
    if(remaining_pages == 0)
      return;
  }
}

#endif 



inline void DRAM_lru_update(Addr vpage){

    LRU_ENTRY* lru = (LRU_ENTRY*) (DRAM.local_lru);

    for (int i = 0; i < DRAM.used; i++){
        if (lru[i].vpage == vpage){  // this means the address is already in the DRAM
            for (int j = i; j > 0; j--)
                lru[j] = lru[j-1];
            lru[0].vpage = vpage;
            lru[0].cnt = 0;
            return;
        }
    }

    if (DRAM.used >= DRAM.local_page_num)
        DRAM.used = DRAM.local_page_num - 1;

    for (int i = DRAM.used; i > 0; i--){
        lru[i] = lru[i-1];
    }

    DRAM.used += 1;
    lru[0].vpage = vpage;
    lru[0].cnt = 0;
    return;
}

#ifdef PAGE_PROF
__attribute__((always_inline))
static __inline__
Bool cachesim_ref_page(dram_t2* dram, Addr a, Bool is_read, Bool llc_miss)
{

    UWord vpage = a >> page_offset;                        // get virtual page number
    PAGE_ENTRY * entry = hashmap_get(&page_table, &vpage); // look up in page table
    LRU_ENTRY* lru = (LRU_ENTRY*) (DRAM.local_lru);

    VG_(printf)("strategy info: %d\n", strategy);

    if (llc_miss){
        // before a llc_miss, there must be a tlb access
        if (entry == NULL) { 
            VG_(tool_panic)("page first accessed in a llc miss!");
        }
        else if (is_read){
            entry->pg_info.acc_cnt_llc++;
            entry->pg_info.acc_cnt_llc_period++;
            entry->pg_info.acc_cnt_llc_epoch++;
            
            if (entry->pg_info.is_local)
                n_local_page_acc_cnt++;
            else{
                n_remote_page_acc_cnt++;

                // here we decide how to migrate
                if (strategy == 1){
                    // once touch remote memory, migrate them to local memory
                    migrate_cnt++;
                    PAGE_ENTRY * least_entry = hashmap_get(&page_table, &(lru[DRAM.used-1].vpage));
                    least_entry->pg_info.is_local = False;
                    entry->pg_info.is_local = True;
                }
            }
            DRAM_lru_update(vpage);
        }
    }
    else{
        // the page is not in the hashmap, which means its the first time that we try to access this page
        // so we create a new page, set its attribute and add it to the hashmap
        // when setting its attribute, we are actually doing the process of allocation (decide allocate at which place, local or remote)
        // however, this assumps that all the pages are anon pages, which is created when it is firstly accessed (is this right?)
        if (entry == NULL) {
            if(n_global_page % 10000 == 0){
                VG_(printf)("n_global_page: %lu  n_local_page: %lu  n_remote_page: %lu\n", n_global_page, n_local_page, n_remote_page);
                VG_(printf)("n_local_page_allocate_cnt: %lu  n_remote_page_allocate_cnt: %lu\n", n_local_page_allocate_cnt, n_remote_page_allocate_cnt);
                VG_(printf)("n_local_page_acc_cnt: %lu  n_remote_page_acc_cnt: %lu  migrate_cnt: %lu\n\n", n_local_page_acc_cnt, n_remote_page_acc_cnt, migrate_cnt);
            }
            PAGE_INFO page_info = {.acc_cnt_llc = 0, .acc_cnt_tlb = 1, .acc_cnt_llc_period = 0, .acc_cnt_tlb_period = 1, .acc_cnt_llc_epoch = 0, .acc_cnt_tlb_epoch = 1}; // create a new page info
            page_info.phys_page = n_global_page ++; // assign a physical page number using the global counter
            if (page_info.phys_page >= (dram->local_size >> page_offset)) {
                page_info.is_local = 0; // if the physical page number is larger than the local size, it is remote
                n_remote_page++;
                n_remote_page_allocate_cnt++;
            }
            else{
                page_info.is_local = 1; // otherwise, it is local
                n_local_page++;
                n_local_page_allocate_cnt++; 
            }
            
            // add to page table
            hashmap_set(&page_table, &(PAGE_ENTRY){.virt_page = vpage, .pg_info = page_info});
        }
        else{
            // tlb access time added
            entry->pg_info.acc_cnt_tlb++;
            entry->pg_info.acc_cnt_tlb_period++;
            entry->pg_info.acc_cnt_tlb_epoch++;
            // set a bit 
            entry->pg_info.a_bit = 1;
        }

        ///////////////////////////////////////////////////
        // below, we can do some state updating to simulate the behaviour of sketch and bitmap
        ///////////////////////////////////////////////////

        // bitmap_state_update_epoch_by_epoch();

        // Trigger page hotness profiling
        // For one instruction, we just want to profile once, so we put the state updating process below
        // It means that, each time we try to access an address in memory, we will update the statement (e.g., do something, such as do profiling)
        if(n_global_page > (dram->local_size >> page_offset) && (profiling_start == 0)){
            profiling_start = 1;
            VG_(printf)("Profiling start\n");
        }

        // Trigger page hotness profiling
        if(n_global_page > (dram->local_size >> page_offset) && (profiling_start == 0)){
            profiling_start = 1;
            VG_(printf)("Profiling start\n");
        }

        if(profiling_start && !profiling_end){
            // profiling page hotness periodically
            if(tik % interval == 0){
                a_bit_based_hotness_profiling();
                profiled_epochs ++;
            }
            if(profiled_epochs == 10){
                dump_hotness_info(n_dump_page);
                reset_acc_cnt_scan();
                profiled_epochs = 0;
                profiling_end = 1;
            }
        }
    }
    return True;
}
#endif



static void cachesim_initcaches(cache_t I1c, cache_t D1c, cache_t LLc)
{
   cachesim_initcache(I1c, &I1);
   cachesim_initcache(D1c, &D1);
   cachesim_initcache(LLc, &LL);
}

static void cachesim_initdrams(dram_t Dram)
{
   // cachesim_initdram(Dram, &DRAM);
   DRAM.local_size = Dram.local_size;
   DRAM.page_size = Dram.page_size;
   DRAM.remote_size = Dram.remote_size;
   DRAM.size = Dram.size;
   VG_(printf)("%lu, %lu, %lu, %lu \n", DRAM.page_size, DRAM.size, DRAM.local_size, DRAM.remote_size);

   ULong local_page_num = (DRAM.local_size >> page_offset);

   DRAM.local_page_num = local_page_num;
   DRAM.local_lru = vg_malloc(local_page_num * sizeof(LRU_ENTRY));
   DRAM.used = 0;

#ifdef PAGE_PROF
   init_page_table();
#endif 
}


__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_Gen(Addr a, UChar size, ULong* m1, ULong *mL)
{

#ifdef PAGE_PROF   
   cachesim_ref_page(&DRAM, a, True, False);
#endif

   if (cachesim_ref_is_miss(&I1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size)){
         (*mL)++;

#ifdef PAGE_PROF
         cachesim_ref_page(&DRAM, a, True, True);
#endif
      }
   }
}

// common special case IrNoX
__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_NoX(Addr a, UChar size, ULong* m1, ULong *mL)
{
   UWord block  = a >> I1.line_size_bits;
   UInt  I1_set = block & I1.sets_min_1;

#ifdef PAGE_PROF
   cachesim_ref_page(&DRAM, a, True, False);
#endif
   // use block as tag
   if (cachesim_setref_is_miss(&I1, I1_set, block)) {
      UInt  LL_set = block & LL.sets_min_1;
      (*m1)++;
      // can use block as tag as L1I and LL cache line sizes are equal
      if (cachesim_setref_is_miss(&LL, LL_set, block))
      {
         (*mL)++;
#ifdef PAGE_PROF
         cachesim_ref_page(&DRAM, a, True, True);
#endif
      }
   }
}

__attribute__((always_inline))
static __inline__
void cachesim_D1_doref(Addr a, UChar size, ULong* m1, ULong *mL, Bool is_read)
{
#ifdef PAGE_PROF
   cachesim_ref_page(&DRAM, a, is_read, False);
#endif

   if (cachesim_ref_is_miss(&D1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size))
      {
         (*mL)++;
#ifdef PAGE_PROF
         cachesim_ref_page(&DRAM, a, is_read, True);
#endif
      }
   }
}

/* Check for special case IrNoX. Called at instrumentation time.
 *
 * Does this Ir only touch one cache line, and are L1I/LL cache
 * line sizes the same? This allows to get rid of a runtime check.
 *
 * Returning false is always fine, as this calls the generic case
 */
static Bool cachesim_is_IrNoX(Addr a, UChar size)
{
   UWord block1, block2;

   if (I1.line_size_bits != LL.line_size_bits) return False;
   block1 =  a         >> I1.line_size_bits;
   block2 = (a+size-1) >> I1.line_size_bits;
   if (block1 != block2) return False;

   return True;
}

/*--------------------------------------------------------------------*/
/*--- end                                                 cg_sim.c ---*/
/*--------------------------------------------------------------------*/

