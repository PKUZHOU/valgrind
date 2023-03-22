
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

#include "cg_page.h"
#include "hashmap.h"

#define PAGE_PROF

typedef struct {
   Long          size;                   /* bytes */
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
   Long         size;                   /* bytes */
   Int          page_size;              /* bytes */
   Long         local_size;
   Long         remote_size;
} dram_t2;

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

static void cachesim_initdram(dram_t config, dram_t2 * d)
{
   d->size        = config.size;
   d->page_size   = config.page_size;
   // currently, the memory space is partitioned to 0->local-1, local->remote
   d->local_size  = config.local_size;
   // assert(d->size >= d->local_size);
   d->remote_size = config.size - config.local_size; 
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

__attribute__((always_inline))
static __inline__
Bool cachesim_ref_page(dram_t* dram, Addr a, Bool llc_miss)
{
   if(n_global_page % 1000 == 0){
      VG_(printf)("n_global_page: %lu  n_local_page: %lu  n_remote_page: %lu", n_global_page, n_local_page, n_remote_page);
   }
   UWord vpage = a >> page_offset; // get virtual page number
   PAGE_ENTRY * entry = hashmap_get(&page_table, &vpage); // look up in page table
   if (!entry) { // if not found, add to page table
      PAGE_INFO page_info = {.acc_cnt_llc = 0, .acc_cnt_tlb = 0}; // create a new page info
      page_info.is_local = 1; // default to local
      page_info.phys_page = n_global_page ++; // assign a physical page number using the global counter
      if (page_info.phys_page >= dram->local_size) {
         page_info.is_local = 0; // if the physical page number is larger than the local size, it is remote
         n_remote_page ++;
      }
      else{
         page_info.is_local = 1; // otherwise, it is local
         n_local_page ++; 
      }
      if (llc_miss){
         page_info.acc_cnt_llc = 1; // if it is a llc miss, update the llc miss counter
      }
      else{
         page_info.acc_cnt_tlb = 1; // if it is a tlb miss, update the tlb miss counter
      }
      hashmap_set(&page_table, &(PAGE_ENTRY){ // add to page table
         .virt_page = vpage,
         .pg_info = page_info});
      return False;
   }
   // update info 
   else{
      if (llc_miss){
         entry->pg_info.acc_cnt_llc ++;
      }
      else{
         entry->pg_info.acc_cnt_tlb ++;
      }
      return True;
   }

}

static cache_t2 LL;
static cache_t2 I1;
static cache_t2 D1;
static dram_t2  DRAM;

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
}


__attribute__((always_inline))
static __inline__
void cachesim_I1_doref_Gen(Addr a, UChar size, ULong* m1, ULong *mL)
{

#ifdef PAGE_PROF   
   cachesim_ref_page(&DRAM, a, false);
#endif
   if (cachesim_ref_is_miss(&I1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size)){
         (*mL)++;
#ifdef PAGE_PROF
         cachesim_ref_page(&DRAM, a, true);
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
   cachesim_ref_page(&DRAM, a, false);
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
         cachesim_ref_page(&DRAM, a, false);
#endif
      }
   }
}

__attribute__((always_inline))
static __inline__
void cachesim_D1_doref(Addr a, UChar size, ULong* m1, ULong *mL)
{
#ifdef PAGE_PROF
   cachesim_ref_page(&DRAM, a, false);
#endif
   if (cachesim_ref_is_miss(&D1, a, size)) {
      (*m1)++;
      if (cachesim_ref_is_miss(&LL, a, size))
      {
         (*mL)++;
#ifdef PAGE_PROF
         cachesim_ref_page(&DRAM, a, false);
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

