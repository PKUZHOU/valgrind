#ifndef CG_PAGE_H
#define CG_PAGE_H

#include "libvex_basictypes.h"
#include "hashmap.h"
#include <stdlib.h>


static uint64_t n_local_page = 0;
static uint64_t n_remote_page = 0;
static uint64_t n_global_page = 0;

static const uint32_t page_offset = 12;

struct hashmap * page_table;

typedef struct page_info{
    uint64_t phys_page; // physical page id
    uint64_t acc_cnt_tlb;  // how many times this page has been accessed at pte
    uint64_t acc_cnt_llc;  // how many times this page has been accessed after last miss
    bool is_local;      // is this page local or remote
} PAGE_INFO;

typedef struct page_entry {
    uint64_t virt_page; // virtual page id
    PAGE_INFO pg_info;  // page info
}PAGE_ENTRY;

void init_page_table(); // create page table

// page table implemented using hashmap
uint64_t virtToPhys(uint64_t vaddr);


#endif