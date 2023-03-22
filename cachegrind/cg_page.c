#include "cg_page.h"
#include <malloc.h>
#include "pub_tool_basics.h"
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

uint64_t page_hash(const void *item, uint64_t seed0, uint64_t seed1)
{
    const struct page_entry *pe = (struct page_entry *)item;
    return pe->virt_page * 2654435761ULL; // A simple hash function
}


void init_page_table()
{
    page_table = hashmap_new(sizeof(struct page_entry), 0, 0, 0,  page_hash, page_compare, NULL, NULL);
}



// Long virtToPhys(Long vaddr);
// {
//    Long pageMask = (1 << pageShift) - 1; 
//    Long phys_addr = vaddr & (~pageMask);
//    Long virt_page = vaddr >> pageShift;

//    auto it = virtToPhysMap.find(virt_page);

//    if(it != virtToPhysMap.end()) {
//       Long phys_page = it->second;
//       phys_addr |= phys_page;
//    }
//    else {
//       Long phys_page = nextPage << pageShift;
//       phys_addr |= phys_page;
//       virtToPhysMap.insert(std::make_pair(virt_page, phys_page));
//       ++nextPage;
//    }

//    return phys_addr;
// }
