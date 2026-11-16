/*
Allocation.

One region from the platform, handed out from the front and never returned. A freed block goes on a list for
its size and is reused for the next request of that size:

  - up to 4096 bytes, sizes are multiples of 16, one list each;
  - above that, sizes are powers of two, one list each.

Every block is zeroed when it is freed, so nothing a Lean value held (a key, a nonce) outlives the value on
the heap. Sixteen bytes in front of each block record its size class and whether it is in use; freeing a
block that is not in use stops the machine instead of corrupting the lists.

Which block a request gets depends only on the sizes asked for and freed so far, never on what the blocks
contain.
*/
#include "rt.h"

#define SMALL_LIMIT   4096
#define SMALL_CLASSES (SMALL_LIMIT / 16 + 1)   /* class c holds blocks of c * 16 bytes */
#define LARGE_FIRST   13                       /* 2^13 = 8192, the first power of two above SMALL_LIMIT */
#define LARGE_LAST    47
#define IN_USE        0xA110CA7EDB10C000ull
#define FREED         0xF4EEDB10C0000000ull

typedef struct {
    uint64_t size_class;   /* below SMALL_CLASSES: c * 16 bytes; otherwise SMALL_CLASSES + (log2 - LARGE_FIRST) */
    uint64_t state;
} block_header;

static uint8_t * heap_at;
static uint8_t * heap_end;
static bool heap_asked;
static void * free_small[SMALL_CLASSES];
static void * free_large[LARGE_LAST - LARGE_FIRST + 1];

static size_t class_bytes(uint64_t size_class) {
    if (size_class < SMALL_CLASSES) return (size_t)size_class * 16;
    return (size_t)1 << (LARGE_FIRST + (size_class - SMALL_CLASSES));
}

static void ** class_list(uint64_t size_class) {
    if (size_class < SMALL_CLASSES) return &free_small[size_class];
    return &free_large[size_class - SMALL_CLASSES];
}

void * rt_malloc(size_t size) {
    uint64_t size_class;
    if (size == 0) size = 1;
    if (size <= SMALL_LIMIT) {
        size_class = (size + 15) / 16;
    } else {
        unsigned log2 = LARGE_FIRST;
        while (((size_t)1 << log2) < size) {
            log2++;
            if (log2 > LARGE_LAST) lean_internal_panic_out_of_memory();
        }
        size_class = SMALL_CLASSES + (log2 - LARGE_FIRST);
    }
    void ** list = class_list(size_class);
    block_header * header;
    if (*list != NULL) {
        void * block = *list;
        *list = *(void **)block;
        *(void **)block = NULL;
        header = (block_header *)block - 1;
        if (header->state != FREED) rt_stop("the allocator's free list holds a block that is not free");
    } else {
        if (!heap_asked) {
            size_t heap_size = 0;
            heap_at = silo_plat_heap(&heap_size);
            heap_end = heap_at == NULL ? NULL : heap_at + heap_size;
            heap_asked = true;
            /* Objects waiting to be freed are linked through 48 bits of their headers (object.c). */
            if (((uintptr_t)heap_end >> 48) != 0) rt_stop("the heap lies above what 48-bit object links can reach");
        }
        size_t needed = sizeof(block_header) + class_bytes(size_class);
        if (heap_at == NULL || (size_t)(heap_end - heap_at) < needed) lean_internal_panic_out_of_memory();
        header = (block_header *)heap_at;
        heap_at += needed;
        header->size_class = size_class;
    }
    header->state = IN_USE;
    return header + 1;
}

void rt_free(void * block) {
    block_header * header = (block_header *)block - 1;
    if (header->state != IN_USE) rt_stop("a block was freed that is not in use");
    header->state = FREED;
    memset(block, 0, class_bytes(header->size_class));
    void ** list = class_list(header->size_class);
    *(void **)block = *list;
    *list = block;
}

/* An object of a small fixed size. The header's size field is set, as <lean/lean.h> says it must be. */
lean_object * lean_alloc_small_object_core(unsigned sz) {
    lean_object * o = rt_malloc(sz);
    o->m_cs_sz = sz;
    return o;
}

/* An object of any size: arrays, strings, closures. */
lean_object * lean_alloc_object(size_t sz) {
    lean_object * o = rt_malloc(sz);
    o->m_cs_sz = 0;
    return o;
}

void lean_free_object(lean_object * o) {
    rt_free(o);
}
