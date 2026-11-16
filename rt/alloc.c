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

This file is printed from Mini/Alloc.lean by `lake exe mini-print`. Change that, not this: CI checks that
the two agree.
*/
#include "rt.h"

static inline uint64_t mini_load(uint64_t address) {
    uint64_t word;
    __builtin_memcpy(&word, (void const *)address, sizeof word);
    return word;
}

static inline void mini_store(uint64_t address, uint64_t word) {
    __builtin_memcpy((void *)address, &word, sizeof word);
}

static uint64_t heap_at;
static uint64_t heap_end;
static uint64_t heap_asked;
static uint64_t heap_size;
static uint64_t free_small[257];
static uint64_t free_large[35];

static uint64_t mini_class_bytes(uint64_t size_class);
static uint64_t mini_list_get(uint64_t size_class);
static uint64_t mini_list_set(uint64_t size_class, uint64_t block);
static uint64_t mini_rt_malloc(uint64_t size);
static uint64_t mini_rt_free(uint64_t block);

/* How many bytes a block of this class holds. */
static uint64_t mini_class_bytes(uint64_t size_class) {
    if ((uint64_t)(size_class < 257ull)) {
        return (size_class * 16ull);
    }
    return (1ull << (13ull + (size_class - 257ull)));
}

/* The first free block of this class, or zero. */
static uint64_t mini_list_get(uint64_t size_class) {
    if ((uint64_t)(size_class < 257ull)) {
        return free_small[size_class];
    }
    return free_large[(size_class - 257ull)];
}

static uint64_t mini_list_set(uint64_t size_class, uint64_t block) {
    if ((uint64_t)(size_class < 257ull)) {
        free_small[size_class] = block;
    } else {
        free_large[(size_class - 257ull)] = block;
    }
    return 0;
}

/* A block of at least `size` bytes. Sixteen bytes in front of it record its class and its state. */
static uint64_t mini_rt_malloc(uint64_t size) {
    uint64_t size_class = 0;
    uint64_t log2 = 0;
    uint64_t block = 0;
    uint64_t header = 0;
    uint64_t start = 0;
    uint64_t bytes = 0;
    uint64_t needed = 0;
    if ((uint64_t)(size == 0ull)) {
        size = 1ull;
    }
    if ((uint64_t)(size <= 4096ull)) {
        size_class = ((size + 15ull) / 16ull);
    } else {
        log2 = 13ull;
        while ((uint64_t)((1ull << log2) < size)) {
            log2 = (log2 + 1ull);
            if ((uint64_t)(47ull < log2)) {
                lean_internal_panic_out_of_memory();
            }
        }
        size_class = (257ull + (log2 - 13ull));
    }
    block = mini_list_get(size_class);
    if ((uint64_t)(block != 0ull)) {
        mini_list_set(size_class, mini_load(block));
        mini_store(block, 0ull);
        header = (block - 16ull);
        if ((uint64_t)(mini_load((header + 8ull)) != 17649284854698737664ull)) {
            rt_stop("the allocator's free list holds a block that is not free");
        }
    } else {
        if ((uint64_t)(heap_asked == 0ull)) {
            start = (uint64_t)(silo_plat_heap((size_t *)&heap_size));
            heap_at = start;
            if ((uint64_t)(start == 0ull)) {
                heap_end = 0ull;
            } else {
                heap_end = (start + heap_size);
            }
            heap_asked = 1ull;
            if ((uint64_t)((heap_end >> 48ull) != 0ull)) {
                rt_stop("the heap lies above what 48-bit object links can reach");
            }
        }
        bytes = mini_class_bytes(size_class);
        needed = (16ull + bytes);
        if (((uint64_t)(heap_at == 0ull) | (uint64_t)((heap_end - heap_at) < needed))) {
            lean_internal_panic_out_of_memory();
        }
        header = heap_at;
        heap_at = (heap_at + needed);
        mini_store(header, size_class);
    }
    mini_store((header + 8ull), 11605998885923766272ull);
    return (header + 16ull);
}

void * rt_malloc(size_t size) {
    return (void *)mini_rt_malloc((uint64_t)size);
}

/* Takes a block back. It is zeroed, so nothing a Lean value held outlives the value on the heap. */
static uint64_t mini_rt_free(uint64_t block) {
    uint64_t header = 0;
    uint64_t size_class = 0;
    uint64_t bytes = 0;
    uint64_t at = 0;
    uint64_t next = 0;
    header = (block - 16ull);
    if ((uint64_t)(mini_load((header + 8ull)) != 11605998885923766272ull)) {
        rt_stop("a block was freed that is not in use");
    }
    mini_store((header + 8ull), 17649284854698737664ull);
    size_class = mini_load(header);
    bytes = mini_class_bytes(size_class);
    at = 0ull;
    while ((uint64_t)(at < bytes)) {
        mini_store((block + at), 0ull);
        at = (at + 8ull);
    }
    next = mini_list_get(size_class);
    mini_store(block, next);
    mini_list_set(size_class, block);
    return 0;
}

void rt_free(void * block) {
    mini_rt_free((uint64_t)block);
}
