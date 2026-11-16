/*
Giving up references, and freeing what the last one was keeping alive.

This file is printed from Mini/Free.lean by `lake exe mini-print`. Change that, not this: CI checks that
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


static uint64_t mini_release(uint64_t o, uint64_t waiting);
static uint64_t mini_release_all(uint64_t at, uint64_t count, uint64_t waiting);
static uint64_t mini_free_one(uint64_t o, uint64_t waiting);
static uint64_t mini_lean_dec_ref_cold(uint64_t o);

/* Gives up one reference to `o`. If it was the last, `o` joins the objects waiting to be freed: they
are linked through their own headers, in the 48 bits that held the count and the size field, which leaves
the kind and the field count in place to say how to walk the object when its turn comes. A count of 0 is
a permanent object, and one with its top bit set has overflowed and frozen: neither is ever freed. */
static uint64_t mini_release(uint64_t o, uint64_t waiting) {
    uint64_t header = 0;
    uint64_t count = 0;
    if ((uint64_t)((o & 1ull) != 0ull)) {
        return waiting;
    }
    header = mini_load(o);
    count = (header & 4294967295ull);
    if (((uint64_t)(1ull < count) & (uint64_t)(count < 2147483648ull))) {
        mini_store(o, (header - 1ull));
        return waiting;
    }
    if ((uint64_t)(count == 1ull)) {
        mini_store(o, ((header & 18446462598732840960ull) | waiting));
        return o;
    }
    return waiting;
}

/* Gives up one reference to each of the `count` objects whose addresses start at `at`. */
static uint64_t mini_release_all(uint64_t at, uint64_t count, uint64_t waiting) {
    uint64_t i = 0;
    i = 0ull;
    while ((uint64_t)(i < count)) {
        waiting = mini_release(mini_load((at + (i * 8ull))), waiting);
        i = (i + 1ull);
    }
    return waiting;
}

/* Frees `o`, whose last reference is gone, and returns the waiting list with whatever that released. */
static uint64_t mini_free_one(uint64_t o, uint64_t waiting) {
    uint64_t header = 0;
    uint64_t kind = 0;
    uint64_t value = 0;
    uint64_t computes = 0;
    header = mini_load(o);
    kind = (header >> 56ull);
    if ((uint64_t)(kind <= 243ull)) {
        waiting = mini_release_all((o + 8ull), ((header >> 48ull) & 255ull), waiting);
        rt_free((void *)o);
        return waiting;
    }
    if ((uint64_t)(kind == 245ull)) {
        waiting = mini_release_all((o + 24ull), ((mini_load((o + 16ull)) >> 16ull) & 65535ull), waiting);
    } else {
        if ((uint64_t)(kind == 246ull)) {
            waiting = mini_release_all((o + 24ull), mini_load((o + 8ull)), waiting);
        } else {
            if ((((uint64_t)(kind == 248ull) | (uint64_t)(kind == 249ull)) | (uint64_t)(kind == 250ull))) {
            } else {
                if ((uint64_t)(kind == 251ull)) {
                    value = mini_load((o + 8ull));
                    computes = mini_load((o + 16ull));
                    if ((uint64_t)(computes != 0ull)) {
                        waiting = mini_release(computes, waiting);
                    }
                    if ((uint64_t)(value != 0ull)) {
                        waiting = mini_release(value, waiting);
                    }
                } else {
                    if ((uint64_t)(kind == 253ull)) {
                        value = mini_load((o + 8ull));
                        if ((uint64_t)(value != 0ull)) {
                            waiting = mini_release(value, waiting);
                        }
                    } else {
                        if ((uint64_t)(kind == 254ull)) {
                            ((void (*)(void *))mini_load(mini_load(o + 8)))((void *)mini_load(o + 16));
                        } else {
                            rt_stop("an object of a kind this runtime does not have (a task or promise) was freed");
                        }
                    }
                }
            }
        }
    }
    rt_free((void *)o);
    return waiting;
}

/* Called by compiled Lean when it gives up a reference and the count is not above one. Freeing an object
frees what it alone was keeping alive, which can be a very long chain, so nothing here calls itself: one
object is freed at a time, and what that releases waits its turn. */
static uint64_t mini_lean_dec_ref_cold(uint64_t o) {
    uint64_t waiting = 0;
    if ((uint64_t)((mini_load(o) & 4294967295ull) != 1ull)) {
        return 0ull;
    }
    waiting = 0ull;
    while (1ull) {
        waiting = mini_free_one(o, waiting);
        if ((uint64_t)(waiting == 0ull)) {
            return 0ull;
        }
        o = waiting;
        waiting = (mini_load(o) & 281474976710655ull);
    }
    return 0ull;
}

void lean_dec_ref_cold(lean_object * o) {
    mini_lean_dec_ref_cold((uint64_t)o);
}
