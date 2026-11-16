/*
Hashing bytes.

Lean hashes strings and byte arrays with the 64-bit MurmurHash2 (MurmurHash64A, by Austin Appleby, public
domain), and compiled Lean depends on the exact values: a `HashMap` built at compile time and one probed at
run time have to agree. So this is that function, bit for bit.
*/
#include "rt.h"

uint64_t rt_hash_bytes(uint8_t const * bytes, size_t length, uint64_t seed) {
    const uint64_t m = 0xc6a4a7935bd1e995ull;
    const int r = 47;
    uint64_t h = seed ^ (length * m);
    uint8_t const * end = bytes + (length / 8) * 8;
    while (bytes != end) {
        uint64_t k;
        memcpy(&k, bytes, 8);
        bytes += 8;
        k *= m;
        k ^= k >> r;
        k *= m;
        h ^= k;
        h *= m;
    }
    switch (length & 7) {
    case 7: h ^= (uint64_t)bytes[6] << 48; /* fall through */
    case 6: h ^= (uint64_t)bytes[5] << 40; /* fall through */
    case 5: h ^= (uint64_t)bytes[4] << 32; /* fall through */
    case 4: h ^= (uint64_t)bytes[3] << 24; /* fall through */
    case 3: h ^= (uint64_t)bytes[2] << 16; /* fall through */
    case 2: h ^= (uint64_t)bytes[1] << 8;  /* fall through */
    case 1:
        h ^= (uint64_t)bytes[0];
        h *= m;
    }
    h ^= h >> r;
    h *= m;
    h ^= h >> r;
    return h;
}
