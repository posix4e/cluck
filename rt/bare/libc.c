/*
The five functions the runtime and compiled code expect of a C library, for a machine that has none.

Copying and filling are the processor's own instructions for them where it has them (x86-64: `rep movsb`,
`rep stosb`), which on processors of the last ten years are as fast as anything for a few bytes and for
megabytes. Elsewhere, and for comparing and measuring, plain loops a byte at a time. The compiler is told
not to recognise the loops (-fno-builtin), or it would turn each back into a call to the function it is in.

They were plain loops everywhere until a guest was seen to take a request of two megabytes in at six
megabytes a second, every byte of it copied this way several times.

Elsewhere. Linux's lib/string.c has the same plain loops, as the fallback behind its assembly versions,
and arch/x86/lib/memcpy_64.S the same `rep movsb` where the processor says it is fast.
*/
#include <stddef.h>

void * memcpy(void * to, void const * from, size_t count) {
#if defined(__x86_64__)
    void * t = to;
    __asm__ volatile("rep movsb" : "+D"(t), "+S"(from), "+c"(count) : : "memory");
#else
    unsigned char * t = to;
    unsigned char const * f = from;
    for (size_t i = 0; i < count; i++) t[i] = f[i];
#endif
    return to;
}

void * memmove(void * to, void const * from, size_t count) {
    unsigned char * t = to;
    unsigned char const * f = from;
    // Forward when that cannot write over what is still to be read: the common case, and the fast one.
    if (t <= f || t >= f + count) return memcpy(to, from, count);
    for (size_t i = count; i > 0; i--) t[i - 1] = f[i - 1];
    return to;
}

void * memset(void * to, int byte, size_t count) {
#if defined(__x86_64__)
    void * t = to;
    __asm__ volatile("rep stosb" : "+D"(t), "+c"(count) : "a"(byte) : "memory");
#else
    unsigned char * t = to;
    for (size_t i = 0; i < count; i++) t[i] = (unsigned char)byte;
#endif
    return to;
}

int memcmp(void const * left, void const * right, size_t count) {
    unsigned char const * l = left;
    unsigned char const * r = right;
    for (size_t i = 0; i < count; i++) {
        if (l[i] != r[i]) return l[i] < r[i] ? -1 : 1;
    }
    return 0;
}

size_t strlen(char const * text) {
    size_t length = 0;
    while (text[length] != 0) length++;
    return length;
}
