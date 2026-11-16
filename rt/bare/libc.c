/*
The five functions the runtime and compiled code expect of a C library, for a machine that has none.

Plain loops, a byte at a time. The compiler is told not to recognise them (-fno-builtin), or it would turn
each loop back into a call to the function it is in.
*/
#include <stddef.h>

void * memcpy(void * to, void const * from, size_t count) {
    unsigned char * t = to;
    unsigned char const * f = from;
    for (size_t i = 0; i < count; i++) t[i] = f[i];
    return to;
}

void * memmove(void * to, void const * from, size_t count) {
    unsigned char * t = to;
    unsigned char const * f = from;
    if (t < f) {
        for (size_t i = 0; i < count; i++) t[i] = f[i];
    } else {
        for (size_t i = count; i > 0; i--) t[i - 1] = f[i - 1];
    }
    return to;
}

void * memset(void * to, int byte, size_t count) {
    unsigned char * t = to;
    for (size_t i = 0; i < count; i++) t[i] = (unsigned char)byte;
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
