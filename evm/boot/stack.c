/*
A larger stack for `main`, with a hole under it.

Firmware starts an EFI application on a stack of about 128 KiB. Jaune recurses deeper than that: as a process
the service fails on a 128 KiB stack and runs on 512 KiB. The OS's boot/efi/platform.c is compiled for this
package with `main` renamed to this function, which moves to a stack of its own and calls the real one.

The stack is 64 MiB of the image's memory, and its lowest 1 MiB is taken out of the mapping before anything
runs on it (the OS's boot/efi/guard.c, which says how). Recursion that uses up the 63 MiB above reaches the
hole, the processor stops it there, and the machine says so and halts: it does not write on what the linker
put below. A function could step over a hole smaller than its own frame without touching it; the largest
frame in the image is under 6 KiB (the largest `sub ..., %rsp` in its disassembly), and the hole is 1 MiB.

If the hole cannot be made the image does not go on: it says why and stops.
*/
#include <stddef.h>

#include <stdbool.h>
#include "../../boot/boot.h"

extern int main(int, char **);
extern bool efi_guard(void * start, size_t bytes);
#define HOLE (1u << 20)
static _Alignas(4096) unsigned char stack[64u << 20];

int evm_main_on_its_own_stack(int argc, char ** argv) {
    if (!efi_guard(stack, HOLE)) boot_halt(5);
    void * top = stack + sizeof stack;
    int (*entry)(int, char **) = main;
    int result;
    __asm__ volatile(
        "mov %%rsp, %%rbx\n\t"
        "mov %[top], %%rsp\n\t"
        "call *%[entry]\n\t"
        "mov %%rbx, %%rsp"
        : "=a"(result)
        : [top] "r"(top), [entry] "r"(entry), "D"(argc), "S"(argv)
        : "rbx", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory", "cc");
    return result;
}
