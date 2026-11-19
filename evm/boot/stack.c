/*
A larger stack for `main`.

Firmware starts an EFI application on a stack of about 128 KiB. Jaune recurses deeper than that: as a process
the service fails on a 128 KiB stack and runs on 512 KiB. The OS's boot/efi/platform.c is compiled for this
package with `main` renamed to this function, which moves to a 64 MiB stack of its own and calls the real one.

Nothing guards the bottom of this stack. Recursion deeper than 64 MiB writes into whatever the linker put
below it. A guard page needs the page tables, which belong to firmware on this target (THREAT_MODEL.md).
*/
#include <stddef.h>

extern int main(int, char **);
static _Alignas(16) unsigned char stack[64u << 20];

int evm_main_on_its_own_stack(int argc, char ** argv) {
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
