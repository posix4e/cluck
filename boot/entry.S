/*
Where the machine hands over.

A boot loader leaves the processor in 32-bit protected mode with paging off and a pointer to what it knows
about the machine in a register. From there to compiled C takes: a stack, page tables that map memory to
itself, long mode, the floating-point and vector registers switched on (compiled code uses them freely), and
a jump. That is this file, and nothing else is.

There are three ways in, and they meet at `long_mode_entry`:

  - `pvh_entry`, for a PVH loader given the image as an ELF file (QEMU with -kernel, among others). Its
    address is in the ELF note below, and the loader passes the address of an `hvm_start_info` in EBX.
  - `linux_home32` and `linux_home64`, for a loader that speaks the Linux boot protocol, as a Nitro Enclave's
    does. Those loaders enter at the image's first bytes (linux.S), which move the image to where it is
    linked to run and jump here with the address of a `boot_params` page in EBX or R8, and where the loader
    had put the image in EBP or RBP.

The page tables here map the first four gigabytes one-to-one in 2 MiB pages, writable and executable. They
are only what the machine boots on: early.c rewrites them, before `main` runs, so that code cannot be written,
data cannot be run, nothing else is mapped at all, and the page under the stack is missing.

Exceptions are fatal: there is one small stub per vector, which records which one it was and goes to C to
say so and stop. No interrupt is ever enabled.
*/

#define MSR_EFER 0xC0000080

/* The note a PVH loader looks for: XEN_ELFNOTE_PHYS32_ENTRY (18), owner "Xen", the 32-bit entry address. */
    .section .note.Xen, "a", @note
    .balign 4
    .long 4
    .long 8
    .long 18
    .asciz "Xen"
    .balign 4
    .quad pvh_entry
    .balign 4

    .section .boot.text, "ax", @progbits
    .code32
    .globl pvh_entry
pvh_entry:
    cli
    cld
    movl $boot_stack_top, %esp
    movl %ebx, boot_info
    movl $1, boot_kind
    jmp enter_long_mode

/* From linux.S, entered in 32-bit mode: the image is home, paging is off, the segments are the loader's. */
    .globl linux_home32
linux_home32:
    movl $boot_stack_top, %esp
    movl %ebx, boot_info
    movl %ebp, boot_loaded_at
    movl $2, boot_kind

enter_long_mode:
    /* Physical address extension, which long mode needs, and the two bits that let SSE instructions run. */
    movl %cr4, %eax
    orl $((1 << 5) | (1 << 9) | (1 << 10)), %eax
    movl %eax, %cr4
    movl $boot_pml4, %eax
    movl %eax, %cr3
    /* Long mode enable, which takes effect when paging goes on, and the no-execute bit in page tables. */
    movl $MSR_EFER, %ecx
    rdmsr
    orl $((1 << 8) | (1 << 11)), %eax
    wrmsr
    /* Paging and write protection on; the floating-point unit present, not emulated. */
    movl %cr0, %eax
    andl $~(1 << 2), %eax
    orl $((1 << 31) | (1 << 16) | (1 << 1) | 1), %eax
    movl %eax, %cr0
    lgdt boot_gdt_pointer
    ljmp $0x08, $long_mode_entry

/* From linux.S, entered in 64-bit mode: the image is home, but the segments and the page tables are still
the loader's. Take our own descriptor table and code segment, set the control registers as the 32-bit path
leaves them, and change to our own page tables. */
    .code64
    .globl linux_home64
linux_home64:
    movl $boot_stack_top, %esp
    movq %r8, boot_info(%rip)
    movq %rbp, boot_loaded_at(%rip)
    movl $3, boot_kind(%rip)
    lgdt boot_gdt_pointer(%rip)
    pushq $0x08
    leaq 1f(%rip), %rax
    pushq %rax
    lretq
1:  movq %cr4, %rax
    orq $((1 << 9) | (1 << 10)), %rax
    movq %rax, %cr4
    movl $MSR_EFER, %ecx
    rdmsr
    orl $(1 << 11), %eax
    wrmsr
    movq %cr0, %rax
    andq $~(1 << 2), %rax
    orq $((1 << 16) | (1 << 1)), %rax
    movq %rax, %cr0
    movl $boot_pml4, %eax
    movq %rax, %cr3

long_mode_entry:
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    movw %ax, %fs
    movw %ax, %gs
    movq $boot_stack_top, %rsp
    xorl %ebp, %ebp
    /* Memory the program expects to start as zero. A loader given an ELF file clears it; one given a flat
    image knows nothing about it. Cleared here either way. */
    movl $boot_bss_start, %edi
    movl $boot_bss_end, %ecx
    subl %edi, %ecx
    xorl %eax, %eax
    cld
    rep stosb
    movq boot_info(%rip), %rdi
    movl boot_kind(%rip), %esi
    call silo_boot
1:  hlt
    jmp 1b

/* One stub per exception vector. The processor pushes an error code for some vectors and not for others;
the stubs even that out, add the vector number, and share the rest. */
    .macro fault_stub vector, pushes_error
    .balign 16
fault_stub_\vector:
    .if \pushes_error == 0
    pushq $0
    .endif
    pushq $\vector
    jmp fault_common
    .endm

    .text
    .code64
    fault_stub 0, 0
    fault_stub 1, 0
    fault_stub 2, 0
    fault_stub 3, 0
    fault_stub 4, 0
    fault_stub 5, 0
    fault_stub 6, 0
    fault_stub 7, 0
    fault_stub 8, 1
    fault_stub 9, 0
    fault_stub 10, 1
    fault_stub 11, 1
    fault_stub 12, 1
    fault_stub 13, 1
    fault_stub 14, 1
    fault_stub 15, 0
    fault_stub 16, 0
    fault_stub 17, 1
    fault_stub 18, 0
    fault_stub 19, 0
    fault_stub 20, 0
    fault_stub 21, 1
    fault_stub 22, 0
    fault_stub 23, 0
    fault_stub 24, 0
    fault_stub 25, 0
    fault_stub 26, 0
    fault_stub 27, 0
    fault_stub 28, 0
    fault_stub 29, 1
    fault_stub 30, 1
    fault_stub 31, 0

fault_common:
    /* On the stack: vector, error code, then what the processor saved (RIP, CS, RFLAGS, RSP, SS). */
    movq %rsp, %rdi
    andq $-16, %rsp
    call silo_fault
1:  hlt
    jmp 1b

    .section .rodata
    .balign 8
    .globl boot_fault_stubs
boot_fault_stubs:
    .irp vector, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
    .quad fault_stub_\vector
    .endr

    .section .boot.data, "aw", @progbits
    .balign 8
boot_gdt:
    .quad 0
    .quad 0x00AF9A000000FFFF    /* 0x08: 64-bit code */
    .quad 0x00CF92000000FFFF    /* 0x10: data */
boot_gdt_end:
boot_gdt_pointer:
    .word boot_gdt_end - boot_gdt - 1
    .quad boot_gdt
    .balign 8
    .globl boot_info
boot_info:
    .quad 0
/* Where a Linux boot protocol loader put the image before it moved itself (linux.S leaves it in EBP/RBP). */
    .globl boot_loaded_at
boot_loaded_at:
    .quad 0
    .globl boot_kind
boot_kind:
    .long 0

/* Memory mapped to itself: one top-level table, one below it, and four page directories of 2 MiB pages. */
    .balign 4096
boot_pml4:
    .quad boot_pdpt + 0x3
    .fill 511, 8, 0
boot_pdpt:
    .quad boot_pd + 0x0000 + 0x3
    .quad boot_pd + 0x1000 + 0x3
    .quad boot_pd + 0x2000 + 0x3
    .quad boot_pd + 0x3000 + 0x3
    .fill 508, 8, 0
    .globl boot_pd
boot_pd:
    .set page, 0
    .rept 2048
    .quad (page << 21) | 0x83
    .set page, page + 1
    .endr

/* The stack, in a section of its own so that link.ld can leave a hole under it. */
    .section .stack, "aw", @nobits
    .balign 16
    .skip 8 * 1024 * 1024
