/*
The front of the kernel image, as the Linux boot protocol wants it: the setup header, and the real-mode code
a BIOS-era loader runs.

A kernel image in Linux's "bzImage" shape starts with a few 512-byte sectors of this, and the kernel proper
follows. Every loader reads the header at 0x1f1 to learn how to load the rest. What happens next depends on
the loader:

  - One that enters the kernel directly in 32-bit or 64-bit mode, as a virtual machine monitor does (a Nitro
    Enclave among them), builds the `boot_params` page itself and never runs a byte of this file.
  - One that starts the kernel the way a PC's BIOS would (QEMU with -kernel, which is how this is tested)
    loads these sectors low in memory and jumps to 0x200 in real mode. The code below then does what the
    other kind of loader does: builds `boot_params`, asks the BIOS for the memory map, switches to 32-bit
    protected mode and enters the kernel proper at its first byte.

No stock loader that this project can run on its own machines enters a kernel at its 64-bit entry, and that
is the entry a Nitro Enclave uses. So this file can be built a second way (ENTER_LONG): the code below then goes on
to do what such a loader does (page tables that map memory to itself, long mode, the protocol's segments)
and enters the kernel proper 0x200 bytes in. That image is for testing the 64-bit entry under an emulator.

Nor does any of them put the kernel proper anywhere but 1 MiB. So there is a third way to build this file
(MOVE_TO, an address): the code below then copies the kernel proper there before entering it, at its 32-bit
entry. That is for testing that the image finds its way home from somewhere else, and refuses when it has
been put on top of where it has to go.

Offsets and meanings are from Linux's Documentation/arch/x86/boot.rst. mkimage fills in the three fields
that depend on the image: `setup_sects`, `syssize` and `init_size`.

This file is linked on its own, at address zero, into a flat run of bytes (scripts/build-bare).

Elsewhere. Linux's arch/x86/boot/header.S is this header; its real-mode C (arch/x86/boot/main.c and
memory.c) asks the BIOS for the same memory map with the same call. FreeBSD climbs from the BIOS in stages
instead (boot0, boot2 under its BTX monitor, then loader(8)), and for some twenty years the last stage was
programmable in Forth: loader(8) carried FICL, a small Forth, and its menus and configuration were Forth
words, until Lua replaced it. Open Firmware (Sun, Apple's PowerPC Macs, OLPC) went further, with the whole
firmware a Forth system and device drivers shipped as Forth bytecode. The idea worth keeping from them: the
first code to run is a small language a person can read whole, not compiled C. This project's version of that
is the small language in Mini/, whose first boot code is the real mapping (Mini/Map.lean); see TODO.md for
giving it a translator to machine code of its own.
*/

#define PARAMS 0x4000          /* where in this segment `boot_params` is built; the stack ENTER_LONG uses is below */
#define TABLES 0x5000          /* and the six pages of page tables ENTER_LONG builds */
#ifndef ENTER_LONG
#define CODE32 0x10            /* the 32-bit code segment in the descriptor table at the end of this file */
#else
#define CODE32 0x20
#endif
#define PARAMS_MAP_ENTRIES 0x1e8
#define PARAMS_MAP 0x2d0
#define MAP_ENTRY 20
#define MAP_MOST 128

    .section .setup, "awx", @progbits
    .code16

    .org 0x1f1
header:
    .byte 0                     /* 0x1f1 setup_sects: sectors of setup after the first (mkimage) */
    .word 0                     /* 0x1f2 root_flags */
    .long 0                     /* 0x1f4 syssize: the kernel proper, in units of 16 bytes (mkimage) */
    .word 0                     /* 0x1f8 ram_size */
    .word 0xffff                /* 0x1fa vid_mode */
    .word 0                     /* 0x1fc root_dev */
    .word 0xaa55                /* 0x1fe boot_flag */
    .byte 0xeb, real_mode - 1f  /* 0x200 a short jump over the rest of the header */
1:  .ascii "HdrS"               /* 0x202 header */
    .word 0x020f                /* 0x206 version: protocol 2.15 */
    .long 0                     /* 0x208 realmode_swtch */
    .word 0x1000                /* 0x20c start_sys_seg */
    .word name - 0x200          /* 0x20e kernel_version */
    .byte 0                     /* 0x210 type_of_loader (the loader's to fill) */
    .byte 0x01                  /* 0x211 loadflags: the kernel proper is loaded at 1 MiB or above */
    .word 0x8000                /* 0x212 setup_move_size */
    .long 0x100000              /* 0x214 code32_start: where a real-mode loader puts the kernel proper */
    .long 0                     /* 0x218 ramdisk_image */
    .long 0                     /* 0x21c ramdisk_size */
    .long 0                     /* 0x220 bootsect_kludge */
    .word 0                     /* 0x224 heap_end_ptr */
    .byte 0                     /* 0x226 ext_loader_ver */
    .byte 0                     /* 0x227 ext_loader_type */
    .long 0                     /* 0x228 cmd_line_ptr (the loader's to fill) */
    .long 0x7fffffff            /* 0x22c initrd_addr_max */
    .long 0x200000              /* 0x230 kernel_alignment */
    .byte 1                     /* 0x234 relocatable_kernel: it moves itself home from anywhere */
    .byte 21                    /* 0x235 min_alignment, as a power of two */
    .word 0x0001                /* 0x236 xloadflags: has the 64-bit entry at 0x200 */
    .long 2047                  /* 0x238 cmdline_size */
    .long 0                     /* 0x23c hardware_subarch */
    .quad 0                     /* 0x240 hardware_subarch_data */
    .long 0                     /* 0x248 payload_offset */
    .long 0                     /* 0x24c payload_length */
    .quad 0                     /* 0x250 setup_data */
    .quad 0x1000000             /* 0x258 pref_address: where the image is linked to run */
    .long 0                     /* 0x260 init_size: memory needed from the load address on (mkimage) */
    .long 0                     /* 0x264 handover_offset */
    .long 0                     /* 0x268 kernel_info_offset */
header_end:

name:
    .asciz "silo"

/* Entered here in real mode by a BIOS-style loader, with DS, ES and SS on this segment, a stack near its
top, and CS 0x20 higher (so that this instruction is at CS:0). */
real_mode:
    pushw %ds
    pushw $1f
    lretw
1:  cld
    /* An empty `boot_params`, with this file's header (as the loader has changed it) where it belongs. */
    movw $PARAMS, %di
    xorw %ax, %ax
    movw $(4096 / 2), %cx
    rep stosw
    movw $header, %si
    movw $(PARAMS + header), %di
    movw $(header_end - header), %cx
    rep movsb
    /* The memory map, one range per call to the BIOS until it says there are no more. */
    xorl %ebx, %ebx
    movw $(PARAMS + PARAMS_MAP), %di
2:  movl $0xe820, %eax
    movl $0x534d4150, %edx
    movl $MAP_ENTRY, %ecx
    int $0x15
    jc 3f
    cmpl $0x534d4150, %eax
    jne 3f
    addw $MAP_ENTRY, %di
    incb PARAMS + PARAMS_MAP_ENTRIES
    cmpb $MAP_MOST, PARAMS + PARAMS_MAP_ENTRIES
    jae 3f
    testl %ebx, %ebx
    jnz 2b
3:  cli
    /* Address line 20, which a PC keeps off until asked. */
    inb $0x92, %al
    orb $0x02, %al
    andb $0xfe, %al
    outb %al, $0x92
    /* Protected mode, with the two flat segments the boot protocol names. Addresses below are within this
    segment; where the segment itself is has to be added to the ones the processor will use directly. */
    xorl %ebx, %ebx
    movw %ds, %bx
    shll $4, %ebx
    addl %ebx, descriptors_pointer + 2
    addl %ebx, far_target
    leal PARAMS(%ebx), %esi
    lgdtl descriptors_pointer
    movl %cr0, %eax
    orl $1, %eax
    movl %eax, %cr0
    .byte 0x66, 0xea            /* a far jump to a 32-bit address */
far_target:
    .long protected_mode
    .word CODE32

    .code32
protected_mode:
    movl $0x18, %eax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %ss
    movw %ax, %fs
    movw %ax, %gs
#ifndef ENTER_LONG
    xorl %ebp, %ebp
    xorl %edi, %edi
    xorl %ebx, %ebx
    movl 0x214(%esi), %eax
#ifdef MOVE_TO
    /* A loader that puts the kernel proper somewhere other than 1 MiB, as the protocol lets one: the bytes
    are copied to MOVE_TO and entered there. `syssize` is their number, in units of 16. */
    movl %esi, %edx
    movl 0x1f4(%esi), %ecx
    shll $4, %ecx
    movl %eax, %esi
    movl $MOVE_TO, %edi
    rep movsb
    movl %edx, %esi
    xorl %edi, %edi
    movl $MOVE_TO, %eax
#endif
    jmp *%eax
#else
    /* Page tables mapping the first four gigabytes to themselves in 2 MiB pages: one top-level table, one
    below it, four page directories. Everything here is addressed from ESI, which is where PARAMS is. */
    movl %esi, %esp
    leal (TABLES - PARAMS)(%esi), %ebx
    movl %ebx, %edi
    xorl %eax, %eax
    movl $(6 * 4096 / 4), %ecx
    rep stosl
    leal 0x1003(%ebx), %eax
    movl %eax, (%ebx)
    leal 0x2003(%ebx), %eax
    xorl %ecx, %ecx
1:  movl %eax, 0x1000(%ebx, %ecx, 8)
    addl $0x1000, %eax
    incl %ecx
    cmpl $4, %ecx
    jb 1b
    movl $0x83, %eax
    xorl %ecx, %ecx
2:  movl %eax, 0x2000(%ebx, %ecx, 8)
    addl $0x200000, %eax
    incl %ecx
    cmpl $2048, %ecx
    jb 2b
    /* Long mode: physical address extension, the tables, the enable bit, paging. */
    movl %cr4, %eax
    orl $(1 << 5), %eax
    movl %eax, %cr4
    movl %ebx, %cr3
    movl $0xc0000080, %ecx
    rdmsr
    orl $(1 << 8), %eax
    wrmsr
    movl %cr0, %eax
    orl $(1 << 31), %eax
    movl %eax, %cr0
    pushl $0x10
    leal (long_mode - PARAMS)(%esi), %eax
    pushl %eax
    lretl

    .code64
long_mode:
    movl %esi, %esi
    movl 0x214(%rsi), %eax
    addq $0x200, %rax
    jmp *%rax
#endif

    .balign 8
descriptors:
    .quad 0
    .quad 0
#ifndef ENTER_LONG
    .quad 0x00cf9a000000ffff    /* 0x10: code, 32-bit, all four gigabytes */
    .quad 0x00cf92000000ffff    /* 0x18: data, the same */
#else
    .quad 0x00af9a000000ffff    /* 0x10: code, 64-bit */
    .quad 0x00cf92000000ffff    /* 0x18: data, all four gigabytes */
    .quad 0x00cf9a000000ffff    /* 0x20: code, 32-bit, for the steps between real mode and long mode */
#endif
descriptors_end:
descriptors_pointer:
    .word descriptors_end - descriptors - 1
    .long descriptors
