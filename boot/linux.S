/*
The first bytes of the image, for a loader that speaks the Linux boot protocol.

Such a loader (a Nitro Enclave's is one, and uses the 64-bit entry with the image at 1 MiB) is handed a
kernel image in Linux's "bzImage" shape: a few sectors
of real-mode setup (setup.S) and after them the kernel proper, which here is this image as a flat run of
bytes. The loader puts those bytes somewhere in memory and enters them in one of two ways, both with the
address of a `boot_params` page in ESI/RSI and interrupts off:

  - at their first byte, in 32-bit protected mode with paging off;
  - 0x200 bytes in, in 64-bit mode on the loader's own page tables, which map memory to itself.

So this section is linked first (link.ld), its 64-bit entry is at exactly 0x200, and it cannot assume where
it is running: the image is linked to run at 16 MiB and the loader may have put it anywhere, 1 MiB being
usual. All this code does is find out where it is, move the image home, and jump to the copy; from there
entry.S carries on as it does for a PVH loader.

The copy runs from the last byte down, which is right whenever the image has to move up. An image loaded
above its home must be clear of it, or the copy would overwrite the code doing the copying; that is refused
with a line on the serial port.

The 64-bit entry relies on the loader's tables mapping the image's home. The protocol promises that for
`init_size` bytes from where the image was loaded, which mkimage sets to reach from 1 MiB to the end of the
image at home; a loader that puts the image higher than its home and maps only what it must is not served.
*/

#define COM1 0x3F8

/* Writes the refusal over the serial port, a byte at a time, and stops. The text's address is in ESI/RSI.
The labels are numbered high so that the code around each use can keep 1, 2 and 3 for itself. */
    .macro say_and_stop
97: lodsb
    testb %al, %al
    jz 99f
    movb %al, %ah
    movw $(COM1 + 5), %dx
98: inb %dx, %al
    testb $0x20, %al
    jz 98b
    movw $COM1, %dx
    movb %ah, %al
    outb %al, %dx
    jmp 97b
99: hlt
    jmp 99b
    .endm

    .section .boot.head, "ax", @progbits
    .code32
    .globl linux_head
linux_head:
    cli
    cld
    /* Where is this? A call pushes the address of the next instruction, and the only memory known to be
    writable is the page ESI points at, which has four bytes set aside for exactly this. */
    leal 0x1e8(%esi), %esp
    call 1f
1:  popl %ebp
    subl $(1b - linux_head), %ebp
    movl %esi, %ebx
    movl $boot_image_start, %edi
    cmpl %edi, %ebp
    je 3f
    jb 2f
    cmpl $boot_payload_end, %ebp
    jae 2f
    leal (linux_refusal - linux_head)(%ebp), %esi
    say_and_stop
2:  movl $boot_payload_size, %ecx
    leal -1(%ebp, %ecx), %esi
    leal -1(%edi, %ecx), %edi
    std
    rep movsb
    cld
3:  movl $linux_home32, %eax
    jmp *%eax

linux_refusal:
    .asciz "silo boot: loaded on top of where the image has to go\n"

    .org 0x200
    .code64
    cli
    cld
    leaq linux_head(%rip), %rbp
    movq %rsi, %r8
    movl $boot_image_start, %edi
    cmpq %rdi, %rbp
    je 3f
    jb 2f
    movl $boot_payload_end, %eax
    cmpq %rax, %rbp
    jae 2f
    leaq linux_refusal(%rip), %rsi
    say_and_stop
2:  movl $boot_payload_size, %ecx
    leaq -1(%rbp, %rcx), %rsi
    leaq -1(%rdi, %rcx), %rdi
    std
    rep movsb
    cld
3:  movl $linux_home64, %eax
    jmp *%rax
