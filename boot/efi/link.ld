/* ELF RVAs are also PE RVAs. Writable absolute pointers are rebased by
   firmware via the PE relocation directory produced by mkefi.py. */
ENTRY(efi_main)
SECTIONS {
    . = 0x1000;
    .text : { *(.text .text.*) }
    .rodata ALIGN(0x1000) : { *(.rodata .rodata.*) }
    .data ALIGN(0x1000) : { *(.data .data.*) *(.got .got.*) }
    .bss ALIGN(0x1000) (NOLOAD) : { *(.bss .bss.*) *(COMMON) }
    .rela.dyn : { *(.rela.dyn) }
    .dynamic : { *(.dynamic) }
    .dynsym : { *(.dynsym) }
    .dynstr : { *(.dynstr) }
    .hash : { *(.hash) }
    .gnu.hash : { *(.gnu.hash) }
    /DISCARD/ : { *(.eh_frame*) *(.comment) *(.note*) *(.llvm_addrsig) }
}
