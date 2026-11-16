/*
How the image is laid out, and with what rights.

Three loadable pieces, each starting on a 4 KiB boundary so that early.c can give each its own rights, page
by page: code (run, not written), constants (neither), and data (written, not run). After the data comes a
2 MiB hole that is never mapped, and above the hole the stack: a stack that overflows runs into the hole
and stops the machine instead of walking into the data below it. The image ends on a 2 MiB boundary, so that
the heap after it can be mapped in 2 MiB pages.

The image is linked to run at 16 MiB, where Linux itself is linked, leaving everything below unmapped. The
note for a PVH loader has its own program header so that the loader can find it.

The image's first bytes are linux.S, which a Linux boot protocol loader enters. Such a loader is given
everything from `boot_image_start` to `boot_payload_end` as one run of bytes (scripts/build-bare, mkimage);
what follows that in memory (`.bss` and the stack) is not in the file.
*/
ENTRY(pvh_entry)

PHDRS {
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    data PT_LOAD FLAGS(6);
    note PT_NOTE FLAGS(4);
}

SECTIONS {
    . = 0x1000000;
    boot_image_start = .;

    boot_text_start = .;
    .text : { KEEP(*(.boot.head)) *(.boot.text) *(.text .text.*) } :text
    . = ALIGN(0x1000);
    boot_text_end = .;

    boot_rodata_start = .;
    .note.Xen : { KEEP(*(.note.Xen)) } :rodata :note
    .rodata : { *(.rodata .rodata.*) } :rodata
    . = ALIGN(0x1000);
    boot_rodata_end = .;

    boot_data_start = .;
    .data : { *(.boot.data) *(.data .data.*) *(.got .got.*) } :data
    boot_payload_end = .;
    boot_payload_size = boot_payload_end - boot_image_start;
    .bss : { boot_bss_start = .; *(.bss .bss.*) *(COMMON) boot_bss_end = .; } :data
    . = ALIGN(0x1000);
    boot_data_end = .;

    boot_stack_guard = .;
    . += 0x200000;
    boot_stack_bottom = .;
    .stack (NOLOAD) : { KEEP(*(.stack)) } :data
    . = ALIGN(0x200000);
    boot_stack_top = .;

    boot_image_end = .;

    /* The linker is told to refuse any section this file does not place (scripts/build-bare): one it placed
    by guesswork after the stack would drag the stack's eight megabytes of nothing into the file. These three
    are the file's own tables, which are not loaded; the image is linked without symbols, so the first two
    are empty. */
    .symtab 0 : { *(.symtab) }
    .strtab 0 : { *(.strtab) }
    .shstrtab 0 : { *(.shstrtab) }

    /DISCARD/ : { *(.comment) *(.note.GNU-stack) *(.note.gnu.*) *(.eh_frame) *(.eh_frame_hdr) *(.llvm_addrsig) }
}
