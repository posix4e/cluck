/* setup.S as a flat run of bytes that starts at address zero of its segment. */
SECTIONS {
    . = 0;
    .setup : { *(.setup) }
    /DISCARD/ : { *(.text) *(.data) *(.bss) *(.comment) *(.note.*) *(.llvm_addrsig) }
}
