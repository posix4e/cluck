"""Package the ELF PIE from link.ld as an x64 EFI PE32+ application.

Compiled Init and Std use the SysV ABI and ELF. All code is position
independent. Only .data contains absolute pointers. Translate ELF RELATIVE
relocations to PE DIR64 records for the firmware's standard image loader.
"""
import struct
import sys
from collections import defaultdict
from pathlib import Path

PAGE = 4096
FILE_ALIGN = 512
IMAGE_BASE = 0x10000000
FLAGS = {".text": 0x60000020, ".rodata": 0x40000040,
         ".data": 0xC0000040, ".bss": 0xC0000080, ".reloc": 0x42000040}


def align(n, unit):
    return (n + unit - 1) // unit * unit


def read_pie(blob):
    if blob[:7] != b"\x7fELF\x02\x01\x01" or struct.unpack_from("<HH", blob, 16) != (3, 62):
        raise ValueError("expected a little-endian x86_64 ELF PIE")
    entry, _, table = struct.unpack_from("<QQQ", blob, 24)
    stride, count, name_index = struct.unpack_from("<HHH", blob, 58)
    headers = [struct.unpack_from("<IIQQQQIIQQ", blob, table + i * stride) for i in range(count)]
    name_offset = headers[name_index][4]
    load = {}
    relocations = b""
    metadata = {".dynamic", ".dynsym", ".dynstr", ".hash", ".gnu.hash"}
    for name, kind, flags, rva, offset, length, _, _, _, _ in headers:
        name = blob[name_offset + name:].split(b"\0", 1)[0].decode()
        if name == ".rela.dyn":
            relocations = blob[offset:offset + length]
        elif name in FLAGS:
            if rva < PAGE or rva % PAGE:
                raise ValueError(f"{name} is not page-aligned")
            raw = b"" if kind == 8 else blob[offset:offset + length]
            load[name] = (rva, length, bytearray(raw))
        elif flags & 2 and name not in metadata:
            raise ValueError(f"unexpected loadable section {name}")
    pages = defaultdict(list)
    data_rva, _, data = load[".data"]
    for at, info, addend in struct.iter_unpack("<QQq", relocations):
        if info != 8 or not data_rva <= at <= data_rva + len(data) - 8:
            raise ValueError(f"unsupported relocation {info} at {at:#x}")
        if not any(start <= addend <= start + size for start, size, _ in load.values()):
            raise ValueError(f"pointer to omitted section at {addend:#x}")
        struct.pack_into("<Q", data, at - data_rva, IMAGE_BASE + addend)
        pages[at & -PAGE].append((10 << 12) | (at % PAGE))
    reloc = bytearray()
    for page, entries in sorted(pages.items()):
        if len(entries) % 2:
            entries.append(0)
        reloc.extend(struct.pack("<II", page, 8 + 2 * len(entries)))
        reloc.extend(struct.pack("<" + "H" * len(entries), *entries))
    reloc_rva = align(max(start + size for start, size, _ in load.values()), PAGE)
    load[".reloc"] = reloc_rva, len(reloc), reloc
    return entry, load


def make_pe(entry, load):
    pe_offset = 0x40
    optional = pe_offset + 24
    sections = optional + 240
    header_size = align(sections + len(load) * 40, FILE_ALIGN)
    image = bytearray(header_size)
    image[:2] = b"MZ"
    struct.pack_into("<I", image, 0x3c, pe_offset)
    struct.pack_into("<4sHHIIIHH", image, pe_offset, b"PE\0\0", 0x8664,
                     len(load), 0, 0, 0, 240, 0x22)
    text_rva, text_len, _ = load[".text"]
    initialized = sum(align(len(data), FILE_ALIGN)
                      for name, (_, _, data) in load.items() if name not in {".text", ".bss"})
    reloc_rva, reloc_len, _ = load[".reloc"]
    struct.pack_into("<HBBIIIIIQII", image, optional, 0x20b, 0, 0,
                     align(text_len, FILE_ALIGN), initialized, load[".bss"][1],
                     entry, text_rva, IMAGE_BASE, PAGE, FILE_ALIGN)
    struct.pack_into("<II", image, optional + 56, align(reloc_rva + reloc_len, PAGE), header_size)
    struct.pack_into("<HH", image, optional + 68, 10, 0x140)  # EFI application, dynamic base, NX
    struct.pack_into("<I", image, optional + 108, 16)
    struct.pack_into("<II", image, optional + 112 + 5 * 8, reloc_rva, reloc_len)
    for i, (name, (rva, length, data)) in enumerate(sorted(load.items(), key=lambda it: it[1][0])):
        size = align(len(data), FILE_ALIGN)
        struct.pack_into("<8sIIIIIIHHI", image, sections + i * 40, name.encode(),
                         length, rva, size, len(image) if size else 0, 0, 0, 0, 0, FLAGS[name])
        image.extend(data)
        image.extend(bytes(size - len(data)))
    return image


if __name__ == "__main__":
    entry, load = read_pie(Path(sys.argv[1]).read_bytes())
    Path(sys.argv[2]).write_bytes(make_pe(entry, load))
