import Mini.Lang

/-! # The real mapping

What the machine may do with each page of its memory, written into the page tables at boot. Until this runs
the machine has the mapping `boot/entry.S` built to get going: the first four gigabytes mapped to themselves,
everything writable and runnable. After it, and after `boot/early.c` makes the processor reload the root,
there is:

- code that can be run and not written;
- constants that can be read only;
- data, the stack and the heap that can be written and not run;
- a hole under the stack, so one that overflows stops the machine instead of walking into the data below;
- device registers, uncached, and nothing beside them;
- and nothing else: address zero, and everything the program has no business touching, is not there.

Pages of 2 MiB are used for the heap and memory shared with devices; the 2 MiB stretches that hold part of
the image, whose pieces have different rights, or device registers, are mapped in 4 KiB pages.

Where other systems do this. Linux's `arch/x86/mm/init_64.c` builds the kernel's direct map with large pages
where it can and splits them where rights differ, and `mark_rodata_ro` takes write away from the kernel's
constants late in boot; here there is nothing before the program to keep writable, so it is done once, before
it runs. seL4 maps its kernel image at boot and then has no kernel heap at all: every other page is handed out
as a capability. Here there is one program, so the whole map is decided at once and never changes.

The layout comes from `boot/link.ld` and what the boot loader said, as words at `layout`:

| word | | word | |
|---|---|---|---|
| 0, 1 | the code | 7, 8 | the stack |
| 2, 3 | the constants | 9 | the end of the image |
| 4, 5 | the data | 10, 11 | the memory for devices, then the heap |
| 6 | the hole under the stack (it ends where the stack starts) | 12, 13 | the device windows: where, how many |

Each device window is two words, where and how many bytes.

This is the first of the boot path written in the small language rather than C. FreeBSD's loader(8) was
programmable in Forth (FICL) for some twenty years, and Open Firmware was a Forth system through and through:
the first code to run was a small language a person could read whole. The same aim here is a translator from
this language straight to machine code, with no C compiler between (TODO.md). -/

namespace Mini.Map

def page : Expr := 0x200000
def small : Expr := 0x1000
def present : Expr := 0x1
def write : Expr := 0x2
def writeThrough : Expr := 0x8
def noCache : Expr := 0x10
def large : Expr := 0x80
def noExecute : Expr := .lit (UInt64.ofNat (2 ^ 63))

/-- Word `k` of the layout. -/
def field (k : Nat) : Expr := .load ("layout" + .lit (UInt64.ofNat (8 * k)))
def textStart := field 0
def textEnd := field 1
def rodataStart := field 2
def rodataEnd := field 3
def dataStart := field 4
def dataEnd := field 5
def guard := field 6
def stackBottom := field 7
def stackTop := field 8
def imageEnd := field 9
def heapFrom := field 10
def heapEnd := field 11
def windows := field 12
def windowCount := field 13

def inRange (a start end_ : Expr) : Expr := Expr.and (Expr.le start a) (Expr.lt a end_)
def flags (fs : List Expr) : Expr := fs.foldl Expr.or "address"

def inHeap : Function where
  name := "in_heap"
  about := "Whether the memory set aside for devices or the heap holds `address`."
  parameters := ["layout", "address"]
  body := [.give (inRange "address" heapFrom heapEnd)]

def hasRegisters : Function where
  name := "has_registers"
  about := "Whether any device's registers are in the `size` bytes at `address`."
  parameters := ["layout", "address", "size"]
  body := [
    .set "i" 0,
    .loop (Expr.lt "i" windowCount) [
      .set "first" (.load (windows + "i" * 16)),
      .set "last" (.load (windows + "i" * 16) + .load (windows + "i" * 16 + 8) - 1),
      .branch (Expr.and (Expr.le "first" ("address" + "size" - 1)) (Expr.le "address" "last")) [.give 1] [],
      .set "i" ("i" + 1)],
    .give 0]

def smallEntry : Function where
  name := "small_entry"
  about := "What the 4 KiB page at `address` is for, and so how it is mapped: zero for not at all. The pieces of the\nimage begin and end on 4 KiB boundaries, by link.ld. Device registers are mapped so that the processor never\nkeeps a copy of what it reads from them or puts off what it writes."
  parameters := ["layout", "address"]
  body := [
    .branch (inRange "address" textStart textEnd) [.give (flags [present])] [],
    .branch (inRange "address" rodataStart rodataEnd) [.give (flags [present, noExecute])] [],
    .branch (inRange "address" dataStart dataEnd) [.give (flags [present, write, noExecute])] [],
    .branch (inRange "address" guard stackBottom) [.give 0] [],
    .branch (inRange "address" stackBottom stackTop) [.give (flags [present, write, noExecute])] [],
    .call (some "heap") "in_heap" ["layout", "address"],
    .branch (Expr.ne "heap" 0) [.give (flags [present, write, noExecute])] [],
    .call (some "registers") "has_registers" ["layout", "address", small],
    .branch (Expr.ne "registers" 0) [.give (flags [present, write, noExecute, noCache, writeThrough])] [],
    .give 0]

def wantsSmall : Function where
  name := "wants_small"
  about := "Whether the 2 MiB at `address` has to be mapped in 4 KiB pages: it holds part of the image, whose pieces\nhave different rights, or device registers, which are a page or two with nothing of ours beside them."
  parameters := ["layout", "address"]
  body := [
    .branch (Expr.and (Expr.lt "address" imageEnd) (Expr.lt textStart ("address" + page))) [.give 1] [],
    .call (some "registers") "has_registers" ["layout", "address", page],
    .give "registers"]

def largeEntry : Function where
  name := "large_entry"
  about := "The rest is the heap and the memory shared with devices, in 2 MiB pages, or nothing. The heap begins and\nends on 2 MiB boundaries, by link.ld and memory_init."
  parameters := ["layout", "address"]
  body := [
    .call (some "heap") "in_heap" ["layout", "address"],
    .branch (Expr.ne "heap" 0) [.give (flags [present, large, write, noExecute])] [],
    .give 0]

def map : Function where
  name := "boot_map"
  about := "Rewrites the 2048 entries of the page directories at `directories` in place, taking tables of 4 KiB pages\nfrom the `count` at `tables` as needed. Gives 0, or 1 if there were not enough tables, in which case the\nmachine is not to be started. A table is filled in before the directory points at it, so a page in use\n(this code, this stack) goes straight from its old mapping to its new one and is never missing in between."
  seen := some { result := "int", parameters := ["uint64_t const *", "uint64_t *", "uint64_t *", "size_t"] }
  parameters := ["layout", "directories", "tables", "count"]
  body := [
    .set "used" 0,
    .set "i" 0,
    .loop (Expr.lt "i" 2048) [
      .set "address" ("i" * page),
      .call (some "wanted") "wants_small" ["layout", "address"],
      .branch (Expr.eq "wanted" 0)
        [.call (some "entry") "large_entry" ["layout", "address"],
         .store ("directories" + "i" * 8) "entry"]
        [.branch (Expr.eq "used" "count") [.give 1] [],
         .set "table" ("tables" + "used" * 4096),
         .set "used" ("used" + 1),
         .set "j" 0,
         .loop (Expr.lt "j" 512) [
           .call (some "entry") "small_entry" ["layout", "address" + "j" * small],
           .store ("table" + "j" * 8) "entry",
           .set "j" ("j" + 1)],
         .store ("directories" + "i" * 8) (Expr.or (Expr.or "table" present) write)],
      .set "i" ("i" + 1)],
    .give 0]

def program : Program where
  about := "The real mapping, put in place at boot."
  preamble := "#include <stddef.h>\n#include <stdint.h>\n"
  globals := []
  arrays := []
  functions := [inHeap, hasRegisters, smallEntry, wantsSmall, largeEntry, map]

end Mini.Map
