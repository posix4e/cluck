import Mini.Run
import Mini.Map

/-! The real mapping run as its language defines it, on a layout like the image's, and every entry it writes
checked: none is both writable and runnable, each maps a page to itself, and each piece of the image, the
stack's hole, the heap and the device registers get what they should. -/

namespace MapTest
open Mini

def layoutAt : UInt64 := 0x10000
def windowsAt : UInt64 := 0x11000
def directoriesAt : UInt64 := 0x20000
def tablesAt : UInt64 := 0x40000

def present : UInt64 := 0x1
def writable : UInt64 := 0x2
def uncached : UInt64 := 0x18
def large : UInt64 := 0x80
def noExecute : UInt64 := 0x8000000000000000
def addressBits : UInt64 := 0x000FFFFFFFFFF000

structure Layout where
  text : UInt64 × UInt64 := (0x1000000, 0x1002000)
  rodata : UInt64 × UInt64 := (0x1002000, 0x1004000)
  data : UInt64 × UInt64 := (0x1004000, 0x100c000)
  guard : UInt64 := 0x100c000
  stack : UInt64 × UInt64 := (0x100d000, 0x1020000)
  imageEnd : UInt64 := 0x1020000
  heap : UInt64 × UInt64 := (0x1200000, 0x4000000)
  windows : List (UInt64 × UInt64) := [(0xfeb00000, 0x200), (0xfeb00200, 0x200), (0xd0001000, 0x1000)]

def State.ofLayout (l : Layout) : State := Id.run do
  let words := [l.text.1, l.text.2, l.rodata.1, l.rodata.2, l.data.1, l.data.2, l.guard, l.stack.1, l.stack.2,
    l.imageEnd, l.heap.1, l.heap.2, windowsAt, l.windows.length.toUInt64]
  let mut memory : UInt64 → Option UInt8 := fun _ => none
  for (w, k) in words.zipIdx do memory := writeBytes memory (layoutAt + 8 * k.toUInt64) w 8
  for ((base, size), k) in l.windows.zipIdx do
    memory := writeBytes (writeBytes memory (windowsAt + 16 * k.toUInt64) base 8) (windowsAt + 16 * k.toUInt64 + 8) size 8
  return { memory }

def call (function : String) (arguments : List UInt64) (s : State) : Except String UInt64 := do
  match ← Map.program.call (fun c _ _ => throw c) 100000 function arguments s with
  | (.gave value, _) => pure value
  | _ => throw s!"{function} gave nothing"

abbrev Check := Except String Unit

def wanted (what : String) (ok : Bool) : Check := if ok then pure () else throw what

/-- What a present entry may never be: writable and runnable at once, or a page other than its own. -/
def sound (what : String) (address e : UInt64) : Check := do
  if e &&& present == 0 then return
  wanted s!"{what} {address} is writable and runnable" (e &&& writable == 0 || e &&& noExecute != 0)
  wanted s!"{what} {address} is mapped somewhere else" (e &&& addressBits == address)

/-- What the mapping says of each 2 MiB stretch of the first four gigabytes, and of each 4 KiB page in
every stretch that is mapped in small pages. -/
def entries (l : Layout) : Except String (Array (UInt64 × UInt64)) := do
  let s := State.ofLayout l
  let mut pages := #[]
  for i in [0:2048] do
    let stretch := i.toUInt64 * 0x200000
    if (← call "wants_small" [layoutAt, stretch] s) == 0 then
      let e ← call "large_entry" [layoutAt, stretch] s
      sound "the stretch at" stretch e
      if e &&& present != 0 then
        wanted s!"the stretch at {stretch} is mapped but not as a large page" (e &&& large != 0)
      pages := pages.push (stretch, e)
    else
      for j in [0:512] do
        let address := stretch + j.toUInt64 * 0x1000
        let e ← call "small_entry" [layoutAt, address] s
        sound "the page at" address e
        wanted s!"the page at {address} is marked large" (e &&& large == 0)
        pages := pages.push (address, e)
  return pages

def lookup (pages : Array (UInt64 × UInt64)) (address : UInt64) : UInt64 :=
  match pages.find? (fun (a, e) => a ≤ address && address < a + (if e &&& large != 0 then 0x200000 else 0x1000)) with
  | some (_, e) => e
  | none => 0

def everyEntry : Check := do
  let l : Layout := {}
  let pages ← entries l
  let page := lookup pages
  wanted "address zero is mapped" (page 0 &&& present == 0)
  for a in [l.text.1, l.text.2 - 0x1000] do
    let e := page a
    wanted "code is not runnable, or is writable" (e &&& present != 0 && e &&& noExecute == 0 && e &&& writable == 0)
  let e := page l.rodata.1
  wanted "constants are writable or runnable" (e &&& present != 0 && e &&& noExecute != 0 && e &&& writable == 0)
  for a in [l.data.1, l.stack.1, l.stack.2 - 0x1000] do
    let e := page a
    wanted s!"{a} is not writable data" (e &&& present != 0 && e &&& noExecute != 0 && e &&& writable != 0)
  wanted "the hole under the stack is mapped" (page l.guard &&& present == 0)
  wanted "the memory after the image, before the heap, is mapped" (page l.imageEnd &&& present == 0)
  let e := page l.heap.1
  wanted "the heap is not mapped in large, writable, unrunnable pages" (e &&& large != 0 && e &&& present != 0 && e &&& noExecute != 0 && e &&& writable != 0)
  wanted "memory past the heap is mapped" (page l.heap.2 &&& present == 0)
  for (base, _) in l.windows do
    let e := page base
    wanted s!"the device registers at {base} are not uncached writable data" (e &&& present != 0 && e &&& uncached == uncached && e &&& noExecute != 0)
  wanted "memory beside device registers is mapped" (page 0xfeb01000 &&& present == 0)
  wanted "the top of the first four gigabytes is mapped" (page 0xfffff000 &&& present == 0)
  -- Only what is listed above is there: the image, the heap and the registers.
  let mapped := pages.filter (·.2 &&& present != 0)
  let small := mapped.filter (·.2 &&& large == 0)
  -- The image's 32 pages less the hole, and the registers: two windows share a page.
  wanted s!"{small.size} small pages are mapped, where the image and the registers are 31 + 2"
    (small.size == 31 + 2)

def checks : List (String × Check) := [
  ("every page and stretch: never writable and runnable, each to itself, and each piece as it should be", everyEntry)]

end MapTest
