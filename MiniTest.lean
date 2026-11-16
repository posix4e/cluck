import Mini.Run
import Mini.Alloc

/-! Runs the allocator as the language defines it, with no C involved, and checks what it does. A run fails
by itself if the allocator reads memory nothing has written, steps outside an array, or does anything else
C leaves open. -/

open Mini

def base : UInt64 := 0x100000
def heapSize : UInt64 := 0x100000

/-- The platform: one region, and running out of memory ends the run. -/
def outside : Outside := fun c s =>
  if c.startsWith "silo_plat_heap" then pure (base, { s with globals := put s.globals "heap_size" heapSize })
  else throw c

def call (function : String) (argument : UInt64) (s : State) : Except String (Ending × State) :=
  Alloc.program.call outside 100000 function [argument] s

def malloc (size : UInt64) (s : State) : Except String (UInt64 × State) := do
  match ← call "rt_malloc" size s with
  | (.gave block, s) => pure (block, s)
  | (.stopped why, _) => throw s!"stopped: {why}"
  | (.on, _) => throw "rt_malloc gave nothing"

def free (block : UInt64) (s : State) : Except String State := do
  match ← call "rt_free" block s with
  | (.stopped why, _) => throw s!"stopped: {why}"
  | (_, s) => pure s

def scenario : Except String (List (String × Bool)) := do
  let s := Alloc.program.start
  let (a, s) ← malloc 1 s
  let (b, s) ← malloc 1 s
  -- The block is used, then freed.
  let s := { s with memory := put (put s.memory a (some 0xDEAD)) (a + 8) (some 0xBEEF) }
  let s ← free a s
  let wiped := s.memory a == some 0 && s.memory (a + 8) == some 0
  let (again, s) ← malloc 16 s
  let twice := match free b s >>= free b with
    | .error why => why == "stopped: a block was freed that is not in use"
    | .ok _ => false
  let (large, s) ← malloc 5000 s
  let tooMuch := match malloc 0x200000 s with
    | .error why => why == "lean_internal_panic_out_of_memory()"
    | .ok _ => false
  -- Blocks of mixed sizes, some freed: no two in use ever share a byte.
  let mut state := s
  let mut live : Array (UInt64 × UInt64) := #[]
  let mut apart := true
  let mut seed : UInt64 := 12345
  for _ in [0:300] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let size := (seed >>> 33) % 600 + 1
    if (seed >>> 20) % 3 == 0 && live.size > 0 then
      let i := ((seed >>> 40) % live.size.toUInt64).toNat
      state ← free live[i]!.1 state
      live := live.eraseIdx! i
    else
      let (block, next) ← malloc size state
      state := next
      apart := apart && live.all fun (other, length) => block + size ≤ other || other + length ≤ block
      live := live.push (block, size)
  return [
    ("the first block starts after its header", a == base + 16),
    ("the next block does not overlap it", b == a + 32),
    ("a freed block is zeroed", wiped),
    ("and is the next one handed out for that size", again == a),
    ("freeing a block twice stops the machine", twice),
    ("a large block records its class", state.memory (large - 16) == some 257),
    ("asking for more than there is ends in out of memory", tooMuch),
    ("300 requests and frees: no two blocks in use overlap", apart)]

def main : IO UInt32 := do
  match scenario with
  | .error why =>
    IO.println s!"FAIL  the allocator failed as the language defines it: {why}"
    return 1
  | .ok checks =>
    let mut failures := 0
    for (name, held) in checks do
      IO.println s!"{if held then "ok   " else "FAIL "} {name}"
      if !held then failures := failures + 1
    if failures == 0 then IO.println "mini-test: all checks passed" else IO.println s!"mini-test: {failures} failed"
    return (if failures == 0 then 0 else 1)
