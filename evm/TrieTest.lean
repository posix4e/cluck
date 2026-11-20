import Evm

/-! Tests of `Evm.Trie` against Jaune's own root computation, which hashes a whole map from nothing. After
every change to a trie built up and cut down one key at a time, the two roots must agree; the same changes
made through a witness, starting from nothing but the root hash, must agree too; and a witness that lacks a
node must be reported as lacking it. Run on Lean's own runtime. -/
open Jaune Evm.Trie

abbrev Model := TrieBuilder

structure Rng where
  state : UInt64

def Rng.next (r : Rng) : Rng × Nat :=
  let s := r.state * 6364136223846793005 + 1442695040888963407
  (⟨s⟩, (s >>> 33).toNat)

def hex (bytes : ByteArray) : String :=
  bytes.foldl (fun out b => out ++ String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]) ""

def unhex (text : String) : ByteArray := Id.run do
  let digit (c : Char) : UInt8 := (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt8
  let cs := text.toList.toArray
  let mut out := ByteArray.empty
  for i in [0 : cs.size / 2] do out := out.push ((digit cs[2 * i]!) <<< 4 ||| digit cs[2 * i + 1]!)
  return out

def describe : Except Evm.Trie.Fault α → String
  | .ok _ => "an answer"
  | .error (.missing _) => "missing"
  | .error (.malformed _) => "malformed"
  | .error .shape => "shape"

/-- One family of tries: keys of `length` nibbles drawn from the first `alphabet` nibble values, values of
up to `longest` bytes. A small alphabet makes long shared prefixes; short values make embedded nodes. -/
structure Family where
  length : Nat
  alphabet : Nat
  longest : Nat
  keys : Nat
  steps : Nat

def families : List Family :=
  [⟨4, 16, 3, 60, 700⟩, ⟨6, 2, 40, 40, 700⟩, ⟨64, 16, 40, 50, 500⟩, ⟨64, 2, 2, 50, 500⟩, ⟨2, 16, 1, 200, 900⟩]

def draw (r : Rng) (n : Nat) (below : Nat) : Rng × Array UInt8 := Id.run do
  let mut r := r
  let mut out := #[]
  for _ in [0 : n] do
    let (r', x) := r.next
    r := r'
    out := out.push (x % below).toUInt8
  return (r, out)

def run (family : Family) (seed : Nat) : IO Nat := do
  let mut failures := 0
  let mut r : Rng := ⟨seed.toUInt64⟩
  -- The keys there are to choose among, so that writes meet earlier writes and removals find something.
  let mut pool : Array Path := #[]
  for _ in [0 : family.keys] do
    let (r', key) := draw r family.length family.alphabet
    r := r'
    pool := pool.push key
  let mut tree : Node := .empty
  let mut model : Model := .empty
  for step in [0 : family.steps] do
    let (r1, pick) := r.next
    let (r2, kind) := r1.next
    let (r3, size) := r2.next
    let (r4, bytes) := draw r3 (size % family.longest + 1) 256
    r := r4
    let key := pool[pick % pool.size]!
    let value : ByteArray := ⟨bytes⟩
    let removing := kind % 10 < 4
    let before := tree
    -- Every seventh step is also made through a witness: nothing known but the root's hash.
    if step % 7 == 0 then
      let store := Store.ofNodes (encodings before)
      let closed : Node := .sealed (rootHash before)
      let viaWitness := if removing then remove store closed key else put store closed key value
      let direct := if removing then remove .empty before key else put .empty before key value
      match viaWitness, direct with
      | .ok a, .ok b =>
        if rootHash a != rootHash b then
          failures := failures + 1
          IO.println s!"step {step}: through a witness the root differs"
      | a, b =>
        failures := failures + 1
        IO.println s!"step {step}: through a witness {describe a}, directly {describe b}"
      for other in pool do
        match get store closed other, get .empty before other with
        | .ok a, .ok b => if a != b then
            failures := failures + 1
            IO.println s!"step {step}: a read through a witness differs"
        | a, b =>
          failures := failures + 1
          IO.println s!"step {step}: a read through a witness is {describe a}, directly {describe b}"
    match if removing then remove .empty tree key else put .empty tree key value with
    | .error e =>
      failures := failures + 1
      IO.println s!"step {step}: {describe (Except.error e : Except Evm.Trie.Fault Unit)}"
    | .ok next => tree := next
    model := if removing then model.erase key.toList else model.insert key.toList value.toList
    if rootHash tree != trie model then
      failures := failures + 1
      IO.println s!"step {step}: root {rootHash tree}, Jaune's {trie model}, {model.size} keys"
    -- What was written reads back, and what is not there is proven not there.
    let expected := (model.get? key.toList).map (·.toByteArray)
    match get .empty tree key with
    | .ok found => if found != expected then
        failures := failures + 1
        IO.println s!"step {step}: a key does not read back"
    | .error _ =>
      failures := failures + 1
      IO.println s!"step {step}: a read of a whole trie failed"
    -- Every node of the trie must read back as itself: the reader accepts what the writer writes.
    if step % 50 == 0 then
      for bytes in encodings tree do
        match decode bytes with
        | some node => if encode node != bytes then
            failures := failures + 1
            IO.println s!"step {step}: a node read back writes differently"
        | none =>
          failures := failures + 1
          IO.println s!"step {step}: a node the trie wrote does not read: {hex bytes}"
  return failures

def expectFault (what : String) (wanted : String) (got : Except Evm.Trie.Fault α) : IO Nat := do
  if describe got == wanted then return 0
  IO.println s!"{what}: {describe got}, not {wanted}"
  return 1

def main : IO UInt32 := do
  let mut failures := 0
  if rootHash .empty != trie .empty then
    failures := failures + 1
    IO.println "the empty trie's root is not Jaune's"
  for family in families do
    for seed in [1, 2, 3] do
      failures := failures + (← run family seed)
    IO.println s!"keys of {family.length} nibbles from {family.alphabet}, values to {family.longest} bytes: \
      3 runs of {family.steps} changes"
  -- Two long leaves under one branch, and a witness that holds the branch and only one of them.
  let long (b : UInt8) : ByteArray := ⟨Array.replicate 40 b⟩
  let keyA : Path := #[1] ++ Array.replicate 63 5
  let keyB : Path := #[2] ++ Array.replicate 63 5
  let keyC : Path := #[3] ++ Array.replicate 63 5
  match (do put .empty (← put .empty .empty keyA (long 1)) keyB (long 2) : Except Evm.Trie.Fault Node) with
  | .error _ =>
    failures := failures + 1
    IO.println "two keys could not be written"
  | .ok two =>
    let all := encodings two
    let closed : Node := .sealed (rootHash two)
    let partialStore := Store.ofNodes (all.filter fun bytes =>
      (decode bytes).any fun node => match node with | .leaf _ v => v != long 2 | _ => true)
    failures := failures + (← expectFault "a key whose leaf is held" "an answer" (get partialStore closed keyA))
    failures := failures + (← expectFault "a key whose leaf is not held" "missing" (get partialStore closed keyB))
    failures := failures + (← expectFault "a key under an empty slot" "an answer" (get partialStore closed keyC))
    -- Removing A leaves B alone under the branch, and what replaces the branch depends on B, which is not held.
    failures := failures + (← expectFault "a removal that needs a node not held" "missing"
      (remove partialStore closed keyA))
    failures := failures + (← expectFault "a write beside a node not held" "an answer"
      (put partialStore closed keyC (long 3)))
    failures := failures + (← expectFault "a read with no witness at all" "missing" (get .empty closed keyA))
    let junk : ByteArray := ⟨Array.replicate 40 0xc1⟩
    failures := failures + (← expectFault "bytes that are not a node" "malformed"
      (get (Store.ofNodes #[junk]) (.sealed (hashOf junk)) keyA))
  -- Encodings a trie would never hold, each one change away from one it would.
  let leaf := encode (.leaf (Array.replicate 63 5) (long 1))
  let refs := (List.replicate 16 (rlpString (wordBytes (hashOf leaf)))).foldl (· ++ ·) ByteArray.empty
  let refused : List (String × ByteArray) :=
    [("a branch holding a value", rlpList (refs ++ rlpString (long 1))),
     ("a branch of fifteen", rlpList ((refs.extract 33 refs.size) ++ ⟨#[0x80]⟩)),
     ("a branch with one child", rlpList (rlpString (wordBytes (hashOf leaf)) ++ ⟨Array.replicate 16 0x80⟩)),
     ("a child named by 31 bytes", rlpList (rlpString ⟨Array.replicate 31 7⟩ ++ refs.extract 33 refs.size ++ ⟨#[0x80]⟩)),
     ("an embedded child of 32 bytes or more", rlpList (leaf ++ refs.extract 33 refs.size ++ ⟨#[0x80]⟩)),
     ("a leaf with no value", rlpList (rlpString (hexPrefix #[1, 2] true) ++ ⟨#[0x80]⟩)),
     ("an extension with no path", rlpList (rlpString (hexPrefix #[] false) ++ rlpString (wordBytes (hashOf leaf)))),
     ("a path of 65 nibbles", rlpList (rlpString (hexPrefix (Array.replicate 65 5) true) ++ rlpString (long 1))),
     ("an odd flag with a stray nibble", rlpList (rlpString ⟨#[0x05, 0x55]⟩ ++ rlpString (long 1))),
     ("a length written the long way", ⟨#[0xf8, 0x03, 0x20, 0x81, 0x90]⟩),
     ("a byte below 0x80 written as a string", rlpList (⟨#[0x81, 0x20]⟩ ++ rlpString (long 1))),
     ("bytes after the node", leaf.push 0),
     ("a string where a node should be", rlpString (long 1)),
     ("nothing", .empty)]
  for (what, bytes) in refused do
    if (decode bytes).isSome then
      failures := failures + 1
      IO.println s!"{what} was read as a node"
  if (decode leaf).isNone then
    failures := failures + 1
    IO.println "the leaf those are made from does not read"
  IO.println s!"refused encodings: {refused.length}"
  if failures == 0 then IO.println "trie-test: all checks passed" else IO.println s!"trie-test: {failures} FAILED"
  return if failures == 0 then 0 else 1
