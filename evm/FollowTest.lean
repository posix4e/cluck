import Evm.Follow

/-! `Evm/Follow.lean` on saved blocks of the real chain, each with the node's own witness.

    .lake/build/bin/follow-test BLOCK.req...        consecutive blocks, as `witness/fetch` writes them

A block's witness holds proofs, at the state before it, of every account the block reads. So for three
blocks in a row A, B, C: B's witness holds proofs at A's state of what B reads, and C's witness holds
proofs at B's state of what C reads. The test takes the accounts B reads, with the slots of theirs that
B's witness proves something about, as if a transaction had brought proofs of them at A; has the machine
follow B; and requires that the proofs come out good at B's state: every way walkable from B's root
through the kept nodes alone, and, wherever C's witness also proves the same account or slot, the same
value there as C's witness has. Then on through C to the next block, and so on along the row. It counts
how many of the values changed on the way, so that it is known the walk was over ground that moved, and
checks that without the nodes a block wrote the proofs do not come through when anything changed. -/
open Jaune Evm

def request (path : String) : IO Stateless.Request := do
  let input ← IO.FS.readBinFile path
  match (Stateless.request (Stateless.magic ++ input.extract 5 input.size)).run 0 with
  | some (r, _) => pure r
  | none => throw (IO.userError s!"{path}: not a request")

/-- What a store proves is at an account and at each of the slots named, from a root: nothing when it
cannot be walked. -/
def values (store : Trie.Store) (root : U256) (address : ByteArray) (slots : Array ByteArray) :
    Option (Option ByteArray × Array (Option ByteArray)) := do
  let (_, leaf) ← (Trie.trail store (.sealed root) (Bridge.pathOf address)).toOption
  match leaf with
  | none => pure (none, #[])
  | some bytes =>
    let account ← Stateless.Leaf.read bytes
    let found ← slots.mapM fun slot => do
      let (_, value) ← (Trie.trail store (.sealed account.storageRoot) (Bridge.pathOf slot)).toOption
      pure value
    pure (some bytes, found)

def main (args : List String) : IO UInt32 := do
  if args.length < 3 then IO.eprintln "usage: follow-test BLOCK.req BLOCK.req BLOCK.req..."; return 2
  let mut failures := 0
  let mut chain : Follow.Chain := {}
  let mut pool : Seal.Pool := {}
  let mut held : Option Seal.Proofs := none
  let mut previous : Option Stateless.Request := none
  let mut moved := 0
  let mut compared := 0
  let mut carried := 0
  for path in args do
    let r ← request path
    let input ← IO.FS.readBinFile path
    let before := chain.head?
    -- What was held at the block before, checked against this block's witness, which is at that state.
    if let (some proofs, some head) := (held, before) then
      let theirs := Trie.Store.ofNodes r.nodes
      let mine := Trie.Store.ofNodes proofs.nodes
      for (address, slots) in proofs.accounts do
        match values mine head.root address slots with
        | none =>
          failures := failures + 1
          IO.println s!"{path}: a kept proof cannot be walked from the kept nodes alone"
        | some (account, found) =>
          if let some (theirAccount, theirSlots) := values theirs head.root address #[] then
            compared := compared + 1
            if theirAccount != account then
              failures := failures + 1
              IO.println s!"{path}: a kept proof gives another account than the block's witness"
            let _ := theirSlots
          for (slot, value) in slots.zip found do
            if let some (_, theirs) := values theirs head.root address #[slot] then
              compared := compared + 1
              if theirs[0]? != some value then
                failures := failures + 1
                IO.println s!"{path}: a kept proof gives another slot than the block's witness"
    -- The machine follows the block.
    let t0 ← IO.monoMsNow
    let (answer, next, _) := Follow.serve chain pool (Follow.magic ++ input.extract 5 input.size)
    let t1 ← IO.monoMsNow
    if answer[0]! != 0 then
      failures := failures + 1
      IO.println s!"{path}: not followed, status {answer[0]!}"
      continue
    let some head := next.head? | continue
    -- The proofs held are brought to it; and without what the block wrote, they are not, if anything moved.
    if let (some proofs, some old) := (held, before) then
      let written := Trie.Store.ofNodes head.written
      match Follow.forward proofs written head.root with
      | none =>
        failures := failures + 1
        IO.println s!"{path}: the proofs could not be brought to this block"
        held := none
      | some brought =>
        carried := carried + 1
        let oldStore := Trie.Store.ofNodes proofs.nodes
        let newStore := Trie.Store.ofNodes brought.nodes
        let changed := (proofs.accounts.filter fun (address, slots) =>
          values oldStore old.root address slots != values newStore head.root address slots).size
        moved := moved + changed
        if changed > 0 && (Follow.forward proofs .empty head.root).isSome then
          failures := failures + 1
          IO.println s!"{path}: proofs came through a block that changed what they prove, without what it wrote"
        held := some brought
    -- New proofs to carry, from this block's witness: they are at the state before it, so they are
    -- taken up for the next round by being brought through this very block.
    let store := Trie.Store.ofNodes r.nodes
    let parentRoot := match r.headers.getLast?.bind Stateless.header with | some h => h.stateRoot | none => 0
    let addresses := r.keys.filter (·.size == 20)
    let slotKeys := (r.keys.filter (·.size == 32)).toArray
    let accounts : Array (ByteArray × Array ByteArray) := addresses.toArray.map fun address =>
      -- The slots this account's storage has something proven for, among all the slot numbers named.
      let slots := match (Trie.trail store (.sealed parentRoot) (Bridge.pathOf address)).toOption with
        | some (_, some bytes) =>
          match Stateless.Leaf.read bytes with
          | some account =>
            if account.storageRoot == Trie.emptyRoot then #[] else
            slotKeys.filter fun slot =>
              match Trie.trail store (.sealed account.storageRoot) (Bridge.pathOf slot) with
              | .ok (_, some _) => true
              | _ => false
          | none => #[]
        | _ => #[]
      (address, slots)
    let fresh : Seal.Proofs := { root := Trie.wordBytes parentRoot, accounts, nodes := r.nodes, codes := #[] }
    let t2 ← IO.monoMsNow
    match (Follow.forward fresh .empty parentRoot).bind fun atParent =>
        (Follow.forward atParent (Trie.Store.ofNodes head.written) head.root).map fun atHead => (atParent, atHead) with
    | none =>
      failures := failures + 1
      IO.println s!"{path}: this block's own witness could not be made into proofs and brought through it"
    | some (atParent, atHead) =>
      let t3 ← IO.monoMsNow
      let slots := accounts.foldl (fun n a => n + a.2.size) 0
      IO.println s!"{path}: block {head.number} followed in {t1 - t0} ms, {head.written.size} nodes written; \
        proofs of {accounts.size} accounts and {slots} slots: {atParent.nodes.size} nodes of the witness's {r.nodes.size}, \
        brought through the block in {t3 - t2} ms"
      held := some atHead
    chain := next
    previous := some r
  IO.println s!"{carried} sets of proofs carried across a block; {compared} accounts and slots compared with the next block's own witness; \
    {moved} accounts changed on the way"
  if failures == 0 && carried > 0 && compared > 0 && moved > 0 then IO.println "follow-test: all checks passed"; return 0
  IO.println s!"follow-test: {failures} FAILED"
  return 1
