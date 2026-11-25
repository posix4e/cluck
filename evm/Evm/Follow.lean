import Evm.Engine
import Evm.Seal
import Evm.Bid

/-! The machine following the chain, so that a sealed transaction can bring its own proofs and nobody has to
be asked what it reads.

The machine holds no state. To build a block it is given proofs of the state the block's transactions
read, by whoever asks for the block, and for a transaction that sender has not seen there is nobody to
know what to prove but the machine, which then has to say (`Evm/Send.lean`), and saying it tells the
sender which accounts and slots the hidden transaction touches.

The way out taken here: the transaction's own sender brings the proofs, sealed with it (`Evm/Seal.lean`,
"With proofs"). A proof is good at one block, and the chain moves on every twelve seconds, so somebody
has to keep it good. The machine does, without asking anything about any account: it is shown each new
block with that block's own witness, which is a public thing and the same whoever asks, checks the block
with the fast engine as it would any block (`Evm/Engine.lean`), and keeps the nodes the block wrote to the
state's tries. A proof of an account before the block, together with every node the block wrote, holds a
proof of the account after it: the way from the new root is made of nodes the block wrote and nodes that
were on the old way. So each kept proof is walked again from each new root and stays good, and holds no
more than the nodes on its own ways.

## The request

    "JFOL1", then everything a stateless request has after its own five bytes (`Evm/Stateless.lean`)

is answered as a block judged by the fast engine is (`Evm/Engine.lean`), and if the block is valid the
machine takes it for the newest it knows. When it carries on from the last one, the kept proofs are
brought to it. When it does not (the first block shown, a gap, a block replaced), the proofs kept are
for a chain the machine is no longer on, and the transactions that brought them are dropped.

## What is and is not trusted

The machine checks that each block follows by the EVM's rules from the state root in its parent's
header. It does not check that the chain is the one validators agreed on: it has no view of that, here
or anywhere. So whoever feeds it blocks can show it a chain of their own making, as long as every block
on it is valid. On such a chain a sealed transaction might be built into a block nobody will take, or
left out; `THREAT_MODEL.md` says what can be learned that way. -/

open Jaune

namespace Evm.Follow

def magic : ByteArray := "JFOL1".toUTF8

def mine (input : ByteArray) : Bool := input.size ≥ magic.size && input.extract 0 magic.size == magic

/-- A block this machine checked: its hash and number, the state root after it, and the nodes it wrote. -/
structure Seen where
  hash : U256
  number : Nat
  root : U256
  written : Array ByteArray

/-- The last few blocks checked, oldest first, each the parent of the next. -/
structure Chain where
  recent : Array Seen := #[]

/-- How many are kept: a sender's proofs may be at either, the newest block or the one before it. Each
kept block is some megabytes of the nodes it wrote, and memory is what following the chain is short of
(`scripts/follow-memory`). -/
def maxRecent : Nat := 2

def Chain.head? (c : Chain) : Option Seen := c.recent.back?

/-- A checked block added. Whether it carried on from the newest known; when it did not, it is the only
one known now. -/
def Chain.add (c : Chain) (parent : U256) (block : Seen) : Chain × Bool :=
  match c.head? with
  | some head =>
    if head.hash == block.hash then (c, true)
    else if head.hash == parent then
      let recent := c.recent.push block
      ({ recent := recent.extract (recent.size - min recent.size maxRecent) recent.size }, true)
    else ({ recent := #[block] }, false)
  | none => ({ recent := #[block] }, false)

/-- Proofs brought to a later state root: every account and slot they name is walked to from `root`
through the proofs' own nodes and `written`, the nodes written since they were good, and the nodes on
those ways are the proofs now. Nothing when a way cannot be walked: the proofs were short, or not at the
root they were said to be at. -/
def forward (proofs : Seal.Proofs) (written : Trie.Store) (root : U256) : Option Seal.Proofs := do
  let store := proofs.nodes.foldl (fun store node => store.insert (Trie.hashOf node) node) written
  let mut nodes : Array ByteArray := #[]
  for (address, slots) in proofs.accounts do
    let (way, leaf) ← (Trie.trail store (.sealed root) (Bridge.pathOf address)).toOption
    nodes := nodes ++ way
    if let some bytes := leaf then
      let account ← Stateless.Leaf.read bytes
      for slot in slots do
        let (way, _) ← (Trie.trail store (.sealed account.storageRoot) (Bridge.pathOf slot)).toOption
        nodes := nodes ++ way
  -- Each node once: ways share their upper parts.
  let unique := (Trie.Store.ofNodes nodes).foldl (fun out _ node => out.push node) #[]
  pure { proofs with root := Trie.wordBytes root, nodes := unique }

/-- The kept transactions after a block was checked: those with proofs have them brought to it, or are
dropped when that cannot be done, and all of them when the block did not carry on from the last. -/
def advance (pool : Seal.Pool) (block : Seen) (carried : Bool) : Seal.Pool :=
  if pool.kept.all (·.proofs.isNone) then pool else
  let written := Trie.Store.ofNodes block.written
  { kept := pool.kept.filterMap fun kept =>
      match kept.proofs with
      | none => some kept
      | some proofs =>
        if !carried then none
        else (forward proofs written block.root).map fun proofs => { kept with proofs := some proofs } }

/-- A block shown to the machine: the answer, and the chain and the pool after it. -/
def serve (chain : Chain) (pool : Seal.Pool) (input : ByteArray) : ByteArray × Chain × Seal.Pool :=
  let refuse : ByteArray × Chain × Seal.Pool := ((⟨5, 0, 0, 0⟩ : Service.Response).encode, chain, pool)
  match (Stateless.body input).run magic.size with
  | none => refuse
  | some (r, pos) =>
    if pos != input.size then refuse else
    let (response, _, kept) := Stateless.runWithBy (Engine.validateWith true) r
    match kept with
    | none => (response.encode, chain, pool)
    | some (block, hash, written) =>
      let seen : Seen := { hash, number := block.header.number, root := block.header.stateRoot, written }
      let (chain, carried) := chain.add block.header.parentHash seen
      (response.encode, chain, advance pool seen carried)

/-- A transaction sealed with proofs, handed in (`Evm/Seal.lean`): the pool after it and the byte that
answers. The proofs must be at one of the blocks known here, and are brought from there to the newest
before they are kept; that walk is also what shows they reach what they name. -/
def handIn (key : Seal.Key) (pool : Seal.Pool) (chain : Chain) (input : ByteArray) : Seal.Pool × UInt8 :=
  match Seal.openWithProofs key input with
  | .error status => (pool, status)
  | .ok (kept, anchor) =>
    match kept.proofs, chain.recent.findIdx? (fun seen => Trie.wordBytes seen.hash == anchor),
        chain.recent.find? (fun seen => Trie.wordBytes seen.hash == anchor) with
    | some proofs, some at_, some start =>
      -- From the block they are at, through each block after it, to the newest.
      let brought := (chain.recent.extract (at_ + 1) chain.recent.size).foldl (fun proofs (seen : Seen) =>
        proofs.bind fun proofs => forward proofs (Trie.Store.ofNodes seen.written) seen.root)
        (forward proofs .empty start.root)
      match brought with
      | none => (pool, 4)
      | some proofs =>
        let kept := { kept with proofs := some proofs }
        if pool.kept.size ≥ Seal.maxKept || pool.bytes + kept.wire.size + proofs.bytes > Seal.maxBytes then (pool, 3)
        else ({ kept := pool.kept.push kept }, 0)
    | _, _, _ => (pool, 4)

/-- What a block built on `parent` (a block's hash) may try of the kept transactions good for `slot`:
those without proofs, whose lacks are said; and, only when `parent` is the newest block known here, those
with proofs, with the proofs. -/
def extra (pool : Seal.Pool) (chain : Chain) (slot : Nat) (parent : ByteArray) : Bid.Extra :=
  let good := pool.kept.filter (·.good slot)
  let bare := good.filter (·.proofs.isNone)
  let atHead := chain.head?.any fun head => Trie.wordBytes head.hash == parent
  let proven := if atHead then good.filter (·.proofs.isSome) else #[]
  { wires := bare.map (·.wire) ++ proven.map (·.wire)
    loud := bare.size
    nodes := proven.flatMap fun kept => (kept.proofs.map (·.nodes)).getD #[]
    codes := proven.flatMap fun kept => (kept.proofs.map (·.codes)).getD #[] }

end Evm.Follow
