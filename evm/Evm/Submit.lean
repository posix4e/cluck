import Fast.Bytes

/-! A block and the bid for it, as a relay takes them: the builder API's request to submit a block, in SSZ,
for the fork mainnet is on (Fulu).

The pieces are all here already when a block has been built for a bid: the header that was built, as RLP;
the block the request proposed, whose transactions and withdrawals these are; which of the transactions
went in; what the block asks of the consensus layer; and the bid with its signature. This puts them in
the order and the encoding a relay reads, so that the machine that built the block can hand it over
itself, and nobody in between has to be shown it to put it together. No JSON is read or written.

The layout is `SubmitBlockRequest` of the builder API as go-builder-client has it for Fulu (the bid, the
execution payload of Deneb, a bundle of blobs, the execution requests of Electra, the signature), read
from that library's source on 2026-11-21. No block built here carries blobs, so the bundle is empty.
The stand-in relay (`builder/standin-relay`) takes it apart again, and `builder/shadow --guest-sends` lays
what it found beside the same block put together on the host, the way blocks sent to real relays have
been until now. That decoder is by the same hand as this, written from the same reading of the layout; it
is not a relay's own, and until a relay has taken one of these that is what has not been shown. -/

namespace Evm.Submit

/-- A number in `width` bytes, lowest first, as SSZ writes numbers. -/
def little (width n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range width).map fun i => (n >>> (8 * i)).toUInt8)

/-- A number from bytes, highest first, as RLP writes numbers. -/
def big (b : ByteArray) : Nat := b.foldl (fun n x => n * 256 + x.toNat) 0

/-- One item of RLP: whether it is a list, where it begins with its heading, and where what it holds
lies. -/
structure Item where
  list : Bool
  first : Nat
  start : Nat
  stop : Nat
  deriving Inhabited

/-- The item at `pos`, which must end by `limit`. -/
def item? (b : @& ByteArray) (pos limit : Nat) : Option Item :=
  if pos ≥ limit || limit > b.size then none else
  let p := (Fast.byte b pos).toNat
  let sized (list : Bool) (start size : Nat) : Option Item :=
    if start + size > limit then none else some ⟨list, pos, start, start + size⟩
  let long (list : Bool) (count : Nat) : Option Item :=
    if pos + 1 + count > limit then none
    else sized list (pos + 1 + count) (big (b.extract (pos + 1) (pos + 1 + count)))
  if p < 0x80 then sized false pos 1
  else if p ≤ 0xb7 then sized false (pos + 1) (p - 0x80)
  else if p ≤ 0xbf then long false (p - 0xb7)
  else if p ≤ 0xf7 then sized true (pos + 1) (p - 0xc0)
  else long true (p - 0xf7)

/-- The items a list holds, end to end. -/
def items? (b : @& ByteArray) (list : Item) : Option (Array Item) :=
  go b list.stop (list.stop - list.start + 1) list.start #[]
where
  go (b : @& ByteArray) (stop : Nat) : Nat → Nat → Array Item → Option (Array Item)
    | 0, _, _ => none
    | fuel + 1, pos, found =>
      if pos == stop then some found
      else match item? b pos stop with
        | none => none
        | some item => go b stop fuel item.stop (found.push item)

/-- What an item that is not a list holds. -/
def bytes (b : @& ByteArray) (item : Item) : ByteArray := b.extract item.start item.stop

/-- The heading RLP puts before `size` bytes, of a list or not. -/
def heading (list : Bool) (size : Nat) : ByteArray :=
  let short : Nat := if list then 0xc0 else 0x80
  if size ≤ 55 then ByteArray.mk #[(short + size).toUInt8]
  else
    let digits := ByteArray.mk ((List.range ((size.log2 / 8) + 1)).reverse.map fun i => (size >>> (8 * i)).toUInt8).toArray
    ByteArray.mk #[(short + 55 + digits.size).toUInt8] ++ digits

/-- How many transactions a block proposes. -/
def proposed? (block : @& ByteArray) : Option Nat := do
  let parts ← items? block (← item? block 0 block.size)
  pure (← items? block (← parts[1]?)).size

/-- A transaction as it stands in a block's list: one of the old kind is its own RLP; any other is its
bytes, as a string. -/
def listed (wire : ByteArray) : ByteArray :=
  if wire.size > 0 && wire[0]! ≥ 0xc0 then wire
  else if wire.size == 1 && wire[0]! < 0x80 then wire
  else heading false wire.size ++ wire

/-- A block with more transactions proposed after those it has: the same RLP with `more`, each as it
goes on the wire, added to the end of its list of transactions. -/
def withMore? (block : @& ByteArray) (more : Array ByteArray) : Option ByteArray := do
  let whole ← item? block 0 block.size
  let parts ← items? block whole
  let list ← parts[1]?
  if !list.list || whole.stop != block.size then none
  let transactions := more.foldl (fun out wire => out ++ listed wire) (block.extract list.start list.stop)
  let body := block.extract whole.start list.first ++ heading true transactions.size ++ transactions
    ++ block.extract list.stop whole.stop
  pure (heading true body.size ++ body)

/-- What goes into a submission. -/
structure Parts where
  slot : Nat
  builderKey : ByteArray
  proposerKey : ByteArray
  /-- What the block pays the proposer, in wei. -/
  value : Nat
  blockHash : ByteArray
  /-- The header that was built, as RLP. -/
  header : ByteArray
  /-- The block the request proposed, as RLP: a header, transactions, ommers, withdrawals. -/
  block : ByteArray
  /-- Which of the proposed transactions went in, in the block's order. -/
  places : List Nat
  /-- What the block asks of the consensus layer: each a byte for its kind, then its data. -/
  requests : List ByteArray
  signature : ByteArray

/-- A list of things of different lengths, as SSZ writes one: where each begins, then each. -/
def uneven (items : Array ByteArray) : ByteArray :=
  let (offsets, _) := items.foldl (fun (out, at_) item => (out ++ little 4 at_, at_ + item.size)) (ByteArray.empty, 4 * items.size)
  items.foldl (· ++ ·) offsets

/-- A container's fixed part and the parts of varying length after it: `fields` in order, each either
bytes that go where they stand or a part that goes after, with where it begins written in its place. -/
def container (fields : Array (Bool × ByteArray)) : ByteArray :=
  let fixed := fields.foldl (fun n (later, part) => n + (if later then 4 else part.size)) 0
  let (head, tail) := fields.foldl (fun (head, tail) (later, part) =>
    if later then (head ++ little 4 (fixed + tail.size), tail ++ part) else (head ++ part, tail)) (ByteArray.empty, ByteArray.empty)
  head ++ tail

/-- The request to submit a block, or nothing when the pieces are not what they should be. -/
def submission (p : Parts) : Option ByteArray := do
  let header ← items? p.header (← item? p.header 0 p.header.size)
  -- A header since Cancun: 20 fields at the least, in the order every client has them.
  if header.size < 20 then none
  let field (i : Nat) : ByteArray := bytes p.header header[i]!
  let number (i : Nat) : ByteArray := little 8 (big (field i))
  let parts ← items? p.block (← item? p.block 0 p.block.size)
  if parts.size < 4 then none
  let proposed ← items? p.block parts[1]!
  -- A transaction as it goes on the wire: one of the old kind is its RLP whole; any other is the bytes
  -- its item holds, which begin with its kind.
  let transactions ← p.places.toArray.mapM fun place => do
    let item ← proposed[place]?
    pure (if item.list then p.block.extract item.first item.stop else bytes p.block item)
  let withdrawals ← (← items? p.block parts[3]!).mapM fun item => do
    let w ← items? p.block item
    if w.size != 4 || (bytes p.block w[2]!).size != 20 then none
    pure (little 8 (big (bytes p.block w[0]!)) ++ little 8 (big (bytes p.block w[1]!)) ++ bytes p.block w[2]!
      ++ little 8 (big (bytes p.block w[3]!)))
  if (field 0).size != 32 || (field 2).size != 20 || (field 3).size != 32 || (field 5).size != 32 || (field 6).size != 256
      || (field 13).size != 32 || (field 12).size > 32 || p.blockHash.size != 32 || p.builderKey.size != 48
      || p.proposerKey.size != 48 || p.signature.size != 96 then none
  let trace := little 8 p.slot ++ field 0 ++ p.blockHash ++ p.builderKey ++ p.proposerKey ++ field 2
    ++ number 9 ++ number 10 ++ little 32 p.value
  let payload := container #[
    (false, field 0 ++ field 2 ++ field 3 ++ field 5 ++ field 6 ++ field 13 ++ number 8 ++ number 9 ++ number 10 ++ number 11),
    (true, field 12),
    (false, little 32 (big (field 15)) ++ p.blockHash),
    (true, uneven transactions),
    (true, withdrawals.foldl (· ++ ·) ByteArray.empty),
    (false, number 17 ++ number 18)]
  let asked (kind : UInt8) : ByteArray :=
    p.requests.foldl (fun out r => if r.size > 0 && r[0]! == kind then out ++ r.extract 1 r.size else out) ByteArray.empty
  let requests := container #[(true, asked 0), (true, asked 1), (true, asked 2)]
  let blobs := container #[(true, .empty), (true, .empty), (true, .empty)]
  pure (container #[(false, trace), (true, payload), (true, blobs), (true, requests), (false, p.signature)])

end Evm.Submit
