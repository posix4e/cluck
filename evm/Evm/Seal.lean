import Tls.Hpke
import Tls.Wire

/-! Transactions only this machine can read: sealed to a key it draws when it starts, handed in through
whoever carries its packets, and kept here until they are built into a block or their time is up.

## The key

    "JSEK1"

is answered with the machine's public key for sealing, 32 bytes: an X25519 key, drawn from the
platform's randomness when the machine starts, kept in its memory and nowhere else, and gone when it
stops. Asked for with a report (`Evm/Attest.lean`), the answer is tied to the machine's measurements,
which is how someone outside knows that only an image they have read holds the other half.

## A sealed transaction

    "JSEA1"
    32   the sender's public half, made for this one message
    then the message, sealed

is HPKE (RFC 9180, `Tls/Hpke.lean`: X25519, HKDF-SHA-256, ChaCha20-Poly1305, base mode) to that key, with
`info` the words "sealed transaction v1" and no data beside the message. What is sealed is

    8    the last slot the transaction may go in a block for
    then a transaction, as it goes on the wire

and the answer is one byte: 0 kept, 1 it does not open, 2 it opens to nothing that could be a
transaction, 3 no room. Nothing about the transaction is said: whoever handed it in learns only whether
it was kept.

## What is kept, and for how long

At most `maxKept` transactions and `maxBytes` bytes together, in memory. A transaction is tried in every
block built to be sent (`Evm/Send.lean`) for a slot up to the one it names, and is dropped when a block
is asked for a later slot. It is not dropped for having gone into a block: the machine does not know
whether its block was the one the chain took, and a transaction already in the chain fails on its own
the next time, because its number has been used.

The slot is the sender's protection against a carrier that keeps a transaction back and has it built
in when that suits the carrier: after the slot named it will not go into anything. Before it, when it
goes in is still up to whoever asks for blocks.

## With proofs

    "JSEA2"
    32   the sender's public half
    then the message, sealed, with `info` the words "sealed transaction with proofs v1"

carries with the transaction the proofs of the state it reads (`withProofs?` has the layout): the sender
knows what its own transaction touches and can ask any node for the proofs, and then nobody has to be
asked on the transaction's behalf. The proofs are at a block the sender names, which must be one of the
last few this machine has itself checked (`Evm/Follow.lean`); from then on the machine keeps them good,
block by block, from what each block it checks wrote. The answer is one byte as above, with 4 for proofs
at a block this machine does not know, or that do not reach what they say they prove.

## What this does not hide

The machine has no state of the chain; whoever asks it for a block supplies proofs of the state the
block's transactions read. For a transaction sealed without proofs the machine must therefore say which
accounts and slots it lacks (`Evm/Send.lean`), and whoever supplies them learns that much of what the
transaction touches. One sealed with its proofs asks nobody for anything: if what it brought does not
cover what it reads, it is left out and nothing is said. Its amounts, its call data and what it does are
not said either way. The length of the sealed message is the length of what was sealed, give or take,
and with proofs that grows with how much state the transaction reads. -/

namespace Evm.Seal

def keyMagic : ByteArray := "JSEK1".toUTF8
def magic : ByteArray := "JSEA1".toUTF8

def info : ByteArray := "sealed transaction v1".toUTF8

/-- The most transactions kept, and the most bytes of them together. -/
def maxKept : Nat := 64
def maxBytes : Nat := 512 * 1024

/-- The machine's key for sealing: the private half and the public half. -/
structure Key where
  secret : ByteArray
  publicKey : ByteArray

def Key.of (secret : ByteArray) : Key := ⟨secret, Tls.X25519.publicKey secret⟩

/-- A key everyone knows, for tests and for the service run as a process. Never one a machine holds. -/
def testKey : Key := Key.of (Tls.Sha256.hash "a sealing key for tests, known to everyone".toUTF8)

/-- Proofs of the state a transaction reads, which its sender brought with it: the accounts and the slots
of their storage it names, the nodes of the state's tries that lead to them from a state root, and the
codes of the contracts among them. -/
structure Proofs where
  /-- The state root the nodes lead from, 32 bytes. -/
  root : ByteArray
  /-- Each account's address, 20 bytes, and the numbers of its slots, 32 bytes each. -/
  accounts : Array (ByteArray × Array ByteArray)
  nodes : Array ByteArray
  codes : Array ByteArray

def Proofs.bytes (p : Proofs) : Nat :=
  p.nodes.foldl (fun n b => n + b.size) (p.codes.foldl (fun n b => n + b.size) (p.accounts.foldl (fun n a => n + 20 + 32 * a.2.size) 0))

/-- A transaction that was sealed to this machine, opened. -/
structure Kept where
  /-- The last slot it may go in a block for. -/
  last : Nat
  /-- The transaction as it goes on the wire. -/
  wire : ByteArray
  /-- The proofs its sender brought, if any, kept good at the newest block this machine has checked. -/
  proofs : Option Proofs := none

/-- The transactions kept. -/
structure Pool where
  kept : Array Kept := #[]

def Pool.bytes (p : Pool) : Nat := p.kept.foldl (fun n k => n + k.wire.size + (k.proofs.map (·.bytes)).getD 0) 0

def mine (input : ByteArray) : Bool :=
  input == keyMagic || (input.size ≥ magic.size && input.extract 0 magic.size == magic)

/-- A sealed transaction handed in: the pool after it, and the byte that answers. -/
def handIn (key : Key) (pool : Pool) (input : ByteArray) : Pool × UInt8 :=
  if input.size < magic.size + 32 + 16 then (pool, 1) else
  let enc := input.extract magic.size (magic.size + 32)
  match Tls.Hpke.open? key.secret key.publicKey enc info .empty (input.extract (magic.size + 32) input.size) with
  | none => (pool, 1)
  | some plain =>
    if plain.size < 8 + 1 then (pool, 2) else
    let last := (plain.extract 0 8).foldl (fun n b => n * 256 + b.toNat) 0
    let wire := plain.extract 8 plain.size
    if pool.kept.size ≥ maxKept || pool.bytes + wire.size > maxBytes then (pool, 3)
    else ({ kept := pool.kept.push { last, wire } }, 0)

/-- The same with proofs: a second request, sealed under other words so that neither kind opens as the
other. See "With proofs" below. -/
def magic2 : ByteArray := "JSEA2".toUTF8
def info2 : ByteArray := "sealed transaction with proofs v1".toUTF8

def withProofs (input : ByteArray) : Bool := input.size ≥ magic2.size && input.extract 0 magic2.size == magic2

/-- The most a sealed transaction with its proofs may be, opened. -/
def maxOpened : Nat := 256 * 1024

/-- What a transaction sealed with proofs opens to: the last slot, the transaction, the hash of the block
the proofs are at, and the proofs with no root named yet (the machine knows that block's, or does not know
the block). Laid out as

    8    the last slot
    4    a length, then the transaction
    32   the hash of the block the proofs are at
    2    how many accounts, then for each: 20 its address, 2 how many slots, then 32 each
    4    how many nodes, then each with 2 bytes of length before it
    2    how many codes, then each with 4 bytes of length before it

Nothing when the bytes are not that. -/
def withProofs? (plain : ByteArray) : Option (Kept × ByteArray) := do
  let cur := Tls.Cursor.of plain
  let (last, cur) ← cur.number 8
  let (wire, cur) ← cur.framed 4
  let (anchor, cur) ← cur.take 32
  let (count, cur) ← cur.number 2
  let mut cur := cur
  let mut accounts : Array (ByteArray × Array ByteArray) := #[]
  for _ in [0:count] do
    let (address, next) ← cur.take 20
    let (slots, next) ← next.number 2
    let mut next := next
    let mut keys : Array ByteArray := #[]
    for _ in [0:slots] do
      let (key, after) ← next.take 32
      keys := keys.push key
      next := after
    accounts := accounts.push (address, keys)
    cur := next
  let (count, next) ← cur.number 4
  cur := next
  let mut nodes : Array ByteArray := #[]
  for _ in [0:count] do
    let (node, next) ← cur.framed 2
    nodes := nodes.push node
    cur := next
  let (count, next) ← cur.number 2
  cur := next
  let mut codes : Array ByteArray := #[]
  for _ in [0:count] do
    let (code, next) ← cur.framed 4
    codes := codes.push code
    cur := next
  if !cur.done || wire.isEmpty then none
  pure ({ last, wire, proofs := some { root := .empty, accounts, nodes, codes } }, anchor)

/-- A transaction sealed with proofs, opened: 1 for one that does not open, 2 for one that opens to
something else. Whether its proofs are any good is for whoever knows the chain (`Evm/Follow.lean`). -/
def openWithProofs (key : Key) (input : ByteArray) : Except UInt8 (Kept × ByteArray) :=
  if input.size < magic2.size + 32 + 16 then .error 1 else
  let enc := input.extract magic2.size (magic2.size + 32)
  match Tls.Hpke.open? key.secret key.publicKey enc info2 .empty (input.extract (magic2.size + 32) input.size) with
  | none => .error 1
  | some plain =>
    if plain.size > maxOpened then .error 2 else
    match withProofs? plain with
    | some found => .ok found
    | none => .error 2

/-- The transactions to try in a block for `slot`, and the pool without those whose time is up. -/
def Pool.forSlot (p : Pool) (slot : Nat) : Pool × Array ByteArray :=
  let kept := p.kept.filter (·.last ≥ slot)
  ({ kept }, kept.map (·.wire))

/-- The answer to either request here, and the pool after it. -/
def serve (key : Key) (pool : Pool) (input : ByteArray) : Pool × ByteArray :=
  if input == keyMagic then (pool, key.publicKey)
  else
    let (pool, status) := handIn key pool input
    (pool, ByteArray.mk #[status])

end Evm.Seal
