import Tls.Hpke

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

## What this does not hide

The machine has no state of the chain; whoever asks it for a block supplies proofs of the state the
block's transactions read. For a sealed transaction the machine must therefore say which accounts and
slots it lacks (`Evm/Send.lean`), and whoever supplies them learns that much of what the transaction
touches. Its amounts, its call data and what it does are not said. The length of the sealed message is
the length of the transaction, give or take. -/

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

/-- A transaction that was sealed to this machine, opened. -/
structure Kept where
  /-- The last slot it may go in a block for. -/
  last : Nat
  /-- The transaction as it goes on the wire. -/
  wire : ByteArray

/-- The transactions kept. -/
structure Pool where
  kept : Array Kept := #[]

def Pool.bytes (p : Pool) : Nat := p.kept.foldl (fun n k => n + k.wire.size) 0

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
