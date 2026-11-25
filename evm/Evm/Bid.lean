import Evm.Build
import Evm.Sign
import Evm.Submit

/-! A bid: a block built here, and the builder's signature over what it offers the proposer for it.

A relay takes a block from a builder together with a signed statement of what the block is and what it
pays (the bid trace of the builder API: slot, parent hash, block hash, the builder's and the proposer's
keys, the proposer's fee recipient, gas limit, gas used, value). This is `Evm.Build` with that statement
made out and signed, by a key that is held where this runs and is never a `Nat` (`Evm/Sign.lean`).

## The requests

    "JBID2"
    8    the slot
    48   the proposer's public key
    4    the fork version the signature is for (the chain's genesis version: zeros for mainnet)
    4    milliseconds allowed for transactions, or 0 for as long as they take
    then a request to build, from its own "JBLD1" on (Evm/Build.lean)

is answered with the response to that request to build, and after it, if a block was built:

    48   this builder's public key
    96   its signature over the bid

The time allowed is for a builder that has a slot to meet: counted from when the request's first bytes
arrived (so that a request slow on the way in makes a smaller block and not a late one), and once it is up everything still proposed is left out and the block is ended with what is in
it, so the answer is a smaller block and not a late one. It is looked at between transactions, not within
one. Only a machine with a clock can count it (`EfiMain.lean`); run as a process there is none, and the
answer is the block with no limit.

    "JKEY1"

is answered with this builder's public key, 48 bytes.

## What gets signed

Only this: the bid for a block that was built here, in answer to the request that asked for it. Every
field of the bid is either worked out here (block hash, gas used, value: `Evm.Build`), read off the header
that was built (parent hash, fee recipient, gas limit), this builder's own key, or named by the sender and
signed as named (the slot, the proposer's key, the fork version). There is no request that signs a message
of the sender's choosing, so the key cannot be made to sign something that is not a bid; and the domain is
fixed to the builder's (`0x00000001`), so a bid cannot be passed off as a consensus message. The sender can
still have any number of bids signed, for any slot and proposer it names: a bid says "this block, for this
slot, pays this", and it is for the sender to send it where that is wanted.

The hashing is SSZ's, written out for this one container, with SHA-256 from Jaune: a bid is nine fields,
merkleized as sixteen leaves; a 48-byte key is two leaves hashed together. `bls-test` checks the root
against `JauneConsensus`'s own merkleization and domain, and the whole of it against a registration a real
validator signed for a real relay under the same domain. -/

namespace Evm.Bid

open Jaune Evm.Service

def magic : ByteArray := "JBID2".toUTF8
def keyMagic : ByteArray := "JKEY1".toUTF8

def sha (bytes : ByteArray) : ByteArray := (Bytes.sha256 bytes.toList).toBytes.toByteArray

def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- Filled out with zeros to one leaf. -/
def leaf (bytes : ByteArray) : ByteArray := bytes ++ zeros (32 - bytes.size)

/-- A number in `width` bytes, lowest first, as SSZ writes numbers. -/
def little (width n : Nat) : ByteArray :=
  ⟨(Array.range width).map fun i => (n >>> (8 * i)).toUInt8⟩

/-- The root of leaves whose number is a power of two. -/
partial def merkle (leaves : Array ByteArray) : ByteArray :=
  if leaves.size ≤ 1 then leaves[0]?.getD (zeros 32)
  else merkle ((Array.range (leaves.size / 2)).map fun i => sha (leaves[2 * i]! ++ leaves[2 * i + 1]!))

/-- The root of a 48-byte public key: two leaves. -/
def keyRoot (key : ByteArray) : ByteArray :=
  sha (key.extract 0 32 ++ leaf (key.extract 32 48))

/-- What a builder offers for a block: the bid trace of the builder API. -/
structure Bid where
  slot : Nat
  parentHash : ByteArray
  blockHash : ByteArray
  builderKey : ByteArray
  proposerKey : ByteArray
  feeRecipient : ByteArray
  gasLimit : Nat
  gasUsed : Nat
  value : Nat

def Bid.root (b : Bid) : ByteArray :=
  merkle (#[leaf (little 8 b.slot), b.parentHash, b.blockHash, keyRoot b.builderKey, keyRoot b.proposerKey,
    leaf b.feeRecipient, leaf (little 8 b.gasLimit), leaf (little 8 b.gasUsed), little 32 b.value] ++
    Array.replicate 7 (zeros 32))

/-- The builder's signing domain for a chain whose genesis fork version this is: the domain type, then
the first 28 bytes of the root of the version with a zero genesis validators root. -/
def domain (forkVersion : ByteArray) : ByteArray :=
  ⟨#[0, 0, 0, 1]⟩ ++ (sha (leaf forkVersion ++ zeros 32)).extract 0 28

/-- What is signed: the root of the object and its domain, hashed together. -/
def signingRoot (objectRoot domain : ByteArray) : ByteArray := sha (objectRoot ++ domain)

/-- A key and its public key, worked out once. -/
structure Key where
  secret : Sign.Scalar
  publicKey : ByteArray

def Key.of (secret : Sign.Scalar) : Key := ⟨secret, (Sign.publicKey secret).toByteArray⟩

/-- The order of the group, as four 64-bit words, low first. -/
def order : Sign.Scalar :=
  ⟨0xffffffff00000001, 0x53bda402fffe5bfe, 0x3339d80809a1d805, 0x73eda753299d7d48⟩

/-- Whether a key is one: not zero and below the order. Done without a branch on the key's words, though
the answer itself is not a secret: a draw that is not a key is thrown away. -/
def usable (k : Sign.Scalar) : Bool :=
  let step (a b borrow : UInt64) : UInt64 × UInt64 :=
    let d := a - b - borrow
    (d, ((~~~a &&& b) ||| ((~~~a ||| b) &&& d)) >>> 63)
  let (_, c0) := step k.w0 order.w0 0
  let (_, c1) := step k.w1 order.w1 c0
  let (_, c2) := step k.w2 order.w2 c1
  let (_, c3) := step k.w3 order.w3 c2
  c3 == 1 && (k.w0 ||| k.w1 ||| k.w2 ||| k.w3) != 0

/-- A key from 32 bytes of randomness, if they make one: the top bit is dropped, and about nine draws in
ten are below the order. -/
def keyOf (random : ByteArray) : Option Key :=
  if random.size != 32 then none else
  let word (i : Nat) : UInt64 :=
    (List.range 8).foldl (fun w j => w ||| (random[i + j]!.toUInt64 <<< (8 * j).toUInt64)) 0
  let k : Sign.Scalar := ⟨word 0, word 8, word 16, word 24 &&& 0x7fffffffffffffff⟩
  if usable k then some (Key.of k) else none

/-- A key that everyone knows, for the service run as a process and for tests. Never one a machine holds:
`EfiMain.lean` draws its own. -/
def testKey : Option Key := keyOf (sha "a key for tests, known to everyone".toUTF8)

/-- The milliseconds a request to build and bid allows for transactions; 0 when it names none or is not
such a request. -/
def allowed (input : ByteArray) : Nat :=
  if input.size < magic.size + 64 || input.extract 0 magic.size != magic then 0
  else (input.extract (magic.size + 60) (magic.size + 64)).foldl (fun n b => n * 256 + b.toNat) 0

/-- What came of a request to build and bid. -/
structure Outcome where
  /-- The response, as the request's sender is given it. -/
  reply : ByteArray
  /-- When a block was built and signed for: the block and bid as a relay takes them (`Evm/Submit.lean`). -/
  submission : Option ByteArray := none
  /-- Of the transactions added to those the request proposed, the ones that went in, by their place
  among those added. -/
  added : Array Nat := #[]
  /-- What the witness lacked for transactions left out because of it (the fast engine's builder only). -/
  wanted : Array Fast.Lack := #[]
  /-- Whether transactions were added to those the request proposed, whether or not any went in. -/
  tried : Bool := false
  /-- When a block was built: the slot it is for, the hash of the block it is built on, and what it pays
  the proposer. Two blocks alike in the first two are rivals for one place, and the third says which is
  the better. -/
  slot : Nat := 0
  parent : ByteArray := .empty
  value : Nat := 0

/-- Transactions the machine adds to those a request proposes, which the request's sender has not seen. -/
structure Extra where
  /-- Each as it goes on the wire, in the order they are to be proposed after the request's own. -/
  wires : Array ByteArray := #[]
  /-- How many of the first of them may have what the witness lacked for them said in the answer: those
  that came with no proofs of their own. Of the rest nothing is said. -/
  loud : Nat := 0
  /-- Proofs and codes that came with them, added to the witness. -/
  nodes : Array ByteArray := #[]
  codes : Array ByteArray := #[]

/-- A request to build and bid, or a request for the key, carried out. `over` is asked before each
transaction whether the time allowed has run out (`Build.Stage.finishWith`); whoever has a clock supplies
it. Whatever it says, what comes back is a whole block and a bid for that block.

`added`, given the hash of the block built on, is transactions the request's sender did not propose and
is not shown: they are tried with the rest, by the fast engine's builder only (Jaune's wants to be told
beforehand everything a transaction will read, and nobody can say that of a transaction they have not
seen). The response tells the sender nothing of them but, in the places of those that went in, numbers
past the end of what it proposed. If the block cannot be built with them in it, whatever the reason, it
is built again without them, and the reason is not said: a block must not fail, or name a node of the
state, because of a transaction the sender is not to know about. -/
def buildWith {m : Type → Type} [Monad m] (over : m Bool) (key : Key) (input : ByteArray)
    (added : ByteArray → Extra := fun _ => {}) (other : Build.Other := Build.byJaune) : m Outcome := do
  if input == keyMagic then return { reply := key.publicKey }
  let refuse : Outcome := { reply := ({ status := 5 } : Build.Response).encode }
  if input.size < magic.size + 64 || input.extract 0 magic.size != magic then return refuse
  let start := magic.size
  let slot := (input.extract start (start + 8)).foldl (fun n b => n * 256 + b.toNat) 0
  let proposerKey := input.extract (start + 8) (start + 56)
  let forkVersion := input.extract (start + 56) (start + 60)
  match (Build.request (input.extract (start + 64) input.size)).run 0 with
  | none => return refuse
  | some (request, _) =>
    -- A request that allows a time is built against a clock, and no transaction in it may ask more of
    -- precompiled contracts than `Build.txWork`; with no time allowed the answer depends on the request alone.
    let request := if allowed input == 0 then request else { request with work := Build.txWork }
    -- The block the request proposed, with the added transactions after its own.
    let own := (Submit.proposed? request.witness.block).getD 0
    let parent := match request.witness.headers.getLast? with
      | some header => Trie.wordBytes (Trie.hashOf header)
      | none => .empty
    let extra := if request.engine then added parent else {}
    let plain := request
    let request := if extra.wires.isEmpty then request else
      match Submit.withMore? request.witness.block extra.wires with
      | some block =>
        { request with
          loud := own + extra.loud
          witness := { request.witness with
            block, nodes := request.witness.nodes ++ extra.nodes, codes := request.witness.codes ++ extra.codes.toList } }
      | none => request
    let (response, _, _) ← Build.runWith over request other
    let (response, request) ← if response.built.isNone && !extra.wires.isEmpty then do
        let (again, _, _) ← Build.runWith over plain other
        pure (again, plain)
      else pure (response, request)
    match response.built with
    | none => return { reply := response.encode, wanted := response.wanted, tried := !extra.wires.isEmpty }
    | some built =>
      let bid : Bid :=
        { slot, parentHash := Trie.wordBytes built.header.parentHash, blockHash := Trie.wordBytes built.hash,
          builderKey := key.publicKey, proposerKey,
          feeRecipient := built.header.coinbase.toBytes.toByteArray, gasLimit := built.header.gasLimit,
          gasUsed := built.header.gasUsed, value := built.value }
      match Sign.sign key.secret (signingRoot bid.root (domain forkVersion)).toList with
      | .ok signature =>
        let submission := Submit.submission
          { slot, builderKey := key.publicKey, proposerKey, value := built.value, blockHash := bid.blockHash,
            header := (Header.toRlpItem built.header).toBytes.toByteArray, block := request.witness.block,
            places := built.included, requests := built.requests.map (·.toByteArray), signature := signature.toByteArray }
        return { reply := response.encode ++ key.publicKey ++ signature.toByteArray, submission,
                 added := (built.included.filter (· ≥ own)).toArray.map (· - own), wanted := response.wanted,
                 tried := !extra.wires.isEmpty, slot, parent := bid.parentHash, value := built.value }
      | .error _ => return { reply := ({ status := 4 } : Build.Response).encode }

/-- The response alone. -/
def serveWith {m : Type → Type} [Monad m] (over : m Bool) (key : Key) (input : ByteArray) : m ByteArray := do
  return (← buildWith over key input).reply

/-- The slot a request to build and bid is for; 0 when it is not such a request. -/
def slotOf (input : ByteArray) : Nat :=
  if input.size < magic.size + 64 || input.extract 0 magic.size != magic then 0
  else (input.extract magic.size (magic.size + 8)).foldl (fun n b => n * 256 + b.toNat) 0

/-- The same with no clock: the time allowed is not looked at, and the answer is a function of the request
and the key. -/
def serve (key : Key) (input : ByteArray) : ByteArray :=
  Id.run (serveWith (pure false) key input)

/-- Whether a request is one of the two this file answers. -/
def mine (input : ByteArray) : Bool :=
  input == keyMagic || input.extract 0 magic.size == magic

end Evm.Bid
