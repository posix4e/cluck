import Evm.Stateless
import Evm.Engine

/-! Building one block, from transactions somebody else proposes and a witness for the state they touch.

`Evm.Stateless` is given a block and says whether it is valid. This is given the makings of a block and
makes one: it decides which of the proposed transactions go in and in what order, runs them, and works
out everything in the header that follows from running them. It is the same Jaune and the same witness
either way, and what was true there is true here: nothing the block read is taken on trust, and what
cannot be shown is left out, never guessed.

## The request

    "JBLD1"
    1   fork, as in a stateless request; 255 asks for mainnet's schedule
    8   chain id
    1   the rule for ordering: 0 as given, 1 by what each pays the proposer
    8   the most gas the block may use, however much the header would allow
    4   length, then a block as RLP: the header the slot fixes, the proposed transactions, withdrawals
    then headers, nodes, codes and keys exactly as in a stateless request

The header in the request is a template. What the slot fixes has to be in it and right: parent hash, fee
recipient, number, gas limit, time, randomness, parent beacon root, extra data. It is checked against the
parent by Jaune's own `validateHeader`, so a gas limit out of step or a time not after the parent's is
refused here, not found out by a relay. Two fields follow from the parent alone, the base fee and the
excess blob gas, and are worked out here from it. The fields that follow from running the block (state
root, the roots of transactions and receipts, logs bloom, gas used, blob gas used, withdrawals root,
requests hash) are worked out here too. Whatever the sender put in any of those is replaced.

## What goes in

A proposed transaction is left out, and the block goes on without it, when it does not decode; when its
signer cannot be recovered; when Jaune rejects it on the state as it then stands (nonce, balance, fees, gas
limit); when it would take the block past the gas asked for; or **when it read anything the witness does
not prove**. The last is what keeps a short witness from becoming a wrong block: such a transaction ran on
a state that never was, so its effects are thrown away with it. Under rule 1 a transaction that carries
blobs is left out too, because nothing here handles the blobs that would have to go with it.

Rule 1 is the order a builder with no opinion would use: of each signer's transactions the one with the
lowest nonce is a candidate, and the candidate paying the most per unit of gas to the block's fee recipient
goes next. Ties go to the one proposed first. Rule 0 is for tests, where the order is the thing known.

Whoever sends the request still decides what is proposed and what the witness proves, so they can keep a
transaction out by not proposing it or by leaving its signer's account unproven. The order among those
that go in is not theirs to choose under rule 1.

## The response

    1    status: 0 a block was built. Otherwise none was, and nothing follows but 32 bytes that are
         zero or, for 6, the hash of a node the witness lacks: 3 the template is not a header the parent
         allows; 4 Jaune failed outside any one transaction, in a system call or the requests, which a
         witness that lacks a system contract will cause; 5 not a request; 6 the witness falls short of
         what the block as a whole needs; 7 the witness is malformed
    32   the block's hash
    32   its state root
    32   what the fee recipient's balance rose by over the transactions (before withdrawals), in wei
    8    gas used
    4    how many transactions went in, then for each, 4 bytes: its place among those proposed
    4    length, then the header as RLP
    4    how many requests the block made of the consensus layer (deposits, withdrawals, consolidations),
         then each with its length: a byte for its kind and then its data, as the header's hash of them
         is taken

The block is that header, those transactions in that order, no ommers, and the withdrawals proposed. The
sender has the transactions and puts the block together; the response is small whatever the block is.

## By the fast engine

A request that begins `JBLF1` is the same in every other byte and is built by the engine of `Fast/`, not by
Jaune: the same rule for what goes in and in what order, the same response. Three things differ. The
engine reads the witness as it goes, so the addresses and slot numbers a request carries are not used. A
transaction that asks the witness for what it cannot prove is undone whole and left out, as here, but the
engine knows it at the moment of asking, not from a list checked afterwards. And when the block's own
calls, before the first transaction or after the last, ask for what the witness lacks, the answer is 6,
where Jaune's is 4. `build-test` puts every case to both.

## On what was sent before

A request that begins `JBLF2` is one for the fast engine with one more byte after those five, and is read
with what whoever answers has kept of earlier such requests (`Kept`):

    "JBLF2"
    1   0 to build on what is kept; 1 to have everything kept forgotten first
    then everything a request has after its own five bytes

It need give only the trie nodes and the codes that no request since the last forgetting gave, and of the
headers only those after the newest it gave before: fewer than 255 headers are joined to the kept ones
where the oldest given names a kept one as its parent, and none at all stands for the kept ones as they
are. What it gives is kept in its turn, whatever becomes of the block. Nodes and codes are found by
their hashes and headers by the hash the next one names, kept or given alike, so a kept one proves
exactly what the same bytes would prove in the request, and nothing kept can make a block wrong. What
is kept does change which requests can be answered: one that leaves out what was never given, or was
forgotten, is answered as any request with a short witness is (6, or transactions left out), and whoever
sends it has to know what it has sent. When the nodes and codes given since the last forgetting come to
more than `Kept.limit` bytes, everything is forgotten once the request that passed it is answered.

Who signed each transaction of the last such request is kept too (`Signers`), because finding that out
is the largest part of what a request costs before its first transaction goes in, and a slot's requests
propose mostly the same transactions. A signer is kept under the hash that was signed, with the
signature and the chain it was found for, and is taken for a transaction only when all of those are the
transaction's own; it was worked out here, from a transaction given here, and is what working it out
again would give. Nobody sends one. They are not counted in the limit: there are no more of them than the
last request had transactions. The transactions a machine adds to a request itself are left out of this
altogether (`Request.fromSender`). A
request that begins `JBLF1` neither reads what is kept nor adds to it, and is still a function of its
bytes. So is one that begins `JBLF2` where nothing is kept: `serve` here keeps nothing, and only a
machine that builds for relays does (`Evm/Machine.lean`).

Statuses 0 and 3 are about the request alone, or for `JBLF2` about it and what is kept. A block built here was not then put to `Evm.Stateless` as a
check: `build-test` does that, on test chains and on blocks of mainnet built again from their own
transactions, where the hash has to come out as the chain's. -/

namespace Evm.Build

open Jaune Evm.Service Evm.Stateless
open Evm.Trie (Node Store)

def magic : ByteArray := "JBLD1".toUTF8
/-- The same request, built by the fast engine of `Fast/` (see "By the fast engine" above). -/
def magicFast : ByteArray := "JBLF1".toUTF8
/-- The fast engine's request read with what was sent before (see "On what was sent before" above). -/
def magicSeen : ByteArray := "JBLF2".toUTF8

/-- Who signed a transaction, with everything that was worked out from besides the hash signed: the
chain, whether the transaction is of the first kind (whose `v` carries the chain), and the signature. -/
structure Signer where
  chain : UInt64
  legacy : Bool
  v : Nat
  r : Bytes
  s : Bytes
  sender : Address

/-- Signers by the hash each signed. -/
abbrev Signers := Std.TreeMap U256 Signer Trie.order

/-- Who signed `tx`, and the entry that says so under the hash signed: the one held, when it was worked
out from this same signature on this chain, and otherwise worked out now (`recoverSender`, which reads of
a transaction its signature, its kind and the hash signed, and nothing else). `none` when nobody can be
found to have signed it. -/
def Signers.signer (held : Signers) (chain : UInt64) (tx : Transaction) : Option (U256 × Signer) :=
  match tx.signingHash with
  | none => none
  | some hash =>
    let legacy := match tx.type with
      | .legacy .. => true
      | _ => false
    let known := match held.get? hash with
      | some known =>
        if known.chain == chain && known.legacy == legacy && known.v == tx.v && known.r == tx.r && known.s == tx.s
        then some known else none
      | none => none
    match known with
    | some known => some (hash, known)
    | none =>
      match recoverSender chain tx with
      | .ok sender => some (hash, { chain, legacy, v := tx.v, r := tx.r, s := tx.s, sender })
      | .error _ => none

structure Request where
  witness : Stateless.Request
  /-- 0 as given, 1 by what each pays. -/
  rule : Nat
  gasCap : Nat
  /-- Whether the fast engine builds it: which of the two beginnings the request had. -/
  engine : Bool := false
  /-- Of the transactions proposed, how many from the first may have what the witness lacked for them
  said in the answer (`Response.wanted`). Not part of a request as it is written: every transaction a
  request proposes may; the ones added to it by the machine itself may or may not (`Evm/Bid.lean`). -/
  loud : Nat := 1000000000
  /-- The work one transaction may ask of precompiled contracts (`Bridge.work`), by the fast engine. Not
  part of a request as it is written, and no limit unless whoever runs it sets one: a block built with
  no clock running is a function of its request. -/
  work : UInt64 := 0xffffffffffffffff
  /-- For a request read with what was sent before: whether that is to be forgotten first. `none` for
  any other request. -/
  seen : Option Bool := none
  /-- Nodes and codes held already, by their hashes, beside those the witness lists. Not part of a
  request as it is written: `Kept.take` puts them here. -/
  held : Store := .empty
  heldCodes : Std.HashMap Fast.Word ByteArray := {}
  /-- Who signed the transactions of the request before this one, for a request read with what was sent
  before: `Kept.take` puts them here too. -/
  signers : Signers := {}
  /-- Of the transactions proposed, how many from the first came from whoever sent the request. The
  signers of the rest, which the machine added itself (`Evm/Bid.lean`), are neither looked for among
  those kept nor kept: how long a request takes then says nothing of them that it did not before. -/
  fromSender : Nat := 1000000000

/-- What one transaction may ask of precompiled contracts in a block built against a clock: a quarter of a
second, by `Bridge.work`. The clock is looked at between transactions and cannot be looked at inside one,
so this is what one transaction can make a block late by, as far as those contracts go, and it is under
the half second after which a block is not sent (`Send.grace`). A proof checked on bn254 is some 20 ms
of it and a hundred signers recovered 80; a transaction that wants more is left out, and said to be. -/
def txWork : UInt64 := 250000

def request (input : ByteArray) : P Request := do
  let begins ← take input magic.size
  let engine ← if begins == magic then pure false else if begins == magicFast || begins == magicSeen then pure true else stop
  let seen : Option Bool ← if begins != magicSeen then pure none else do
    let forget ← nat input 1
    if forget > 1 then stop
    pure (some (forget == 1))
  let code ← nat input 1
  let fork ← if code == 255 then pure none else match Stateless.forkOf code with
    | some fork => pure (some fork)
    | none => stop
  let chainId ← nat input 8
  let rule ← nat input 1
  if rule > 1 then stop
  let gasCap ← nat input 8
  let block ← sized input
  let headers ← many (← nat input 4) (sized input)
  let nodes ← many (← nat input 4) (sized input)
  let codes ← many (← nat input 4) (sized input)
  let keys ← many (← nat input 4) (sized input)
  pure { witness := { fork, chainId := chainId.toUInt64, block, headers, nodes := nodes.toArray, codes, keys },
         rule, gasCap, engine, seen }

def Request.encode (r : Request) : Option ByteArray := do
  let fork ← match r.witness.fork with
    | some fork => Stateless.forkCode fork
    | none => some 255
  let list (items : List ByteArray) : ByteArray :=
    items.foldl (fun out item => out ++ Evm.Service.sized item) (be 4 items.length)
  let begins := match r.seen with
    | some forget => magicSeen ++ be 1 (if forget then 1 else 0)
    | none => if r.engine then magicFast else magic
  pure <| begins ++ be 1 fork ++ be 8 r.witness.chainId.toNat ++ be 1 r.rule ++ be 8 r.gasCap ++
    Evm.Service.sized r.witness.block ++ list r.witness.headers ++ list r.witness.nodes.toList ++
    list r.witness.codes ++ list r.witness.keys

/-- What is kept of the requests read with what was sent before: their nodes and codes by hash, the
headers last built on, and how much has been given since nothing was kept. -/
structure Kept where
  nodes : Store := .empty
  codes : Std.HashMap Fast.Word ByteArray := {}
  /-- Oldest first, each with its hash; never more than 255. -/
  chain : Array (U256 × ByteArray) := #[]
  /-- The bytes of the nodes and codes given since nothing was kept, counted each time one is given. -/
  given : Nat := 0
  /-- Who signed the transactions of the last request built with what was sent before. `take` hands them
  to the next and does not change them: whoever runs the request puts that request's in their place
  (`runKeeping`, `Evm/Bid.lean`). -/
  signers : Signers := {}

/-- The most the nodes and codes given may come to before everything is forgotten. A request gives a
megabyte or two when nothing is kept and a tenth of that when the last one's are, so this is some
minutes of requests; held by hash in a tree it takes about a third more than its bytes, out of a heap
of 256 MiB that also holds a request of up to 32 MiB while it is read. -/
def Kept.limit : Nat := 16 * 1024 * 1024

/-- A request read with what was sent before, made whole from what is kept, and what is kept after it.
Any other request comes back as it is, and so does what is kept.

The nodes and codes it gives join those kept, by their hashes. Its headers, when there are fewer than
255, follow the kept ones up to the one the oldest given names as its parent; when there are none, the
kept ones stand as they are. Whether the result is a chain to the block's parent is not looked at here:
`begin` checks that of every request, joined or not. What was given is counted, and past `limit`
none of those is kept after this request. The signers kept go with the request, unless it says to forget. -/
def Kept.take (kept : Kept) (r : Request) (limit : Nat := Kept.limit) : Request × Kept :=
  match r.seen with
  | none => (r, kept)
  | some forget =>
    let kept : Kept := if forget then {} else kept
    let given := r.witness.headers.toArray.map fun header => (Trie.hashOf header, header)
    let before : Array (U256 × ByteArray) :=
      if given.size ≥ 255 then #[] else
      match r.witness.headers.head? with
      | none => kept.chain
      | some oldest =>
        match Stateless.header oldest with
        | none => #[]
        | some header =>
          match kept.chain.findIdx? (·.1 == header.parentHash) with
          | some i => kept.chain.extract 0 (i + 1)
          | none => #[]
    let chain := before ++ given
    let chain := chain.extract (chain.size - 255) chain.size
    let nodes := r.witness.nodes.foldl (fun store node => store.insert (Trie.hashOf node) node) kept.nodes
    let codes := r.witness.codes.foldl (fun codes code => codes.insert (Fast.keccak code) code) kept.codes
    let size := r.witness.codes.foldl (fun n code => n + code.size)
      (r.witness.nodes.foldl (fun n node => n + node.size) kept.given)
    let whole : Request :=
      { r with
        held := nodes, heldCodes := codes, signers := kept.signers
        witness := { r.witness with headers := chain.toList.map (·.2), nodes := #[], codes := [] } }
    (whole, if size > limit then { signers := kept.signers } else { nodes, codes, chain, given := size, signers := kept.signers })

/-- A block that was built. -/
structure Built where
  header : Header
  hash : U256
  /-- Places, among the transactions proposed, of those that went in, in the block's order. -/
  included : List Nat
  value : Nat
  /-- What the block asks of the consensus layer, each a byte for its kind and then its data. -/
  requests : List Bytes := []

structure Response where
  status : UInt8
  /-- For a status other than 0: zero, or the hash of a node the witness lacks. -/
  lacking : U256 := 0
  built : Option Built := none
  /-- What the witness lacked for transactions that were left out because of it: not part of the answer
  as it is written out, and for whoever can add to the witness and ask again. Only the fast engine's
  builder says. -/
  wanted : Array Fast.Lack := #[]

def Response.encode (r : Response) : ByteArray :=
  match r.status, r.built with
  | 0, some b =>
    let header := (Header.toRlpItem b.header).toBytes.toByteArray
    b.included.foldl (fun out i => out ++ be 4 i)
      (be 1 0 ++ Trie.wordBytes b.hash ++ Trie.wordBytes b.header.stateRoot ++
        Trie.wordBytes b.value.toU256 ++ be 8 b.header.gasUsed ++ be 4 b.included.length) ++
      Evm.Service.sized header ++
      b.requests.foldl (fun out r => out ++ Evm.Service.sized r.toByteArray) (be 4 b.requests.length)
  | status, _ => be 1 status.toNat ++ Trie.wordBytes r.lacking

/-- What a transaction pays the fee recipient for each unit of gas, at this base fee; `none` when it does
not cover the base fee, or carries blobs. -/
def tip (baseFee : Nat) (tx : Transaction) : Option Nat :=
  let capped (maxPriority maxFee : Nat) : Option Nat :=
    if maxFee < baseFee then none else some (min maxPriority (maxFee - baseFee))
  match tx.type with
  | .legacy gasPrice _ => capped gasPrice gasPrice
  | .eip2930 _ gasPrice _ _ => capped gasPrice gasPrice
  | .eip1559 _ maxPriority maxFee _ _ => capped maxPriority maxFee
  | .eip7702 _ maxPriority maxFee _ _ _ => capped maxPriority maxFee
  | .eip4844 .. => none

/-- A transaction proposed: where it stood in the request, who signed it, what it pays. -/
structure Candidate where
  place : Nat
  tx : Transaction
  sender : Address
  tip : Nat

/-- The order of rule 1. Each signer's transactions are taken lowest nonce first; of the transactions at
the front of their signers' queues, the one paying most goes next, the earlier proposed if two pay the
same.

Each transaction is given the number of its signer's others that go before it (a lower nonce, or the same
nonce and an earlier place); those with none before them are the fronts. Taking a front leaves each of its
signer's others with one fewer before it. That is one pass over every pair to begin with and one pass over
the list for each transaction taken. (Until 2026-11-25 the fronts were worked out anew from every pair for
each transaction taken, which for 400 transactions was 0.8 s of a block that took 1.9 s to build.) -/
def byTip (waiting : List Candidate) : Array Candidate := Id.run do
  let all := waiting.toArray
  let taken := all.size + 1
  let mut before : Array Nat := all.map fun c => all.foldl (fun n d =>
    if d.sender == c.sender && (d.tx.nonce < c.tx.nonce || (d.tx.nonce == c.tx.nonce && d.place < c.place))
    then n + 1 else n) 0
  let mut out : Array Candidate := Array.mkEmpty all.size
  for _ in [0:all.size] do
    let mut best : Option (Nat × Candidate) := none
    for c in all, i in [0:all.size] do
      if before[i]! == 0 then
        best := match best with
          | none => some (i, c)
          | some (j, b) => if c.tip > b.tip || (c.tip == b.tip && c.place < b.place) then some (i, c) else some (j, b)
    let some (chosen, front) := best | break
    out := out.push front
    before := before.set! chosen taken
    for c in all, i in [0:all.size] do
      let n := before[i]!
      if n != 0 && n != taken && c.sender == front.sender then
        before := before.set! i (n - 1)
  return out

/-- What has been read so far and shown to be in the witness, so that each transaction is asked only
about what it read that nothing before it did. -/
structure Shown where
  accounts : AdrSet := {}
  slots : KeySet := {}

/-- The accounts and slots that are in the state after a transaction and were not before it. A transaction
that makes an account or a slot has to be shown that it was not there, as a block that is checked has to
be; told apart here by counting, so that a transaction that makes nothing costs one pass over the accounts
and no more. One that makes as many as it removes is not noticed here, and is by the check of the whole
block at the end. -/
def madeBy (before after : State) : List Address × List (Address × U256) :=
  let accounts := if after.size == before.size then [] else after.keys.filter fun a => !before.contains a
  let slots := after.foldl (fun out address account =>
    let old := (before.get address).storage
    if account.storage.size == old.size then out
    else (account.storage.keys.filter fun slot => (old.get? slot).isNone).foldl
      (fun out slot => (address, slot) :: out) out) []
  (accounts, slots)

/-- Whether everything in `reads` that is not yet in `shown`, and everything a transaction made, is supplied
or proven absent. An error, saying what, when something was read that the witness does not account for. -/
def showReads (known : Known) (shown : Shown) (reads : BlockAccessListBuilder)
    (made : List Address × List (Address × U256)) : Except String Shown :=
  let accounts := (reads.readAccounts.toList.filter fun a => !shown.accounts.contains a) ++ made.1
  let slots := (reads.readSlots.toList.filter fun k => !shown.slots.contains k) ++ made.2
  match checkReads known accounts slots with
  | .ok () =>
    .ok { accounts := accounts.foldl (fun s a => s.insert a) shown.accounts,
          slots := slots.foldl (fun s k => s.insert k) shown.slots }
  | .error (.lacking hash what) => .error (if what == "" then s!"a node of the witness, {hash}" else what)
  | .error _ => .error "the witness does not read"

/-- What became of one transaction proposed: not part of a response, for whoever is making requests. -/
structure Note where
  place : Nat
  went : Bool
  /-- For one that went in, the gas the block had used once it had run; otherwise why it was left out. -/
  said : String

/-- A block part of the way through being filled: what is still proposed, in the order it will be tried,
and the block as it stands. -/
structure Filling where
  rest : List Candidate
  benv : Benv
  bout : BlockOutput
  shown : Shown := {}
  included : Array Nat := #[]
  notes : Array Note := #[]

/-- The next proposed transaction, put in or left out. One that Jaune rejects, or that read what the
witness does not prove, leaves the state and the block as they were before it. -/
def Filling.step (known : Known) (gasCap : Nat) : Filling → Except TransitionError Filling
  | ⟨[], benv, bout, shown, included, notes⟩ => .ok ⟨[], benv, bout, shown, included, notes⟩
  | ⟨c :: rest, benv, bout, shown, included, notes⟩ =>
    if bout.blockGasUsed + c.tx.gasLimit > gasCap then
      .ok ⟨rest, benv, bout, shown, included, notes.push ⟨c.place, false, "would pass the gas asked for"⟩⟩
    else
      match processTransaction benv bout c.tx included.size with
      | .ok (state, bout') =>
        match showReads known shown bout'.blockAccessListBuilder (madeBy benv.state state) with
        | .ok shown' =>
          .ok ⟨rest, benv.withState state, bout', shown', included.push c.place,
            notes.push ⟨c.place, true, s!"{bout'.blockGasUsed}"⟩⟩
        | .error what => .ok ⟨rest, benv, bout, shown, included, notes.push ⟨c.place, false, s!"read {what}"⟩⟩
      | .error (.internal e) => .error (.internal e)
      | .error e => .ok ⟨rest, benv, bout, shown, included, notes.push ⟨c.place, false, s!"rejected: {e.render}"⟩⟩

/-- A block being built: what was settled before its first transaction, and how far it has been filled. -/
structure Job where
  fork : Fork
  known : Known
  /-- The header with everything in it that does not come from running the block. -/
  blank : Header
  template : Block
  gasCap : Nat
  /-- The fee recipient's balance before the first transaction. -/
  paidBefore : Nat
  filling : Filling

/-- A block being built by the fast engine: what was settled before its first transaction, what is still
proposed, and the block as it stands. -/
structure FastJob where
  fork : Fork
  chainId : UInt64
  witness : Bridge.Witness
  blank : Header
  template : Block
  gasCap : Nat
  blk : Fast.BlockEnv
  host : Fast.Host
  /-- The block's body with no transactions in it: its withdrawals, and what it allows. -/
  body : Fast.BlockInput
  /-- The fee recipient's balance before the first transaction. -/
  paidBefore : Nat
  rest : List Candidate
  out : Fast.BlockOutput
  /-- The transactions that went in, in the block's order. -/
  taken : Array Transaction := #[]
  included : Array Nat := #[]
  notes : Array Note := #[]
  /-- What the witness lacked for the transactions left out because of it. -/
  wanted : Array Fast.Lack := #[]
  /-- The place from which nothing is said of what a transaction lacked. -/
  loud : Nat := 1000000000

/-- How far a request to build has got: answered, or a block still being filled. The fast engine's block
is here as what it is. Another engine's is here only as what can be asked of it: how many transactions are
still proposed, the stage after the next piece of work, and the stage with everything still proposed left
out. So a program that never starts another engine's block has nothing of that engine linked into it;
Jaune's is made into this by `Job.stage` below, and the image that builds for relays never calls that. -/
inductive Stage where
  | done (response : Response) (notes : Array Note) (why : String)
  | going (rest : Nat) (step : Unit → Stage) (cut : Unit → Stage)
  | goingFast (job : FastJob)

instance : Inhabited Stage := ⟨.done { status := 4 } #[] ""⟩

/-- An engine other than the fast one, for a request that asks for it: given the request, the fork, the
parent, the headers before it and the template, the stage the block begins at. -/
abbrev Other := Request → Fork → Header → List Header → Block → Stage

/-- No other engine. A request that asks for one is then not a request this program knows. -/
def noOther : Other := fun _ _ _ _ _ => .done { status := 5 } #[] "this program builds with the fast engine only"

/-- An answer that came out of the witness's own monad. -/
def answered : M (Response × Array Note) → Stage
  | .ok (response, notes) => .done response notes ""
  | .error (.lacking hash what) => .done { status := 6, lacking := hash } #[] what
  | .error .malformed => .done { status := 7 } #[] ""
  | .error .failure => .done { status := 4 } #[] ""

/-- What is the same whoever builds: the header with everything in it that the parent fixes, checked as a
header the parent allows, and the proposed transactions in the order they will be tried, with who signed
each (those the request holds from the one before are not worked out again). The error is the answer when
the template is refused. -/
def openTemplate (r : Request) (fork : Fork) (parent : Header) (chain : BlockChain) (template : Block) :
    Except Stage (Header × List Candidate × Signers) := do
  let rules := fork.ruleSet
  -- What the parent alone fixes is worked out from it; then the template has to be a header the parent
  -- allows, with no gas used yet.
  let asked := { template.header with gasUsed := 0 }
  let baseFee ← match expectedBaseFee { asked with baseFeePerGas := if rules.header.baseFee then some 0 else none } parent with
    | .ok fee => pure fee
    | .error _ => .error (.done { status := 3 } #[] "")
  let blank := { asked with
    baseFeePerGas := baseFee,
    excessBlobGas := if rules.header.blobGas then some (calcExcessBlobGas rules.blob parent) else none }
  if (validateHeader rules chain blank).isOk == false || !template.ommers.isEmpty then
    .error (.done { status := 3 } #[] "")
  let fee := blank.baseFeePerGas.getD 0
  let (proposed, signers) := template.transactions.zipIdx.foldl (init := ((#[] : Array Candidate), ({} : Signers)))
    fun (proposed, signers) (item, place) =>
      match decodeTransaction rules item with
      | .error _ => (proposed, signers)
      | .ok tx =>
        let theirs := place < r.fromSender
        match (if theirs then r.signers else ({} : Signers)).signer r.witness.chainId tx with
        | none => (proposed, signers)
        | some (hash, signer) =>
          let signers := if theirs then signers.insert hash signer else signers
          let sender := signer.sender
          if r.rule == 0 then (proposed.push { place, tx, sender, tip := 0 }, signers)
          else match tip fee tx with
            | some t => (proposed.push { place, tx, sender, tip := t }, signers)
            | none => (proposed, signers)
  let proposed := proposed.toList
  pure (blank, if r.rule == 0 then proposed else (byTip proposed).toList, signers)

/-- Everything before the first transaction: the witness checked, the template checked against the parent,
the two system calls that open a block, and the proposed transactions in the order they will be tried. -/
def start (r : Request) (fork : Fork) (parent : Header) (ancestors : List Header) (template : Block) :
    M (Except Stage Job) := do
  let rules := fork.ruleSet
  let known ← materialise r.witness parent.stateRoot
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := known.state, chainId := r.witness.chainId }
  match openTemplate r fork parent chain template with
  | .error refused => return .error refused
  | .ok (blank, ordered, _) =>
    let benv := initBenv fork chain blank
    let opened : Except TransitionError (Benv × BlockAccessListBuilder) := do
      let (stBeacon, bal) ← beaconRootsCall rules benv
      let benvBeacon := benv.withState stBeacon
      let (stHistory, bal) ← historyStorageCall rules benvBeacon bal
      pure (benvBeacon.withState stHistory, bal)
    match opened with
    | .error _ => return .error (.done { status := 4 } #[] "")
    | .ok (begun, bal) =>
      return .ok
        { fork, known, blank, template, gasCap := min r.gasCap blank.gasLimit,
          paidBefore := (begun.state.bal benv.stat.coinbase).toNat,
          filling := { rest := ordered, benv := begun, bout := { BlockOutput.init with blockAccessListBuilder := bal } } }

/-- An answer that says the witness falls short, in the engine's words for where. -/
def short (witness : Bridge.Witness) (world : Fast.World) (notes : Array Note := #[]) : Stage :=
  match witness.shortfall world with
  | .lacking hash what => .done { status := 6, lacking := hash } notes what
  | _ => .done { status := 7 } notes ""

/-- The same beginning for the fast engine: the template checked against the parent, the engine's world
over the witness, the block's two opening calls, and what the fee recipient has before any transaction.
Beside the stage, who signed the transactions proposed, for whoever keeps that for the next request. -/
def startFastKeeping (r : Request) (fork : Fork) (parent : Header) (ancestors : List Header) (template : Block) :
    Stage × Signers :=
  if !Bridge.supported fork then (.done { status := 4 } #[] "the engine has no rules for this fork", {}) else
  -- Jaune's checks of a header want a chain with a state, and read none of it.
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := State.ofPresentList [], chainId := r.witness.chainId }
  match openTemplate r fork parent chain template with
  | .error refused => (refused, {})
  | .ok (blank, ordered, signers) =>
    match Bridge.body fork r.witness.chainId { template with header := blank } [] with
    | none => (.done { status := 5 } #[] "", {})
    | some body => (·, signers) <|
      let body := { body with work := r.work }
      let witness := Bridge.Witness.of r.witness parent.stateRoot r.held r.heldCodes
      let blk := Bridge.environment fork r.witness.chainId blank ancestors
      let host := Bridge.host fork
      let (world, stack) := Fast.openBlock blk host body ByteArray.empty (Fast.World.new witness.backing)
      let (world, recipient) := world.account blk.coinbase
      if world.missing then short witness world
      else .goingFast
        { fork, chainId := r.witness.chainId, witness, blank, template, gasCap := min r.gasCap blank.gasLimit, blk, host,
          body, paidBefore := recipient.balance.toNat, rest := ordered, loud := r.loud,
          out := { world, stack, receipts := #[], gasUsed := 0, blobs := 0, requests := #[] } }

/-- The next proposed transaction, put in or left out, by the fast engine. One the engine refuses, or that
asked the witness for what it cannot prove, leaves the world and the block as they were before it. -/
def FastJob.step : FastJob → FastJob
  | ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest, out, taken, included, notes, wanted, loud⟩ =>
    match rest with
    | [] => ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, [], out, taken, included, notes, wanted, loud⟩
    | c :: rest =>
      let leftOut (why : String) (out : Fast.BlockOutput) (lacks : Array Fast.Lack := #[]) : FastJob :=
        ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest, out, taken, included,
         notes.push ⟨c.place, false, why⟩,
         if c.place < loud && wanted.size < 4 * Fast.maxLacks then wanted ++ lacks else wanted, loud⟩
      if out.gasUsed.toNat + c.tx.gasLimit > gasCap then leftOut "would pass the gas asked for" out
      else if (Bridge.chainOf c.tx).any (· != chainId) then leftOut "rejected: made for another chain" out
      else
        match Bridge.transactionFrom c.tx c.sender with
        | none => leftOut "rejected: a number in it is too big to be one" out
        | some tx =>
          let ⟨world, stack, receipts, gasUsed, blobs, requests⟩ := out
          let allowed : Fast.Allowance :=
            { gas := blk.gasLimit - gasUsed, blobs := body.maxBlobs - blobs, blobsPerTx := body.blobsPerTx,
              alwaysWarm := body.precompiles, work := body.work }
          match Fast.process blk host allowed tx stack world with
          | .error (why, world, stack) =>
            -- A marked world is the witness not answering. The transaction is undone already; the mark is
            -- taken off, since what could not be answered was not kept, and the next transaction starts clean.
            let why := if world.missing then s!"read what the witness does not prove, at {(Bridge.u256 world.lacking).toHex}"
              else s!"rejected: {why}"
            leftOut why ⟨{ world with missing := false, lacks := #[] }, stack, receipts, gasUsed, blobs, requests⟩ world.lacks
          | .ok (world, stack, receipt) =>
            let gasUsed := gasUsed + receipt.cumulativeGas
            ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest,
             ⟨world, stack, receipts.push { receipt with cumulativeGas := gasUsed }, gasUsed,
              blobs + tx.blobHashes.size.toUInt64, requests⟩,
             taken.push c.tx, included.push c.place, notes.push ⟨c.place, true, s!"{gasUsed.toNat}"⟩, wanted, loud⟩

/-- Everything after the last transaction, by the fast engine: withdrawals, the block's requests, the state
root and the header. -/
def FastJob.finish (job : FastJob) : Stage :=
  let rules := job.fork.ruleSet
  let notes := job.notes
  let witness := job.witness
  let ⟨world, stack, receipts, gasUsed, blobs, requests⟩ := job.out
  let (world, recipient) := world.account job.blk.coinbase
  let value := recipient.balance.toNat - job.paidBefore
  match Fast.closeBlock job.blk job.host job.body ⟨world, stack, receipts, gasUsed, blobs, requests⟩ with
  | .error (_, world) => if world.missing then short witness world notes else .done { status := 4 } notes ""
  | .ok out =>
    if out.world.missing then short witness out.world notes else
    match Bridge.rootAfter witness out.world with
    | .error (.lacking hash what) => .done { status := 6, lacking := hash } notes what
    | .error .malformed => .done { status := 7 } notes ""
    | .error .failure => .done { status := 4 } notes ""
    | .ok stateRoot =>
      let (receiptsRoot, bloom) := Bridge.receiptsRootAndBloom out.receipts
      -- The roots that depend on the block's body alone, by Jaune's functions on what it would have kept.
      let kept : BlockOutput :=
        { BlockOutput.init with
          blockGasUsed := out.gasUsed.toNat
          blobGasUsed := (out.blobs * Fast.gasPerBlob).toNat
          transactionsTrie := job.taken.toList.zipIdx.foldl (fun trie (tx, index) =>
            trie.insert (Rlp.Item.bytes index.toBytes).toBytes tx) BlockOutput.init.transactionsTrie
          withdrawalsTrie := processWithdrawalsTrie BlockOutput.init.withdrawalsTrie job.template.withdrawals }
      let asked := out.requests.toList.map (·.toList)
      let header : Header :=
        { job.blank with
          stateRoot, transactionsRoot := getTransactionsRoot kept, receiptsRoot, logsBloom := bloom,
          gasUsed := out.gasUsed.toNat,
          withdrawalsRoot := if rules.header.withdrawalsRoot then some (getWithdrawalsRoot kept) else none,
          blobGasUsed := if rules.header.blobGas then some kept.blobGasUsed else none,
          requestsHash := if rules.header.requestsHash then some (computeRequestsHash asked) else none }
      .done { status := 0, built := some ⟨header, header.hash, job.included.toList, value, asked⟩, wanted := job.wanted } notes ""

/-- Everything after the last transaction: withdrawals, the block's requests, the checks that everything
read was shown, the state root and the header. -/
def Job.finish (job : Job) : M (Response × Array Note) := do
  let rules := job.fork.ruleSet
  let known := job.known
  let filled := job.filling.benv
  let notes := job.filling.notes
  let value := (filled.state.bal filled.stat.coinbase).toNat - job.paidBefore
  let (stWds, boutWds) := withdrawalsPass rules filled job.filling.bout job.template.withdrawals
  match requestsPass rules (filled.withState stWds) boutWds with
  | .error _ => return ({ status := 4 }, #[])
  | .ok (after, out) =>
    -- As for a block that is checked: everything read was shown, and everything made was not there.
    let reads := out.blockAccessListBuilder
    let made := after.keys.filter fun address => !known.leaves.contains address
    let madeSlots := after.toList.flatMap fun (address, account) =>
      let old := (known.state.get address).storage
      (account.storage.keys.filter fun slot => (old.get? slot).isNone).map fun slot => (address, slot)
    checkReads known (reads.readAccounts.toList ++ made) (reads.readSlots.toList ++ madeSlots)
    let stateRoot ← rootAfter known after
    let header : Header :=
      { job.blank with
        stateRoot, transactionsRoot := getTransactionsRoot out, receiptsRoot := getReceiptRoot out,
        logsBloom := logsBloom out.blockLogs, gasUsed := max out.blockGasUsed out.blockStateGasUsed,
        withdrawalsRoot := if rules.header.withdrawalsRoot then some (getWithdrawalsRoot out) else none,
        blobGasUsed := if rules.header.blobGas then some out.blobGasUsed else none,
        requestsHash := if rules.header.requestsHash then some (computeRequestsHash out.requests) else none }
    -- Jaune's own checks of a header against what running the block gave, on the header just made.
    let agrees := stateTransitionChecks out header header.transactionsRoot stateRoot header.receiptsRoot
      header.logsBloom (getWithdrawalsRoot out) header.requestsHash
    if !agrees.isOk then return ({ status := 4 }, notes)
    return ({ status := 0, built := some ⟨header, header.hash, job.filling.included.toList, value, out.requests⟩ }, notes)

/-- A block being filled by Jaune, as a stage: the next proposed transaction, or, when none is left, the
end of the block; and the same block with everything still proposed left out, each noted as such. -/
partial def Job.stage (job : Job) : Stage :=
  .going job.filling.rest.length
    (fun _ =>
      if job.filling.rest.isEmpty then answered job.finish
      else match job.filling.step job.known job.gasCap with
        | .ok filling => Job.stage { job with filling }
        | .error _ => .done { status := 4 } #[] "")
    (fun _ =>
      let filling := job.filling
      Job.stage { job with filling := { filling with
        rest := [],
        notes := filling.rest.foldl (fun notes c => notes.push ⟨c.place, false, "out of time"⟩) filling.notes } })

/-- Jaune as the other engine. -/
def byJaune : Other := fun r fork parent ancestors template =>
  match start r fork parent ancestors template with
  | .ok (.ok job) => job.stage
  | .ok (.error refused) => refused
  | .error shortfall => answered (.error shortfall)

/-- Where a request to build starts: refused, or a block with nothing in it yet. One that does not ask for
the fast engine is `other`'s to begin. Beside it, who signed the transactions proposed, when the fast
engine got as far as them. -/
def beginKeeping (r : Request) (other : Other) : Stage × Signers :=
  let only (response : Response) (why : String := "") : Stage × Signers := (.done response #[] why, {})
  match rlpToBlockE r.witness.block.toList with
  | .error _ => only { status := 5 } "the block does not decode"
  | .ok (template, _) =>
    let fork := match r.witness.fork with
      | some fork => some fork
      | none =>
        if r.witness.chainId != 1 then none else
        match mainnetChainConfig.forkAt template.header.number template.header.timestamp with
        | .ok fork => if (Stateless.forkCode fork).isSome then some fork else none
        | .error _ => none
    match fork, r.witness.headers.mapM Stateless.header with
    | none, _ | _, none => only { status := 5 } "no fork, or a header that does not decode"
    | some fork, some ancestors =>
      let linked := (ancestors.zip (ancestors.drop 1)).all fun (a, b) => a.hash == b.parentHash
      match ancestors.getLast? with
      | none => only { status := 6 } "no headers"
      | some parent =>
        if !linked || parent.hash != template.header.parentHash then only { status := 5 } "the headers are not a chain to the parent"
        else if ancestors.length != min 255 template.header.number then only { status := 6 } "too few headers"
        else
          if r.engine then startFastKeeping r fork parent ancestors template
          else (other r fork parent ancestors template, {})

/-- Where a request to build starts, without the signers. -/
def begin (r : Request) (other : Other) : Stage := (beginKeeping r other).1

/-- One more piece of work: the next proposed transaction, or, when none is left, the end of the block. -/
def Stage.step : Stage → Stage
  | .done response notes why => .done response notes why
  | .going _ step _ => step ()
  | .goingFast job => if job.rest.isEmpty then job.finish else .goingFast job.step

/-- Everything still proposed is left out, each noted as such; the block ends with what is in it. -/
def Stage.cut : Stage → Stage
  | .going _ _ cut => cut ()
  | .goingFast job =>
    .goingFast { job with
      rest := [], notes := job.rest.foldl (fun notes c => notes.push ⟨c.place, false, "out of time"⟩) job.notes }
  | stage => stage

/-- Whether anything is still proposed that has not been tried. -/
def Stage.filling : Stage → Bool
  | .going rest _ _ => rest != 0
  | .goingFast job => !job.rest.isEmpty
  | .done .. => false

/-- How many more steps reach an answer when none is cut: one for each transaction still proposed, and one
to end the block. -/
def Stage.left : Stage → Nat
  | .going rest _ _ => rest + 1
  | .goingFast job => job.rest.length + 1
  | .done .. => 0

/-- A stage taken to its answer. Before each transaction `over` is asked whether to stop, and the first
time it says so the block is ended with what is in it. `over` is the only thing here that is not a function
of the request: on a machine with a clock it is "the time allowed has run out"; without one it never says
stop, and the block is the same every time. -/
def Stage.finishWith {m : Type → Type} [Monad m] (over : m Bool) : Nat → Stage → m Stage
  | 0, stage => pure stage
  | steps + 1, stage => do
    let stage ← if stage.filling then (do if (← over) then pure stage.cut else pure stage) else pure stage
    finishWith over steps stage.step

def Stage.answer : Stage → Response × Array Note × String
  | .done response notes why => (response, notes, why)
  | .going .. | .goingFast _ => ({ status := 4 }, #[], "")

/-- The answer to a request to build, when `over` is asked before each transaction whether to stop. Here and
below, a request that does not ask for the fast engine is built by `other`: Jaune unless the caller says
otherwise, and the machine that builds for relays says `noOther` (`Evm/Machine.lean`). -/
def runWith {m : Type → Type} [Monad m] (over : m Bool) (r : Request) (other : Other := byJaune) :
    m (Response × Array Note × String) := do
  let stage := begin r other
  return (← stage.finishWith over stage.left).answer

/-- The same, and who signed the transactions the request proposed, for the next request to be handed
(`Kept.signers`): none when the fast engine did not get as far as the transactions. -/
def runKeeping {m : Type → Type} [Monad m] (over : m Bool) (r : Request) (other : Other := byJaune) :
    m ((Response × Array Note × String) × Signers) := do
  let (stage, signers) := beginKeeping r other
  return ((← stage.finishWith over stage.left).answer, signers)

def runWithNotes (r : Request) (other : Other := byJaune) : Response × Array Note × String :=
  Id.run (runWith (pure false) r other)

def run (r : Request) (other : Other := byJaune) : Response := (runWithNotes r other).1

def serve (input : ByteArray) (other : Other := byJaune) : ByteArray :=
  match (request input).run 0 with
  | some (r, pos) =>
    -- Nothing is kept here: a request read with what was sent before is read with nothing.
    if pos = input.size then (run (({} : Kept).take r).1 other).encode else ({ status := 5 } : Response).encode
  | none => ({ status := 5 } : Response).encode

end Evm.Build

/-- Any kind of request, told apart by how it begins: a chain with its whole state (`Evm.Service`), one
block with a witness to be checked (`Evm.Stateless`, or by the fast engine `Evm.Engine`), or the makings of
a block to be built. -/
def Evm.serve (input : ByteArray) : ByteArray :=
  if input.extract 0 Evm.Build.magic.size == Evm.Build.magic
      || input.extract 0 Evm.Build.magicFast.size == Evm.Build.magicFast
      || input.extract 0 Evm.Build.magicSeen.size == Evm.Build.magicSeen then Evm.Build.serve input
  else if input.extract 0 Evm.Engine.magic.size == Evm.Engine.magic then Evm.Engine.serve input
  else if input.extract 0 Evm.Stateless.magic.size == Evm.Stateless.magic then Evm.Stateless.serve input
  else Evm.Service.serve input

/-- What the machine that builds for relays answers of these: a request to build by the fast engine, and a
block with its witness to be judged by the fast engine. Anything else gets the answer a request to build
gets when it is not one (status 5), a request to build by Jaune included. Nothing here calls Jaune's
interpreter, so none of it is in that machine's image; `scripts/build-efi` refuses to make the image if it
is. What is still Jaune's on this path is what both engines share: its types for headers, blocks and
transactions, their decoding, the check of a header against its parent, and the recovery of a signer. -/
def Evm.serveBuilder (input : ByteArray) : ByteArray :=
  if input.extract 0 Evm.Build.magic.size == Evm.Build.magic
      || input.extract 0 Evm.Build.magicFast.size == Evm.Build.magicFast
      || input.extract 0 Evm.Build.magicSeen.size == Evm.Build.magicSeen then Evm.Build.serve input Evm.Build.noOther
  else if input.extract 0 Evm.Engine.magic.size == Evm.Engine.magic then Evm.Engine.serve input
  else ({ status := 5 } : Evm.Build.Response).encode

/-- Which engines a machine has: what begins a block the fast engine was not asked for, and what answers
the requests that are neither for a bid, a key, a relay, nor the chain's next block. -/
structure Evm.Serving where
  other : Evm.Build.Other
  rest : ByteArray → ByteArray
  /-- For the console, when the machine starts. -/
  what : String

/-- The fast engine alone. The other choice, every engine, is written where it is used (`EfiSpec.lean`)
and not here: a value kept here would be made when this module starts, in every image, and would bring
Jaune's interpreter into each of them. -/
def Evm.Serving.builder : Evm.Serving :=
  { other := Evm.Build.noOther, rest := Evm.serveBuilder, what := "builds and judges with the fast engine only" }
