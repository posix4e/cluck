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

Statuses 0 and 3 are about the request alone. A block built here was not then put to `Evm.Stateless` as a
check: `build-test` does that, on test chains and on blocks of mainnet built again from their own
transactions, where the hash has to come out as the chain's. -/

namespace Evm.Build

open Jaune Evm.Service Evm.Stateless
open Evm.Trie (Node Store)

def magic : ByteArray := "JBLD1".toUTF8
/-- The same request, built by the fast engine of `Fast/` (see "By the fast engine" above). -/
def magicFast : ByteArray := "JBLF1".toUTF8

structure Request where
  witness : Stateless.Request
  /-- 0 as given, 1 by what each pays. -/
  rule : Nat
  gasCap : Nat
  /-- Whether the fast engine builds it: which of the two beginnings the request had. -/
  engine : Bool := false

def request (input : ByteArray) : P Request := do
  let begins ← take input magic.size
  let engine ← if begins == magic then pure false else if begins == magicFast then pure true else stop
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
         rule, gasCap, engine }

def Request.encode (r : Request) : Option ByteArray := do
  let fork ← match r.witness.fork with
    | some fork => Stateless.forkCode fork
    | none => some 255
  let list (items : List ByteArray) : ByteArray :=
    items.foldl (fun out item => out ++ Evm.Service.sized item) (be 4 items.length)
  pure <| (if r.engine then magicFast else magic) ++ be 1 fork ++ be 8 r.witness.chainId.toNat ++ be 1 r.rule ++ be 8 r.gasCap ++
    Evm.Service.sized r.witness.block ++ list r.witness.headers ++ list r.witness.nodes.toList ++
    list r.witness.codes ++ list r.witness.keys

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
same. -/
partial def byTip (waiting : List Candidate) (out : Array Candidate := #[]) : Array Candidate :=
  -- The front of each signer's queue: no other waiting transaction of that signer has a lower nonce, or
  -- the same nonce and an earlier place.
  let front := waiting.filter fun c => waiting.all fun d =>
    d.sender != c.sender || d.tx.nonce > c.tx.nonce || (d.tx.nonce == c.tx.nonce && d.place ≥ c.place)
  match front with
  | [] => out
  | first :: rest =>
    let best := rest.foldl (fun b c => if c.tip > b.tip || (c.tip == b.tip && c.place < b.place) then c else b) first
    byTip (waiting.filter (·.place != best.place)) (out.push best)

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

/-- How far a request to build has got: answered, or a block still being filled, by Jaune or by the fast
engine. -/
inductive Stage where
  | done (response : Response) (notes : Array Note) (why : String)
  | going (job : Job)
  | goingFast (job : FastJob)

/-- An answer that came out of the witness's own monad. -/
def answered : M (Response × Array Note) → Stage
  | .ok (response, notes) => .done response notes ""
  | .error (.lacking hash what) => .done { status := 6, lacking := hash } #[] what
  | .error .malformed => .done { status := 7 } #[] ""
  | .error .failure => .done { status := 4 } #[] ""

/-- What is the same whoever builds: the header with everything in it that the parent fixes, checked as a
header the parent allows, and the proposed transactions in the order they will be tried. The error is the
answer when the template is refused. -/
def openTemplate (r : Request) (fork : Fork) (parent : Header) (chain : BlockChain) (template : Block) :
    Except Stage (Header × List Candidate) := do
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
  let proposed := template.transactions.zipIdx.filterMap fun (item, place) =>
    match decodeTransaction rules item with
    | .error _ => none
    | .ok tx =>
      match recoverSender r.witness.chainId tx with
      | .error _ => none
      | .ok sender =>
        if r.rule == 0 then some { place, tx, sender, tip := 0 : Candidate }
        else (tip fee tx).map fun t => { place, tx, sender, tip := t }
  pure (blank, if r.rule == 0 then proposed else (byTip proposed).toList)

/-- Everything before the first transaction: the witness checked, the template checked against the parent,
the two system calls that open a block, and the proposed transactions in the order they will be tried. -/
def start (r : Request) (fork : Fork) (parent : Header) (ancestors : List Header) (template : Block) :
    M Stage := do
  let rules := fork.ruleSet
  let known ← materialise r.witness parent.stateRoot
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := known.state, chainId := r.witness.chainId }
  match openTemplate r fork parent chain template with
  | .error refused => return refused
  | .ok (blank, ordered) =>
    let benv := initBenv fork chain blank
    let opened : Except TransitionError (Benv × BlockAccessListBuilder) := do
      let (stBeacon, bal) ← beaconRootsCall rules benv
      let benvBeacon := benv.withState stBeacon
      let (stHistory, bal) ← historyStorageCall rules benvBeacon bal
      pure (benvBeacon.withState stHistory, bal)
    match opened with
    | .error _ => return .done { status := 4 } #[] ""
    | .ok (begun, bal) =>
      return .going
        { fork, known, blank, template, gasCap := min r.gasCap blank.gasLimit,
          paidBefore := (begun.state.bal benv.stat.coinbase).toNat,
          filling := { rest := ordered, benv := begun, bout := { BlockOutput.init with blockAccessListBuilder := bal } } }

/-- An answer that says the witness falls short, in the engine's words for where. -/
def short (witness : Bridge.Witness) (world : Fast.World) (notes : Array Note := #[]) : Stage :=
  match witness.shortfall world with
  | .lacking hash what => .done { status := 6, lacking := hash } notes what
  | _ => .done { status := 7 } notes ""

/-- The same beginning for the fast engine: the template checked against the parent, the engine's world
over the witness, the block's two opening calls, and what the fee recipient has before any transaction. -/
def startFast (r : Request) (fork : Fork) (parent : Header) (ancestors : List Header) (template : Block) : Stage :=
  -- Jaune's checks of a header want a chain with a state, and read none of it.
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := State.ofPresentList [], chainId := r.witness.chainId }
  match openTemplate r fork parent chain template with
  | .error refused => refused
  | .ok (blank, ordered) =>
    match Bridge.body fork r.witness.chainId { template with header := blank } [] with
    | none => .done { status := 5 } #[] ""
    | some body =>
      let witness := Bridge.Witness.of r.witness parent.stateRoot
      let blk := Bridge.environment fork r.witness.chainId blank ancestors
      let host := Bridge.host fork
      let (world, stack) := Fast.openBlock blk host body ByteArray.empty (Fast.World.new witness.backing)
      let (world, recipient) := world.account blk.coinbase
      if world.missing then short witness world
      else .goingFast
        { fork, chainId := r.witness.chainId, witness, blank, template, gasCap := min r.gasCap blank.gasLimit, blk, host,
          body, paidBefore := recipient.balance.toNat, rest := ordered,
          out := { world, stack, receipts := #[], gasUsed := 0, blobs := 0, requests := #[] } }

/-- The next proposed transaction, put in or left out, by the fast engine. One the engine refuses, or that
asked the witness for what it cannot prove, leaves the world and the block as they were before it. -/
def FastJob.step : FastJob → FastJob
  | ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest, out, taken, included, notes⟩ =>
    match rest with
    | [] => ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, [], out, taken, included, notes⟩
    | c :: rest =>
      let leftOut (why : String) (out : Fast.BlockOutput) : FastJob :=
        ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest, out, taken, included,
         notes.push ⟨c.place, false, why⟩⟩
      if out.gasUsed.toNat + c.tx.gasLimit > gasCap then leftOut "would pass the gas asked for" out
      else if (Bridge.chainOf c.tx).any (· != chainId) then leftOut "rejected: made for another chain" out
      else
        match Bridge.transactionFrom c.tx c.sender with
        | none => leftOut "rejected: a number in it is too big to be one" out
        | some tx =>
          let ⟨world, stack, receipts, gasUsed, blobs, requests⟩ := out
          let allowed : Fast.Allowance :=
            { gas := blk.gasLimit - gasUsed, blobs := body.maxBlobs - blobs, blobsPerTx := body.blobsPerTx,
              alwaysWarm := body.precompiles }
          match Fast.process blk host allowed tx stack world with
          | .error (why, world, stack) =>
            -- A marked world is the witness not answering. The transaction is undone already; the mark is
            -- taken off, since what could not be answered was not kept, and the next transaction starts clean.
            let why := if world.missing then s!"read what the witness does not prove, at {(Bridge.u256 world.lacking).toHex}"
              else s!"rejected: {why}"
            leftOut why ⟨{ world with missing := false }, stack, receipts, gasUsed, blobs, requests⟩
          | .ok (world, stack, receipt) =>
            let gasUsed := gasUsed + receipt.cumulativeGas
            ⟨fork, chainId, witness, blank, template, gasCap, blk, host, body, paidBefore, rest,
             ⟨world, stack, receipts.push { receipt with cumulativeGas := gasUsed }, gasUsed,
              blobs + tx.blobHashes.size.toUInt64, requests⟩,
             taken.push c.tx, included.push c.place, notes.push ⟨c.place, true, s!"{gasUsed.toNat}"⟩⟩

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
      .done { status := 0, built := some ⟨header, header.hash, job.included.toList, value, asked⟩ } notes ""

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

/-- Where a request to build starts: refused, or a block with nothing in it yet. -/
def begin (r : Request) : Stage :=
  let only (response : Response) (why : String := "") : Stage := .done response #[] why
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
          if r.engine then startFast r fork parent ancestors template else
          match start r fork parent ancestors template with
          | .ok stage => stage
          | .error shortfall => answered (.error shortfall)

/-- One more piece of work: the next proposed transaction, or, when none is left, the end of the block. -/
def Stage.step : Stage → Stage
  | .done response notes why => .done response notes why
  | .going job =>
    if job.filling.rest.isEmpty then answered job.finish
    else match job.filling.step job.known job.gasCap with
      | .ok filling => .going { job with filling }
      | .error _ => .done { status := 4 } #[] ""
  | .goingFast job => if job.rest.isEmpty then job.finish else .goingFast job.step

/-- Everything still proposed is left out, each noted as such; the block ends with what is in it. -/
def Stage.cut : Stage → Stage
  | .going job =>
    let filling := job.filling
    .going { job with filling := { filling with
      rest := [],
      notes := filling.rest.foldl (fun notes c => notes.push ⟨c.place, false, "out of time"⟩) filling.notes } }
  | .goingFast job =>
    .goingFast { job with
      rest := [], notes := job.rest.foldl (fun notes c => notes.push ⟨c.place, false, "out of time"⟩) job.notes }
  | stage => stage

/-- Whether anything is still proposed that has not been tried. -/
def Stage.filling : Stage → Bool
  | .going job => !job.filling.rest.isEmpty
  | .goingFast job => !job.rest.isEmpty
  | .done .. => false

/-- How many more steps reach an answer when none is cut: one for each transaction still proposed, and one
to end the block. -/
def Stage.left : Stage → Nat
  | .going job => job.filling.rest.length + 1
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
  | .going _ | .goingFast _ => ({ status := 4 }, #[], "")

/-- The answer to a request to build, when `over` is asked before each transaction whether to stop. -/
def runWith {m : Type → Type} [Monad m] (over : m Bool) (r : Request) : m (Response × Array Note × String) := do
  let stage := begin r
  return (← stage.finishWith over stage.left).answer

def runWithNotes (r : Request) : Response × Array Note × String :=
  Id.run (runWith (pure false) r)

def run (r : Request) : Response := (runWithNotes r).1

def serve (input : ByteArray) : ByteArray :=
  match (request input).run 0 with
  | some (r, pos) => if pos = input.size then (run r).encode else ({ status := 5 } : Response).encode
  | none => ({ status := 5 } : Response).encode

end Evm.Build

/-- Any kind of request, told apart by how it begins: a chain with its whole state (`Evm.Service`), one
block with a witness to be checked (`Evm.Stateless`, or by the fast engine `Evm.Engine`), or the makings of
a block to be built. -/
def Evm.serve (input : ByteArray) : ByteArray :=
  if input.extract 0 Evm.Build.magic.size == Evm.Build.magic
      || input.extract 0 Evm.Build.magicFast.size == Evm.Build.magicFast then Evm.Build.serve input
  else if input.extract 0 Evm.Engine.magic.size == Evm.Engine.magic then Evm.Engine.serve input
  else if input.extract 0 Evm.Stateless.magic.size == Evm.Stateless.magic then Evm.Stateless.serve input
  else Evm.Service.serve input
