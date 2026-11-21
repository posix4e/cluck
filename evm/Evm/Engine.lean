import Evm.Bridge

/-! A block with a witness, judged by the fast engine.

    "JWIF1", then everything a stateless request has after its own five bytes (`Evm/Stateless.lean`)

The answer has the same shape and the same statuses. What differs is who runs the block: the engine of
`Fast/`, on the state the witness gives, with Jaune still deciding what does not need the state (the
header against its parent, the size of the block, the decoding of transactions) and still supplying the
precompiled contracts and three of the roots.

One status means more here. Jaune, rejecting a block while it runs, cannot say what it had read by then,
so that rejection is answered 8, no verdict. The engine hands back its world with a refusal, and what it
fetched is exactly what that world holds: if all of it was supplied or proven absent the refusal stands
and is answered 3, and if not it is answered 6 like any other short witness. -/
open Jaune

namespace Evm.Engine

def magic : ByteArray := "JWIF1".toUTF8

/-- Everything the engine fetched, as `Evm.Stateless.checkReads` takes it. -/
def fetched (world : Fast.World) : List Address × List (Address × U256) :=
  (world.accounts.fold (fun all a _ => Bridge.address a :: all) [],
   world.slots.fold (fun all name _ => (Bridge.address name.address, Bridge.u256 name.key) :: all) [])

def validate (r : Stateless.Request) (fork : Fork) (parent : Header) (ancestors : List Header) (block : Block)
    (blockHash : U256) : Stateless.M Stateless.Verdict := do
  let rules := fork.ruleSet
  if let .error e := checkBlockRlpSize rules.block r.block.size then
    return ⟨3, 0, (TransitionError.block e).render⟩
  let known ← Stateless.materialise r parent.stateRoot
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := known.state, chainId := r.chainId }
  -- None of these reads the state: a rejection here stands whatever the witness holds.
  if let .error e := validateHeader rules chain block.header then return ⟨Stateless.refused e, 0, e.render⟩
  if let .error e := checkBlockOmmers rules chain block.header block.ommers then
    return ⟨Stateless.refused e, 0, e.render⟩
  let decoded ← match block.transactions.mapM (decodeTransaction rules) with
    | .ok decoded => pure decoded
    | .error e => return ⟨Stateless.refused e, 0, e.render⟩
  let some body := Bridge.body fork r.chainId block decoded
    | return ⟨3, 0, "a transaction with no sender, for another chain, or with a number too big to be one"⟩
  let blk := Bridge.environment fork r.chainId block.header ancestors
  match Fast.runBlock blk (Bridge.host fork) body ByteArray.empty (Fast.World.new (Bridge.backing known)) with
  | .error (why, world) =>
    -- The refusal stands only if it was reached on answers that were proven.
    let (accounts, slots) := fetched world
    Stateless.checkReads known accounts slots
    return ⟨3, 0, why⟩
  | .ok out =>
    let stateRoot ← Bridge.rootAfter known out.world
    let (receiptsRoot, bloom) := Bridge.receiptsRootAndBloom out.receipts
    -- The roots that depend on the block's body alone, by Jaune's functions on what it would have kept.
    let kept : BlockOutput :=
      { BlockOutput.init with
        blockGasUsed := out.gasUsed.toNat
        blobGasUsed := (out.blobs * Fast.gasPerBlob).toNat
        transactionsTrie := decoded.zipIdx.foldl (fun trie (tx, index) =>
          trie.insert (Rlp.Item.bytes index.toBytes).toBytes tx) BlockOutput.init.transactionsTrie
        withdrawalsTrie := processWithdrawalsTrie BlockOutput.init.withdrawalsTrie block.withdrawals }
    let requestsHash :=
      if rules.header.requestsHash then some (computeRequestsHash (out.requests.toList.map (·.toList))) else none
    match stateTransitionChecks kept block.header (getTransactionsRoot kept) stateRoot receiptsRoot bloom
        (getWithdrawalsRoot kept) requestsHash with
    | .error e => return ⟨3, 0, (TransitionError.block e).render⟩
    | .ok () => return ⟨0, blockHash, ""⟩

def runWithReason (r : Stateless.Request) : Service.Response × String := Stateless.runWithReasonBy validate r

/-- A request for the engine is a stateless request under another name. -/
def serve (input : ByteArray) : ByteArray :=
  let asStateless := Stateless.magic ++ input.extract magic.size input.size
  match (Stateless.request asStateless).run 0 with
  | some (r, pos) =>
    if pos = asStateless.size then (runWithReason r).1.encode else (⟨5, 0, 0, 0⟩ : Service.Response).encode
  | none => (⟨5, 0, 0, 0⟩ : Service.Response).encode

end Evm.Engine
