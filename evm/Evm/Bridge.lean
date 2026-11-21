import Evm.Stateless
import Fast.Block

/-! Between Jaune's types and the fast engine's, for as long as both are here: a block as Jaune decodes it
made into what `Fast.runBlock` takes, the state a witness gave made into what stands behind the engine's
world, Jaune's precompiled contracts made into the engine's host, and what the engine's run produced made
into the roots a header commits to, by Jaune's own functions for them. Nothing in `Fast/` imports Jaune;
this file is where the two meet. -/
open Jaune

namespace Evm.Bridge

def word (x : U256) : Fast.Word := ⟨x.2.2, x.2.1, x.1.2, x.1.1⟩
def u256 (w : Fast.Word) : U256 := ⟨⟨w.w3, w.w2⟩, ⟨w.w1, w.w0⟩⟩
def addressWord (a : Address) : Fast.Word := ⟨a.2.2, a.2.1, a.1.toUInt64, 0⟩
def address (w : Fast.Word) : Address := ⟨w.w2.toUInt32, ⟨w.w1, w.w0⟩⟩

/-- Whether the fork is Osaka or one of the blob-parameter forks after it. -/
def osaka (fork : Fork) : Bool :=
  match fork with
  | .osaka | .bpo1 | .bpo2 => true
  | _ => false

/-- The addresses of the precompiled contracts at a fork. -/
def precompiles (fork : Fork) : Array Fast.Word :=
  let upTo17 := (List.range 17).toArray.map fun i => Fast.Word.ofUInt64 (i + 1).toUInt64
  if osaka fork then upTo17.push (Fast.Word.ofUInt64 0x100) else upTo17

/-- Jaune's precompiled contracts as the engine's host. Each call goes through lists of bytes both ways. -/
def host (fork : Fork) : Fast.Host :=
  let known := precompiles fork
  { isPrecompile := fun a => a.small && known.any (· == a)
    precompile := fun a input gas =>
      let stat : BenvStat := { (default : BenvStat) with fork }
      let sevm : Sevm := { (default : Sevm) with data := input.toList, benvStat := stat }
      let evm : Evm := ⟨0, sevm, (default : Devm).withGasLeft gas.toNat⟩
      match precompileRun evm (address a) with
      | .ok cost output =>
        if cost ≤ gas.toNat then ⟨true, gas - cost.toUInt64, ⟨output.toArray⟩⟩ else ⟨false, 0, ByteArray.empty⟩
      | .error _ _ => ⟨false, 0, ByteArray.empty⟩ }

/-- What a witness gave, as what stands behind the engine's world. An account or slot the witness did not
give is answered as not there: whether that was right is `Evm.Stateless.checkReads`'s to say afterwards. -/
def backing (known : Stateless.Known) : Fast.Backing :=
  let codes : Std.HashMap Fast.Word ByteArray :=
    known.state.toList.foldl (fun codes (a, account) =>
      match known.leaves.get? a with
      | some leaf => codes.insert (word leaf.codeHash) account.code
      | none => codes) {}
  { account := fun a =>
      match known.leaves.get? (address a) with
      | some leaf => .found ⟨leaf.nonce, word leaf.balance, word leaf.codeHash, leaf.storageRoot == Trie.emptyRoot⟩
      | none => .absent
    slot := fun a key =>
      match (known.state.get (address a)).storage.get? (u256 key) with
      | some value => .found (word value)
      | none => .absent
    code := fun hash => codes[hash]? }

def accessList (list : AccessList) : Array (Fast.Word × Array Fast.Word) :=
  list.toArray.map fun (a, keys) => (addressWord a, keys.toArray.map word)

/-- A transaction as the engine takes it, with its sender and the signers of its authorizations recovered
by Jaune. None when the sender cannot be recovered or a number in it is too big to be real. -/
def transaction (chainId : UInt64) (tx : Transaction) : Option Fast.Tx := do
  let sender ← (recoverSender chainId tx).toOption
  if tx.gasLimit ≥ 2 ^ 64 || tx.value ≥ 2 ^ 256 then none
  let base : Fast.Tx :=
    { kind := 0, sender := addressWord sender, callee := none, nonce := tx.nonce, gasLimit := tx.gasLimit.toUInt64,
      value := Fast.Word.ofNat tx.value, input := ⟨tx.data.toArray⟩, maxFee := Fast.Word.zero,
      maxPriorityFee := Fast.Word.zero, accessList := #[], blobHashes := #[], maxBlobFee := Fast.Word.zero,
      authorizations := #[] }
  let fee (n : Nat) : Option Fast.Word := if n < 2 ^ 256 then some (Fast.Word.ofNat n) else none
  match tx.type with
  | .legacy gasPrice dest =>
    pure { base with callee := dest.map addressWord, maxFee := ← fee gasPrice, maxPriorityFee := ← fee gasPrice }
  | .eip2930 _ gasPrice dest list =>
    pure { base with kind := 1, callee := dest.map addressWord, maxFee := ← fee gasPrice, maxPriorityFee := ← fee gasPrice,
                     accessList := accessList list }
  | .eip1559 _ tip max dest list =>
    pure { base with kind := 2, callee := dest.map addressWord, maxFee := ← fee max, maxPriorityFee := ← fee tip,
                     accessList := accessList list }
  | .eip4844 _ tip max dest list blobFee hashes =>
    pure { base with kind := 3, callee := some (addressWord dest), maxFee := ← fee max, maxPriorityFee := ← fee tip,
                     accessList := accessList list, maxBlobFee := ← fee blobFee, blobHashes := hashes.toArray.map word }
  | .eip7702 _ tip max dest list auths =>
    pure { base with kind := 4, callee := some (addressWord dest), maxFee := ← fee max, maxPriorityFee := ← fee tip,
                     accessList := accessList list,
                     authorizations := auths.toArray.map fun auth =>
                       { chainId := word auth.chainId, address := addressWord auth.address, nonce := auth.nonce,
                         authority := (recoverAuthority auth).toOption.map addressWord } }

/-- What the block fixes, from its header and the headers before it. -/
def environment (fork : Fork) (chainId : UInt64) (header : Header) (ancestors : List Header) : Fast.BlockEnv :=
  let hashes : Std.HashMap UInt64 Fast.Word :=
    ancestors.foldl (fun hashes h => hashes.insert h.number.toUInt64 (word h.hash)) {}
  -- The oldest header names its own parent, which is one more block that BLOCKHASH can reach.
  let hashes := match ancestors.head? with
    | some oldest => if oldest.number == 0 then hashes else hashes.insert (oldest.number - 1).toUInt64 (word oldest.parentHash)
    | none => hashes
  { coinbase := addressWord header.coinbase, number := header.number.toUInt64, timestamp := header.timestamp.toUInt64,
    gasLimit := header.gasLimit.toUInt64, prevRandao := word header.prevRandao,
    baseFee := Fast.Word.ofNat (header.baseFeePerGas.getD 0),
    blobBaseFee := Fast.Word.ofNat (getBaseFeePerBlobGas fork.ruleSet.blob (header.excessBlobGas.getD 0)),
    chainId, blockHash := fun n => hashes.getD n Fast.Word.zero, osaka := osaka fork }

/-- A block's body as the engine takes it. None when a transaction does not decode or has no sender. -/
def body (fork : Fork) (chainId : UInt64) (block : Block) : Option Fast.BlockInput := do
  let rules := fork.ruleSet
  let txs ← block.transactions.mapM fun slot => do
    let tx ← (decodeTransaction rules slot).toOption
    transaction chainId tx
  let maxBlobs := (rules.blob.max / 131072).toUInt64
  pure { parentHash := word block.header.parentHash,
         parentBeaconRoot := word (block.header.parentBeaconBlockRoot.getD 0),
         transactions := txs.toArray,
         withdrawals := block.withdrawals.toArray.map fun w => ⟨addressWord w.address, (w.amount.toNat).toUInt64⟩,
         maxBlobs, blobsPerTx := if osaka fork then 6 else maxBlobs, precompiles := precompiles fork }

def log (l : Fast.Log) : Log := ⟨address l.address, l.topics.toList.map u256, l.data.toList⟩

/-- The root of the receipts and the bloom of all their logs, as a header has them, by Jaune's functions. -/
def receiptsRootAndBloom (receipts : Array Fast.Receipt) : U256 × Bytes :=
  let entries := receipts.toList.zipIdx.map fun (r, index) =>
    let logs := r.logs.toList.map log
    let receipt : Receipt := ⟨r.success, r.cumulativeGas.toNat, logsBloom logs, logs⟩
    let key : Bytes := Rlp.Item.toBytes (.bytes index.toBytes)
    (key.toNibbles, r.kind.toNat.toBytes ++ receipt.toRlpItem.toBytes)
  (trie (Std.TreeMap.ofList entries _), logsBloom (receipts.toList.flatMap fun r => r.logs.toList.map log))

end Evm.Bridge
