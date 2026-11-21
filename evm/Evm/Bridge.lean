import Evm.Stateless
import Fast.Block
import Fast.Bn254

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

/-- Jaune's precompiled contracts as a host: every one of them, each call going through lists of bytes both
ways. What the engine's own are held to. -/
def jauneHost (fork : Fork) : Fast.Host :=
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

/-- The engine's host: the precompiled contracts the engine has of its own (the three on bn254), at the
prices the fork's rules give, and Jaune's for the rest. A contract that is given too little gas, or input
that is not what it takes, fails and keeps all it was given. -/
def host (fork : Fork) : Fast.Host :=
  let jaune := jauneHost fork
  let prices := fork.ruleSet.bn254
  let failed : Fast.Precompiled := ⟨false, 0, ByteArray.empty⟩
  let word (b : Bool) : ByteArray := (ByteArray.mk (Array.replicate 31 0)).push (if b then 1 else 0)
  { isPrecompile := jaune.isPrecompile
    precompile := fun a input gas =>
      if a.w0 == 6 then
        let cost := prices.add.toUInt64
        if gas < cost then failed else
        match Fast.Bn254.addPoints input with
        | some out => ⟨true, gas - cost, out⟩
        | none => failed
      else if a.w0 == 7 then
        let cost := prices.mul.toUInt64
        if gas < cost then failed else
        match Fast.Bn254.mulPoint input with
        | some out => ⟨true, gas - cost, out⟩
        | none => failed
      else if a.w0 == 8 then
        let cost := (prices.pairingPerPair * (input.size / 192) + prices.pairingBase).toUInt64
        if gas < cost then failed else
        match Fast.Bn254.pairingCheck input with
        | some holds => ⟨true, gas - cost, word holds⟩
        | none => failed
      else jaune.precompile a input gas }

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

/-- The chain a typed transaction says it is for; a legacy one says it in its signature, which recovering
its sender has checked. -/
def chainOf (tx : Transaction) : Option UInt64 :=
  match tx.type with
  | .legacy _ _ => none
  | .eip2930 chain _ _ _ => some chain
  | .eip1559 chain _ _ _ _ => some chain
  | .eip4844 chain _ _ _ _ _ _ => some chain
  | .eip7702 chain _ _ _ _ _ => some chain

/-- A block's body as the engine takes it, from its transactions as Jaune decoded them. None when one has no
sender, is for another chain, or holds a number too big to be real. -/
def body (fork : Fork) (chainId : UInt64) (block : Block) (decoded : List Transaction) : Option Fast.BlockInput := do
  let rules := fork.ruleSet
  let txs ← decoded.mapM fun tx => do
    if (chainOf tx).any (· != chainId) then none
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

/-- Where an address or a slot's number lies in a trie: the nibbles of its hash. -/
def pathOf (bytes : ByteArray) : Trie.Path := Trie.nibbles (Fast.Keccak.hash bytes 0 bytes.size).bytes

/-- The state root after the engine has run a block on what a witness gave: first that everything the
engine fetched was supplied or is proven not to be there (what it fetched is exactly what its world holds),
then the parent's trie with every account that changed written back. -/
def rootAfter (known : Stateless.Known) (world : Fast.World) : Stateless.M U256 := do
  Stateless.checkReads known (world.accounts.fold (fun all a _ => address a :: all) [])
    (world.slots.fold (fun all name _ => (address name.address, u256 name.key) :: all) [])
  -- The slots that hold something other than they did before the block, by whose they are.
  let changed : Std.HashMap Fast.Word (Array (Fast.Word × Fast.Word)) :=
    world.slots.fold (fun changed name slot =>
      if slot.value == slot.before then changed
      else changed.insert name.address ((changed.getD name.address #[]).push (name.key, slot.value))) {}
  let mut trie : Trie.Node := .sealed known.root
  for (a, account) in world.accounts.toList do
    let slots := changed.getD a #[]
    if !account.dirty && slots.isEmpty then continue
    let leaf := known.leaves.get? (address a)
    let key := pathOf a.addressBytes
    if !account.present then
      if leaf.isSome then trie ← Stateless.ofTrie (Trie.remove known.store trie key)
      continue
    -- An account made in the block starts with no storage, whatever was at its address before.
    let mut storage : Trie.Node :=
      .sealed (if account.fresh then Trie.emptyRoot else (leaf.map (·.storageRoot)).getD Trie.emptyRoot)
    for (slot, value) in slots do
      let path := pathOf slot.bytes
      storage ← Stateless.ofTrie <|
        if value.isZero then Trie.remove known.store storage path
        else Trie.put known.store storage path (Stateless.slotValue (u256 value))
    let written : Stateless.Leaf := ⟨account.nonce, u256 account.balance, Trie.rootHash storage, u256 account.codeHash⟩
    trie ← Stateless.ofTrie (Trie.put known.store trie key written.write)
  pure (Trie.rootHash trie)

end Evm.Bridge
