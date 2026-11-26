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

/-- Whether the engine has this fork's rules: Prague and what has come after it on mainnet. An earlier
fork's blocks are not the engine's to judge or to build, and it must say so, not run them by later rules. -/
def supported (fork : Fork) : Bool :=
  match fork with
  | .prague | .osaka | .bpo1 | .bpo2 => true
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

/-- What one call of a precompiled contract costs this builder: microseconds on the runtime it has in a
trust domain, as `precompile-time` measured them there on 2026-11-25, rounded up. Gas is no guide. It is
priced for arithmetic written for the purpose in machine code, and most of these are Jaune's, on whole
numbers of any size: a transaction of all the gas one may have, spent on recovering signers or adding
points or small powers, took four to six seconds, which a node runs in a few hundredths of one. The
point evaluation (0x0a) and BLS12-381's pairing (0x0f) cost seconds a call. Those of BLS12-381 that were
not measured (0x0d, 0x0e, 0x0f, 0x11) are put above the ones that were. Not counted: what a transaction
does outside these contracts, which gas does bound, less closely. -/
def work (a : Fast.Word) (input : ByteArray) : UInt64 :=
  let size := input.size.toUInt64
  let words := (size + 31) / 32
  -- A length as the power contract reads it: 32 bytes, the highest first, absent ones nothing. More than
  -- 1,024 is refused by the contract or priced out of any block, and counts as that here.
  let lengthAt (at_ : Nat) : UInt64 :=
    let n := (List.range 32).foldl (fun n i => if n > 1024 then n else n * 256 + (input.data.getD (at_ + i) 0).toNat) 0
    (min n 1024).toUInt64
  let n := a.w0
  if n == 1 then 800
  else if n == 2 then 10 + 2 * words
  else if n == 3 then 20 + 6 * words
  else if n == 4 then 1 + words / 64
  else if n == 5 then
    -- Squarings and multiplications of numbers of `limbs` 64-bit words, one or two for each bit of the
    -- exponent. For each bit, in hundredths of a microsecond: 8 for each pair of words, 25 a word, 100.
    let limbs := (max (lengthAt 0) (lengthAt 64) + 7) / 8
    100 + (8 * limbs * limbs + 25 * limbs + 100) * (8 * lengthAt 32 + 8) / 100
  else if n == 6 then 40
  else if n == 7 then 650
  else if n == 8 then 100 + 3300 * (size / 192)
  else if n == 9 then
    5 + ((List.range 4).foldl (fun r i => r * 256 + (input.data.getD i 0).toNat) 0).toUInt64 / 20
  else if n == 0x0a then 3500000
  else if n == 0x0b then 500
  else if n == 0x0c then 35000 * max 1 (size / 160)
  else if n == 0x0d then 2500
  else if n == 0x0e then 150000 * max 1 (size / 288)
  else if n == 0x0f then 2000000 * max 1 (size / 384)
  else if n == 0x10 then 6000
  else if n == 0x11 then 40000
  else if n == 0x100 then 300
  else 0

/-- The engine's host: the precompiled contracts the engine has of its own (the three on bn254, and the
one that hands its input back), at the prices the fork's rules give, and Jaune's for the rest. A contract
that is given too little gas, or input that is not what it takes, fails and keeps all it was given. -/
def host (fork : Fork) : Fast.Host :=
  let jaune := jauneHost fork
  let prices := fork.ruleSet.bn254
  let failed : Fast.Precompiled := ⟨false, 0, ByteArray.empty⟩
  let word (b : Bool) : ByteArray := (ByteArray.mk (Array.replicate 31 0)).push (if b then 1 else 0)
  { isPrecompile := jaune.isPrecompile
    work
    precompile := fun a input gas =>
      if a.w0 == 4 then
        -- The input, as it is: 15 gas and 3 for each 32 bytes begun. (Jaune's took 33 ms over a megabyte,
        -- by way of a list.)
        let cost := 15 + 3 * ((input.size.toUInt64 + 31) / 32)
        if gas < cost then failed else ⟨true, gas - cost, input⟩
      else if a.w0 == 6 then
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

/-- A witness as the engine reads it: the nodes by their hashes, the root they hang from, and the codes by
theirs. No address and no slot number has to be supplied with it: the engine knows what it is asking for,
and hashes that. -/
structure Witness where
  store : Trie.Store
  root : U256
  codes : Std.HashMap Fast.Word ByteArray

/-- Where an address or a slot's number lies in a trie: the nibbles of its hash. -/
def pathOf (bytes : ByteArray) : Trie.Path := Trie.nibbles (Fast.Keccak.hash bytes 0 bytes.size).bytes

/-- The nodes and codes of a request, added to any already held by their hashes (`held`, `heldCodes`:
none unless the caller has some). What is held is found by hash as what the request gives is, so it
proves exactly as much. -/
def Witness.of (r : Stateless.Request) (root : U256) (held : Trie.Store := .empty)
    (heldCodes : Std.HashMap Fast.Word ByteArray := {}) : Witness :=
  { store := r.nodes.foldl (fun store node => store.insert (Trie.hashOf node) node) held, root,
    codes := r.codes.foldl (fun codes code => codes.insert (Fast.keccak code) code) heldCodes }

/-- A witness as what stands behind the engine's world. Each question is answered from the trie when it is
asked: an account or a slot is found, or proven not to be there, or the witness does not reach it (or what
it holds there does not read), which is `missing`. Nothing is answered by default. -/
def Witness.backing (w : Witness) : Fast.Backing :=
  { account := fun a =>
      match Trie.get w.store (.sealed w.root) (pathOf a.addressBytes) with
      | .ok (some bytes) =>
        match Stateless.Leaf.read bytes with
        | some leaf =>
          .found ⟨leaf.nonce, word leaf.balance, word leaf.codeHash, leaf.storageRoot == Trie.emptyRoot,
                  word leaf.storageRoot⟩
        | none => .missing
      | .ok none => .absent
      | .error _ => .missing
    slot := fun storageRoot key =>
      match Trie.get w.store (.sealed (u256 storageRoot)) (pathOf key.bytes) with
      | .ok (some bytes) =>
        match Trie.string bytes with
        | some value =>
          if value.size == 0 || value.size > 32 || value[0]! == 0 then .missing
          else .found (Fast.wordAt ((ByteArray.mk (Array.replicate (32 - value.size) 0)) ++ value) Fast.Word.zero)
        | none => .missing
      | .ok none => .absent
      | .error _ => .missing
    code := fun hash => w.codes[hash]? }

/-- Why the engine could not go on: what the witness lacks at the address or code hash the engine's world
names. The lookup is done again here, for the trie's own account of what is missing. -/
def Witness.shortfall (w : Witness) (world : Fast.World) : Stateless.Shortfall :=
  match Trie.get w.store (.sealed w.root) (pathOf world.lacking.addressBytes) with
  | .error (.missing hash) => .lacking hash s!"account {(u256 world.lacking).toHex}, which the block read"
  | .error _ => .malformed
  | .ok _ => .lacking 0 s!"a code or a slot of storage under {(u256 world.lacking).toHex}, which the block read"

def accessList (list : AccessList) : Array (Fast.Word × Array Fast.Word) :=
  list.toArray.map fun (a, keys) => (addressWord a, keys.toArray.map word)

/-- A transaction as the engine takes it, given who sent it, with the signers of its authorizations
recovered by Jaune. None when a number in it is too big to be real. -/
def transactionFrom (tx : Transaction) (sender : Address) : Option Fast.Tx := do
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

/-- A transaction as the engine takes it, its sender recovered by Jaune. None when there is no sender. -/
def transaction (chainId : UInt64) (tx : Transaction) : Option Fast.Tx := do
  transactionFrom tx (← (recoverSender chainId tx).toOption)

/-- What the block fixes, from its header and the headers before it. -/
def environment (fork : Fork) (chainId : UInt64) (header : Header) (ancestors : List Header)
    (named : List U256 := ancestors.map (·.hash)) : Fast.BlockEnv :=
  -- `named` is each ancestor's hash, for a caller that has them already: 255 headers are not hashed twice.
  let hashes : Std.HashMap UInt64 Fast.Word :=
    (ancestors.zip named).foldl (fun hashes (h, hash) => hashes.insert h.number.toUInt64 (word hash)) {}
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

/-- The root of the receipts and the bloom of all their logs, as a header has them, by Jaune's functions.
What `receiptsRootAndBloom` below has to give; `build-test` compares the two on blocks of mainnet. -/
def receiptsRootAndBloomByJaune (receipts : Array Fast.Receipt) : U256 × Bytes :=
  let entries := receipts.toList.zipIdx.map fun (r, index) =>
    let logs := r.logs.toList.map log
    let receipt : Receipt := ⟨r.success, r.cumulativeGas.toNat, logsBloom logs, logs⟩
    let key : Bytes := Rlp.Item.toBytes (.bytes index.toBytes)
    (key.toNibbles, r.kind.toNat.toBytes ++ receipt.toRlpItem.toBytes)
  (trie (Std.TreeMap.ofList entries _), logsBloom (receipts.toList.flatMap fun r => r.logs.toList.map log))

/-- A bloom with nothing in it: 2048 bits. -/
def noBloom : ByteArray := ByteArray.mk (Array.replicate 256 0)

/-- A bloom with one more thing in it, an address or a topic: three bits, each named by eleven bits of
the thing's keccak hash (the low eleven of its first, second and third pairs of bytes), counted from
the bloom's last byte. -/
def bloomWith (bloom : ByteArray) (item : ByteArray) : ByteArray :=
  let digest := (Fast.Keccak.hash item 0 item.size).bytes
  (#[0, 2, 4] : Array Nat).foldl (fun bloom i =>
    let bit := ((digest[i]!.toNat <<< 8) ||| digest[i + 1]!.toNat) % 2048
    let place := 255 - bit / 8
    bloom.set! place (bloom[place]! ||| (1 <<< (bit % 8)).toUInt8)) bloom

/-- The bloom of some logs: each one's address and each of its topics. -/
def bloomOf (logs : Array Fast.Log) : ByteArray :=
  logs.foldl (fun bloom log =>
    log.topics.foldl (fun bloom topic => bloomWith bloom topic.bytes) (bloomWith bloom log.address.addressBytes)) noBloom

/-- A number below 2^64 as RLP writes one: its bytes, highest first, with none that are nothing in front. -/
def numberBytes (n : Nat) : ByteArray :=
  ⟨(((List.range 8).reverse.map fun k => (n >>> (8 * k)).toUInt8).dropWhile (· == 0)).toArray⟩

/-- A receipt as the receipts' trie holds it: for any kind but the first, the kind's byte; then the list
of whether it succeeded, the gas the block had used after it, its bloom, and its logs, each an address,
topics and data. -/
def receiptBytes (r : Fast.Receipt) (bloom : ByteArray) : ByteArray :=
  let logs := r.logs.foldl (fun out log =>
    out ++ Trie.rlpList (Trie.rlpString log.address.addressBytes
      ++ Trie.rlpList (log.topics.foldl (fun out topic => out ++ Trie.rlpString topic.bytes) ByteArray.empty)
      ++ Trie.rlpString log.data)) ByteArray.empty
  let body := Trie.rlpList (Trie.rlpString (if r.success then ⟨#[1]⟩ else ByteArray.empty)
    ++ Trie.rlpString (numberBytes r.cumulativeGas.toNat) ++ Trie.rlpString bloom ++ Trie.rlpList logs)
  if r.kind == 0 then body else ByteArray.mk #[r.kind] ++ body

/-- The root of the receipts and the bloom of all their logs, as a header has them: each receipt under
its number as RLP writes it, in a trie of this project's (`Evm/Trie.lean`), hashed by its keccak. Until
2026-11-26 this was Jaune's functions on lists of bytes (above), a tenth of what a block cost to build
on a workstation and more in a machine. -/
def receiptsRootAndBloom (receipts : Array Fast.Receipt) : U256 × Bytes :=
  let (trie, bloom, _) := receipts.foldl
    (init := ((.ok .empty : Except Trie.Fault Trie.Node), noBloom, 0))
    fun (trie, bloom, index) r =>
      let own := bloomOf r.logs
      (trie.bind fun node =>
          Trie.set {} node (Trie.nibbles (Trie.rlpString (numberBytes index))) (receiptBytes r own),
        ByteArray.mk (Array.zipWith (· ||| ·) bloom.data own.data), index + 1)
  match trie with
  | .ok node => (Trie.rootHash node, bloom.toList)
  -- No two numbers' writings begin alike, so the trie takes every one; this is not reached.
  | .error _ => receiptsRootAndBloomByJaune receipts

/-- The root of a block's transactions, each as it goes on the wire, under its number as RLP writes it,
in this project's trie: what Jaune's `getTransactionsRoot` gives of the same transactions decoded, which
writes each one out again to put it in its own trie. -/
def transactionsRoot (wires : Array ByteArray) : Option U256 :=
  let trie := wires.zipIdx.foldl (init := (.ok .empty : Except Trie.Fault Trie.Node)) fun trie (wire, index) =>
    trie.bind fun node => Trie.set {} node (Trie.nibbles (Trie.rlpString (numberBytes index))) wire
  match trie with
  | .ok node => if wires.any (·.isEmpty) then none else some (Trie.rootHash node)
  | .error _ => none

/-- The state root after the engine has run a block on a witness: the parent's trie with every account
that changed written back. Everything the engine fetched was proven when it was fetched, so there is
nothing left to check about what it read; a world marked as having asked for what the witness lacks must
not be brought here.

With `keep`, the nodes the block wrote are given too: the encoding of every node of the state's trie and of
the accounts' storage tries that is not as it was before the block. They are what somebody holding a proof
of an account or a slot before the block needs, and all they need, to have a proof of it after
(`Evm/Follow.lean`). -/
def rootAndNodes (w : Witness) (world : Fast.World) (keep : Bool) : Stateless.M (U256 × Array ByteArray) := do
  -- The slots that hold something other than they did before the block, by whose they are.
  let changed : Std.HashMap Fast.Word (Array (Fast.Word × Fast.Word)) :=
    world.slots.fold (fun changed name slot =>
      if slot.value == slot.before then changed
      else changed.insert name.address ((changed.getD name.address #[]).push (name.key, slot.value))) {}
  -- A value that is something is written without first being looked for, when the nodes written are
  -- not wanted: `Trie.put` looks first so as to leave a trie that already holds the value as it was,
  -- sealed, and writing the same value again gives the same root by another walk down and up. With
  -- `keep` the looking stays, so that what is given as written is only what changed. (Looking first
  -- was a third of what a state root cost.)
  let write (trie : Trie.Node) (path : Trie.Path) (value : ByteArray) : Except Trie.Fault Trie.Node :=
    if keep || value.isEmpty then Trie.put w.store trie path value else Trie.set w.store trie path value
  let mut trie : Trie.Node := .sealed w.root
  let mut written : Array ByteArray := #[]
  for (a, account) in world.accounts.toList do
    let slots := changed.getD a #[]
    if !account.dirty && slots.isEmpty then continue
    let key := pathOf a.addressBytes
    if !account.present then
      if account.existed then trie ← Stateless.ofTrie (Trie.remove w.store trie key)
      continue
    -- An account made in the block starts with no storage, whatever was at its address before.
    let mut storage : Trie.Node :=
      .sealed (if account.fresh || !account.existed then Trie.emptyRoot else u256 account.storage)
    for (slot, value) in slots do
      let path := pathOf slot.bytes
      storage ← Stateless.ofTrie <|
        if value.isZero then Trie.remove w.store storage path
        else write storage path (Stateless.slotValue (u256 value))
    if keep then written := Trie.encodings storage written
    let leaf : Stateless.Leaf := ⟨account.nonce, u256 account.balance, Trie.rootHash storage, u256 account.codeHash⟩
    trie ← Stateless.ofTrie (write trie key leaf.write)
  pure (Trie.rootHash trie, if keep then Trie.encodings trie written else written)

def rootAfter (w : Witness) (world : Fast.World) : Stateless.M U256 := do
  return (← rootAndNodes w world false).1

/-- What a state root was worked out with, kept so that the next one for the same block with more in it
goes on from there (`rootGoingOn`): the state's trie as it was written, open in memory as far as the
accounts written reach; what was written for each account, and for each slot; and the storage of each
account that had a slot written, as a trie and its root. All of it is this program's own working, from
a witness's nodes; none of it is given by anyone. -/
structure Rooted where
  trie : Trie.Node
  /-- Each account written, with its leaf as written; no bytes for one taken out of the state. -/
  leaves : Std.HashMap Fast.Word ByteArray := {}
  /-- For each account that existed before the block and had a slot written: its storage, and the root. -/
  storage : Std.HashMap Fast.Word (Trie.Node × U256) := {}
  /-- Each slot written, with the value written. -/
  slots : Std.HashMap Fast.SlotKey Fast.Word := {}

/-- The state root after the engine has run a block, as `rootAfter` gives it, worked out from where the
last one for the same block was (`was`: the block with fewer transactions in it, on the same parent)
and not from the parent's trie: only the accounts and slots that are not as they were last written are
written, and the storage tries nothing was written to are not hashed again. Beside the root, what to
go on from next time. With nothing to go on from it writes everything, as `rootAfter` does.

What makes it the same root: a trie written with the same leaves is the same trie however many steps
it was written in. Each account the world has changed, or that was written before, is written again
wherever its leaf is not the leaf last written; each slot likewise, against the value last written or,
when it never was, the value before the block. An account that was not in the state before the block,
or was made in it, has its storage built from nothing every time, from all it holds: that is all in the
world, and nothing is carried over for it.

`none` when what was written before is not all in this world to be looked at again (an account or a
slot then written that this world has not fetched): the caller works the root out whole. That is not
expected, the world being the one those were written from with more done to it. -/
def rootGoingOn (w : Witness) (world : Fast.World) (was : Option Rooted) : Stateless.M (Option (U256 × Rooted)) := do
  let was := was.getD { trie := .sealed w.root }
  -- The slots that hold something other than was last written, by whose they are; all that hold
  -- anything, by whose they are; and how many of those written before are here.
  let (changed, held, met) := world.slots.fold
    (init := (({} : Std.HashMap Fast.Word (Array (Fast.Word × Fast.Word))),
              ({} : Std.HashMap Fast.Word (Array (Fast.Word × Fast.Word))), 0))
    fun (changed, held, met) name slot =>
      let written := was.slots[name]?
      let last := written.getD slot.before
      (if slot.value == last then changed
        else changed.insert name.address ((changed.getD name.address #[]).push (name.key, slot.value)),
       if slot.value.isZero then held
        else held.insert name.address ((held.getD name.address #[]).push (name.key, slot.value)),
       if written.isSome then met + 1 else met)
  if met != was.slots.size then return none
  let writeAll (storage : Trie.Node) (slots : Array (Fast.Word × Fast.Word)) : Except Trie.Fault Trie.Node :=
    slots.foldlM (fun storage (slot, value) =>
      let path := pathOf slot.bytes
      if value.isZero then Trie.remove w.store storage path
      else Trie.set w.store storage path (Stateless.slotValue (u256 value))) storage
  let mut trie := was.trie
  let mut leaves := was.leaves
  let mut storages := was.storage
  let mut slots := was.slots
  let mut seen := 0
  for (a, account) in world.accounts.toList do
    let news := changed.getD a #[]
    let before := leaves[a]?
    if before.isSome then seen := seen + 1
    if !account.dirty && news.isEmpty && before.isNone then continue
    for (slot, value) in news do
      slots := slots.insert ⟨a, slot⟩ value
    let key := pathOf a.addressBytes
    if !account.present then
      if before != some ByteArray.empty then
        if account.existed || before.isSome then trie ← Stateless.ofTrie (Trie.remove w.store trie key)
        leaves := leaves.insert a ByteArray.empty
        storages := storages.erase a
      continue
    let storageRoot ←
      if account.fresh || !account.existed then
        -- Everything it holds is in the world: built from nothing, and nothing kept of it.
        storages := storages.erase a
        pure (Trie.rootHash (← Stateless.ofTrie (writeAll (.sealed Trie.emptyRoot) (held.getD a #[]))))
      else
        match storages[a]? with
        | some (storage, root) =>
          if news.isEmpty then pure root else
          let storage ← Stateless.ofTrie (writeAll storage news)
          let root := Trie.rootHash storage
          storages := storages.insert a (storage, root)
          pure root
        | none =>
          if news.isEmpty then pure (u256 account.storage) else
          let storage ← Stateless.ofTrie (writeAll (.sealed (u256 account.storage)) news)
          let root := Trie.rootHash storage
          storages := storages.insert a (storage, root)
          pure root
    let leaf := (⟨account.nonce, u256 account.balance, storageRoot, u256 account.codeHash⟩ : Stateless.Leaf).write
    if before == some leaf then continue
    trie ← Stateless.ofTrie (Trie.set w.store trie key leaf)
    leaves := leaves.insert a leaf
  if seen != was.leaves.size then return none
  pure (some (Trie.rootHash trie, { trie, leaves, storage := storages, slots }))

end Evm.Bridge
