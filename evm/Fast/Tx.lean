import Fast.Interp

/-! A transaction on the fast engine: whether it may run at all, what it pays before and after, and the
call or creation it makes. Sums of money here are worked out on `Nat`, exactly, once a transaction: a
product of a gas limit and a price a sender made up need not fit in 256 bits, and must not be allowed to
wrap round to something small. -/

namespace Fast

/-- One authorization of a set-code transaction (EIP-7702), with who signed it worked out already. -/
structure Authorization where
  chainId : Word
  address : Word
  nonce : UInt64
  /-- The signer, when the signature is one. -/
  authority : Option Word

structure Tx where
  /-- 0 legacy, 1 with an access list, 2 with a fee market, 3 with blobs, 4 setting code. -/
  kind : UInt8
  sender : Word
  /-- Whom it calls; none creates a contract. -/
  callee : Option Word
  nonce : UInt64
  gasLimit : UInt64
  value : Word
  input : ByteArray
  /-- The most it pays for gas; for the first two kinds, what it pays. -/
  maxFee : Word
  maxPriorityFee : Word
  accessList : Array (Word × Array Word)
  blobHashes : Array Word
  maxBlobFee : Word
  authorizations : Array Authorization

structure Receipt where
  kind : UInt8
  success : Bool
  /-- Gas used by the block up to and with this transaction. -/
  cumulativeGas : UInt64
  logs : Array Log

/-- The zero bytes and the others in some input. -/
def countBytes (input : @& ByteArray) : UInt64 × UInt64 :=
  go input input.size 0 0 0
where
  go (input : @& ByteArray) : Nat → USize → UInt64 → UInt64 → UInt64 × UInt64
    | 0, _, zero, other => (zero, other)
    | left + 1, i, zero, other =>
      if h : i.toNat < input.size then
        if input.uget i h == 0 then go input left (i + 1) (zero + 1) other else go input left (i + 1) zero (other + 1)
      else (zero, other)

/-- What a transaction costs before it runs anything, and the least it may be charged whatever it runs
(EIP-7623). -/
def intrinsicGas (tx : Tx) : UInt64 × UInt64 :=
  let (zero, other) := countBytes tx.input
  let tokens := zero + 4 * other
  let creation : UInt64 := if tx.callee.isNone then 32000 + 2 * wordsOf tx.input.size.toUInt64 else 0
  let keys := tx.accessList.foldl (fun n entry => n + entry.2.size) 0
  let access := 2400 * tx.accessList.size.toUInt64 + 1900 * keys.toUInt64
  (21000 + 4 * tokens + creation + access + 25000 * tx.authorizations.size.toUInt64, 21000 + 10 * tokens)

/-- The gas one blob takes. -/
def gasPerBlob : UInt64 := 131072

/-- The code an account that has delegated holds: three bytes that say so, then the address. -/
def delegation (address : Word) : ByteArray := (ByteArray.mk #[0xef, 0x01, 0x00]) ++ address.addressBytes

/-- The authorizations of a set-code transaction, each applied if it is good and passed over if not. -/
def authorize (chainId : UInt64) (world : World) (list : Array Authorization) : World :=
  list.foldl (fun world auth =>
    if !(auth.chainId.isZero || auth.chainId == Word.ofUInt64 chainId) || auth.nonce == 0xffffffffffffffff then world else
    match auth.authority with
    | none => world
    | some authority =>
      let (world, _) := world.warm authority
      let (world, account) := world.withCode authority
      if account.code.size != 0 && (delegate? account.code).isNone then world
      else if account.nonce != auth.nonce then world
      else
        -- An account already in the state was charged, in the transaction's price, as if it were new.
        let world := if account.present then world.addRefund 12500 else world
        let world := world.setCode authority (if auth.address.isZero then ByteArray.empty else delegation auth.address)
        world.setNonce authority (auth.nonce + 1)) world

/-- What the block allows a transaction that is not fixed by the block's own fields. -/
structure Allowance where
  /-- Gas the block has left. -/
  gas : UInt64
  /-- Blobs the block has room for. -/
  blobs : UInt64
  /-- Blobs one transaction may carry. -/
  blobsPerTx : UInt64
  /-- Addresses that are warm in every transaction: the precompiled contracts. -/
  alwaysWarm : Array Word

/-- A transaction run. An error is the transaction being one the block may not hold, in which case nothing
was changed and the world and the stack come back with the reason; otherwise the world after it, the stack
given back, and its receipt (with `cumulativeGas` holding only this transaction's gas, for the caller to
add up). -/
def process (blk : @& BlockEnv) (host : @& Host) (allowed : @& Allowance) (tx : @& Tx) (stack : ByteArray) (world : World) :
    Except (String × World × ByteArray) (World × ByteArray × Receipt) :=
  let (intrinsic, floor) := intrinsicGas tx
  if tx.gasLimit < max intrinsic floor then .error ("less gas than the transaction costs before it runs", world, stack) else
  if tx.callee.isNone && tx.input.size > 49152 then .error ("more code than a creation may carry", world, stack) else
  if blk.osaka && tx.gasLimit > 16777216 then .error ("more gas than a transaction may have", world, stack) else
  if tx.gasLimit > allowed.gas then .error ("more gas than the block has left", world, stack) else
  let baseFee := blk.baseFee.toNat
  let maxFee := tx.maxFee.toNat
  let tip := tx.maxPriorityFee.toNat
  if maxFee < baseFee then .error ("a price under the block's base fee", world, stack) else
  if tx.kind ≥ 2 && tip > maxFee then .error ("a tip above the price", world, stack) else
  let price := if tx.kind ≥ 2 then min maxFee (baseFee + tip) else maxFee
  let blobs := tx.blobHashes.size.toUInt64
  if tx.kind == 3 && (tx.callee.isNone || blobs == 0 || blobs > allowed.blobs || blobs > allowed.blobsPerTx ||
      tx.blobHashes.any (fun h => h.w3 >>> 56 != 1) || tx.maxBlobFee.toNat < blk.blobBaseFee.toNat) then
    .error ("blobs it may not carry, or a price for them under the block's", world, stack) else
  if tx.kind == 4 && (tx.callee.isNone || tx.authorizations.size == 0) then .error ("a set-code transaction with nothing to set", world, stack) else
  let (world, sender) := world.withCode tx.sender
  if sender.nonce != tx.nonce then .error (s!"nonce {tx.nonce.toNat} where the sender's is {sender.nonce.toNat}", world, stack) else
  if sender.nonce == 0xffffffffffffffff then .error ("a sender whose nonce is at its end", world, stack) else
  if sender.code.size != 0 && (delegate? sender.code).isNone then .error ("a sender that is a contract", world, stack) else
  let blobGas := (gasPerBlob * blobs).toNat
  if sender.balance.toNat < tx.gasLimit.toNat * maxFee + tx.value.toNat + blobGas * tx.maxBlobFee.toNat then
    .error ("a sender who cannot pay for it", world, stack) else
  -- From here on the transaction is in the block whatever happens to what it runs.
  let world := world.debit tx.sender (Word.ofNat (tx.gasLimit.toNat * price + blobGas * blk.blobBaseFee.toNat))
  let world := world.setNonce tx.sender (tx.nonce + 1)
  let (world, _) := world.warm tx.sender
  let (world, _) := world.warm blk.coinbase
  let world := allowed.alwaysWarm.foldl (fun world a => (world.warm a).1) world
  let world := tx.accessList.foldl (fun world entry =>
    entry.2.foldl (fun world key => world.warmSlotOnly entry.1 key) (world.warm entry.1).1) world
  let world := authorize blk.chainId world tx.authorizations
  let gas := tx.gasLimit - intrinsic
  let env : TxEnv := { origin := tx.sender, gasPrice := Word.ofNat price, blobHashes := tx.blobHashes }
  let mark := world.checkpoint
  let out : Outcome :=
    match tx.callee with
    | some to =>
      let (world, _) := world.warm to
      let world := (world.debit tx.sender tx.value).credit to tx.value
      let (world, account) := world.withCode to
      -- Code that is a delegation runs the code of the account it names, which is made warm by that.
      let (world, code, codeHash) : World × ByteArray × Word :=
        match delegate? account.code with
        | some named =>
          let (world, _) := world.warm named
          let (world, namedAccount) := world.withCode named
          (world, namedAccount.code, namedAccount.codeHash)
        | none => (world, account.code, account.codeHash)
      if host.isPrecompile to then
        let answer := host.precompile to tx.input gas
        if answer.success then ⟨0, answer.gasLeft, answer.output, stack, world⟩ else lost stack world
      else if code.size == 0 then ⟨0, gas, ByteArray.empty, stack, world⟩
      else
        let (world, jumps) := world.jumpsOf codeHash code
        execute blk env host
          { address := to, caller := tx.sender, value := tx.value, input := tx.input, code, jumps, static := false,
            depth := 0, base := 0 } stack gas world
    | none =>
      let target := createAddress tx.sender tx.nonce
      let (world, _) := world.warm target
      let (world, there) := world.account target
      if there.nonce != 0 || there.codeHash != emptyCodeHash || !(there.fresh || there.storageWasEmpty) then lost stack world
      else
        let world := ((world.create target).debit tx.sender tx.value).credit target tx.value
        let out := execute blk env host
          { address := target, caller := tx.sender, value := tx.value, input := ByteArray.empty, code := tx.input,
            jumps := World.jumpBits tx.input, static := false, depth := 0, base := 0 } stack gas world
        if out.halt != 0 then out
        else
          let code := out.output
          let deposit := 200 * code.size.toUInt64
          if code.size > 24576 || (code.size > 0 && code.get! 0 == 0xef) || out.gas < deposit then lost out.stack out.world
          else ⟨0, out.gas - deposit, ByteArray.empty, out.stack, out.world.setCode target code⟩
  let success := out.halt == 0
  let world := if success then out.world else out.world.revert mark
  let left := if out.halt == 2 then 0 else out.gas
  let spent := tx.gasLimit - left
  let refund := min world.refund (spent / 5)
  let used := max (spent - refund) floor
  let world := world.credit tx.sender (Word.ofNat ((tx.gasLimit - used).toNat * price))
  let world := world.credit blk.coinbase (Word.ofNat (used.toNat * (price - baseFee)))
  let receipt : Receipt := { kind := tx.kind, success, cumulativeGas := used, logs := world.logs }
  .ok (world.endTransaction, out.stack, receipt)

end Fast
