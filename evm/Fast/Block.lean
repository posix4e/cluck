import Fast.Tx

/-! A block on the fast engine: the calls the block itself makes before and after its transactions, the
transactions, the withdrawals, and the requests the block hands to the consensus layer. What comes out is
the world after, a receipt for each transaction and the requests; the roots a header commits to are made
of these by whoever holds the header. -/

namespace Fast

/-- A word from hexadecimal digits, for the few addresses that are fixed. -/
def Word.ofHex (digits : String) : Word :=
  Word.ofNat (digits.foldl (fun n c =>
    n * 16 + (if c.isDigit then c.toNat - 48 else if c ≥ 'a' && c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0)

/-- Who the block's own calls come from. -/
def systemAddress : Word := Word.ofHex "fffffffffffffffffffffffffffffffffffffffe"
/-- The contract that keeps the beacon chain's block roots (EIP-4788). -/
def beaconRootsAddress : Word := Word.ofHex "000F3df6D732807Ef1319fB7B8bB8522d0Beac02"
/-- The contract that keeps block hashes (EIP-2935). -/
def historyAddress : Word := Word.ofHex "0000F90827F1C53a10cb7A02335B175320002935"
/-- The contract that queues withdrawal requests (EIP-7002). -/
def withdrawalRequestsAddress : Word := Word.ofHex "00000961Ef480Eb55e80D19ad83579A64c007002"
/-- The contract that queues consolidation requests (EIP-7251). -/
def consolidationRequestsAddress : Word := Word.ofHex "0000BBdDc7CE488642fb579F8B00f3a590007251"
/-- The deposit contract, and the event it logs for a deposit (EIP-6110). -/
def depositAddress : Word := Word.ofHex "00000000219ab540356cBB839Cbe05303d7705Fa"
def depositEvent : Word := Word.ofHex "649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5"

structure Withdrawal where
  address : Word
  /-- The amount, in units of a billion wei. -/
  gwei : UInt64

structure BlockInput where
  parentHash : Word
  parentBeaconRoot : Word
  transactions : Array Tx
  withdrawals : Array Withdrawal
  /-- Blobs the block may hold, and one transaction may. -/
  maxBlobs : UInt64
  blobsPerTx : UInt64
  /-- The addresses of the precompiled contracts. -/
  precompiles : Array Word

structure BlockOutput where
  world : World
  stack : ByteArray
  receipts : Array Receipt
  gasUsed : UInt64
  blobs : UInt64
  /-- Each kind of request that there is any of: the kind's byte, then the requests end to end. -/
  requests : Array ByteArray

/-- A call the block makes itself: from the system address, with gas nobody pays for. The answer is the
world, the stack, how it went (0 well, 1 there is no code there, 2 it failed) and what it returned. -/
def systemCall (blk : @& BlockEnv) (host : @& Host) (target : Word) (input : ByteArray) (stack : ByteArray)
    (world : World) : World × ByteArray × UInt8 × ByteArray :=
  let (world, account) := world.withCode target
  if account.code.size == 0 then (world, stack, 1, ByteArray.empty) else
  let (world, jumps) := world.jumpsOf account.codeHash account.code
  let env : TxEnv := { origin := systemAddress, gasPrice := Word.zero, blobHashes := #[] }
  let mark := world.checkpoint
  let out := execute blk env host
    { address := target, caller := systemAddress, value := Word.zero, input, code := account.code, jumps,
      static := false, depth := 0, base := 0 } stack 30000000 world
  let world := if out.halt == 0 then out.world else out.world.revert mark
  (world.endTransaction, out.stack, if out.halt == 0 then 0 else 2, out.output)

/-- The number 32 bytes of a deposit event spell at `off`, when it is small. -/
def fieldAt (data : @& ByteArray) (off : Nat) : Option Nat :=
  let w := wordAt data (Word.ofUInt64 off.toUInt64)
  if w.small then some w.w0.toNat else none

/-- One deposit as the consensus layer takes it, from the event the deposit contract logged: the fields
without the layout around them. None if the layout is not exactly the contract's. -/
def depositOf (data : @& ByteArray) : Option ByteArray :=
  if data.size != 576 then none
  else if fieldAt data 0 != some 160 || fieldAt data 32 != some 256 || fieldAt data 64 != some 320 ||
      fieldAt data 96 != some 384 || fieldAt data 128 != some 512 then none
  else if fieldAt data 160 != some 48 || fieldAt data 256 != some 32 || fieldAt data 320 != some 8 ||
      fieldAt data 384 != some 96 || fieldAt data 512 != some 8 then none
  else some (data.extract 192 240 ++ data.extract 288 320 ++ data.extract 352 360 ++ data.extract 416 512 ++
             data.extract 544 552)

/-- Every deposit the block's transactions logged, end to end, or none if one is misshapen. -/
def depositsOf (receipts : @& Array Receipt) : Option ByteArray :=
  receipts.foldl (fun found receipt =>
    receipt.logs.foldl (fun found log =>
      match found with
      | none => none
      | some all =>
        if log.address == depositAddress && log.topics.size > 0 && log.topics[0]! == depositEvent then
          (depositOf log.data).map (all ++ ·)
        else some all) found) (some ByteArray.empty)

/-- The transactions, one after another. -/
def transactions (blk : @& BlockEnv) (host : @& Host) (input : @& BlockInput) :
    Nat → Nat → BlockOutput → Except (String × World) BlockOutput
  | 0, _, out => .ok out
  | left + 1, i, out =>
    match input.transactions[i]? with
    | none => .ok out
    | some tx =>
      let allowed : Allowance :=
        { gas := blk.gasLimit - out.gasUsed, blobs := input.maxBlobs - out.blobs, blobsPerTx := input.blobsPerTx,
          alwaysWarm := input.precompiles }
      match process blk host allowed tx out.stack out.world with
      | .error (why, world, _) => .error (s!"transaction {i}: {why}", world)
      | .ok (world, stack, receipt) =>
        let gasUsed := out.gasUsed + receipt.cumulativeGas
        transactions blk host input left (i + 1)
          { out with world, stack, gasUsed, blobs := out.blobs + tx.blobHashes.size.toUInt64,
                     receipts := out.receipts.push { receipt with cumulativeGas := gasUsed } }

/-- What a block does before its first transaction: it records its parent's beacon root and hash. Neither
call can make the block invalid: where the contract is not there, nothing happens. -/
def openBlock (blk : @& BlockEnv) (host : @& Host) (input : @& BlockInput) (stack : ByteArray) (world : World) :
    World × ByteArray :=
  let (world, stack, _, _) := systemCall blk host beaconRootsAddress input.parentBeaconRoot.bytes stack world
  let (world, stack, _, _) := systemCall blk host historyAddress input.parentHash.bytes stack world
  (world, stack)

/-- What a block does after its last transaction: the withdrawals are paid, and the requests are gathered,
the deposits its transactions logged and what the two queues give up, which they must. -/
def closeBlock (blk : @& BlockEnv) (host : @& Host) (input : @& BlockInput) (out : BlockOutput) :
    Except (String × World) BlockOutput := do
  let world := input.withdrawals.foldl (fun world w =>
    world.credit w.address (Word.ofNat (w.gwei.toNat * 1000000000))) out.world
  let world := world.endTransaction
  let some deposits := depositsOf out.receipts
    | .error ("a deposit event that is not shaped as the deposit contract's", world)
  let (world, stack, went, withdrawalRequests) :=
    systemCall blk host withdrawalRequestsAddress ByteArray.empty out.stack world
  if went != 0 then .error ("the withdrawal requests contract is missing or failed", world)
  let (world, stack, went, consolidationRequests) :=
    systemCall blk host consolidationRequestsAddress ByteArray.empty stack world
  if went != 0 then .error ("the consolidation requests contract is missing or failed", world)
  let requests := #[(0x00, deposits), (0x01, withdrawalRequests), (0x02, consolidationRequests)].filterMap
    fun ((kind, data) : UInt8 × ByteArray) => if data.size == 0 then none else some ((ByteArray.mk #[kind]) ++ data)
  return { out with world, stack, requests }

/-- A block run on `world`. An error is the block being one that may not be, with the world as it stood:
whoever relies on the refusal has to know whether the world is marked as having asked for what could not
be proven, because a refusal reached on such answers is no refusal. -/
def runBlock (blk : @& BlockEnv) (host : @& Host) (input : @& BlockInput) (stack : ByteArray) (world : World) :
    Except (String × World) BlockOutput := do
  let (world, stack) := openBlock blk host input stack world
  let out ← transactions blk host input input.transactions.size 0
    { world, stack, receipts := #[], gasUsed := 0, blobs := 0, requests := #[] }
  closeBlock blk host input out

end Fast
