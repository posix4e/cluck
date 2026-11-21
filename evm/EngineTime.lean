import Evm
import Platform

/-! Where the time goes when the fast engine checks a block, a part at a time, on whichever runtime this is
linked against. Reads one stateless request on standard input and prints the milliseconds each part took.
For finding what to make faster next; it gives no verdict. -/
open Jaune Evm

@[extern "evm_clock_millis"] opaque clockMillis : IO UInt64

partial def readAll (soFar : ByteArray) : IO ByteArray := do
  let chunk ← Platform.read 65536
  if chunk.isEmpty then pure soFar else readAll (soFar ++ chunk)

def say (s : String) : IO Unit := Platform.write s.toUTF8

/-- One part, timed. What it computes is forced by being asked a number about it. -/
def part {α : Type} (name : String) (work : Unit → α) (measure : α → Nat) : IO α := do
  let t0 ← clockMillis
  let value ← IO.lazyPure work
  let n := measure value
  let t1 ← clockMillis
  say s!"{name}: {(t1 - t0).toNat} ms ({n})\n"
  return value

def main : IO UInt32 := do
  let input ← readAll .empty
  let t0 ← clockMillis
  let some (r, _) ← part "the request read" (fun _ => (Stateless.request (Stateless.magic ++ input.extract 5 input.size)).run 0)
      (fun x => if x.isSome then 1 else 0)
    | do say "not a request\n"; return 1
  let .ok (block, _) ← part "the block decoded" (fun _ => rlpToBlockE r.block.toList) (fun x => if x.isOk then 1 else 0)
    | do say "the block does not decode\n"; return 1
  let some fork := (match r.fork with
    | some fork => some fork
    | none => (mainnetChainConfig.forkAt block.header.number block.header.timestamp).toOption)
    | do say "no fork\n"; return 1
  let some ancestors ← part "the headers decoded" (fun _ => r.headers.mapM Stateless.header) (fun x => (x.map (·.length)).getD 0)
    | do say "a header does not decode\n"; return 1
  let _ ← part "the headers hashed into a chain" (fun _ =>
    (ancestors.zip (ancestors.drop 1)).all fun (a, b) => a.hash == b.parentHash) (fun x => if x then 1 else 0)
  let some parent := ancestors.getLast? | do say "no headers\n"; return 1
  let .ok known ← part "the witness read (materialise)" (fun _ => Stateless.materialise r parent.stateRoot)
      (fun x => match x with | .ok k => k.leaves.size | .error _ => 0)
    | do say "the witness does not read\n"; return 1
  let rules := fork.ruleSet
  let chain : BlockChain := { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := known.state, chainId := r.chainId }
  let _ ← part "the header checked" (fun _ => validateHeader rules chain block.header) (fun x => if x.isOk then 1 else 0)
  let .ok decoded ← part "the transactions decoded" (fun _ => block.transactions.mapM (decodeTransaction rules))
      (fun x => match x with | .ok l => l.length | .error _ => 0)
    | do say "a transaction does not decode\n"; return 1
  let some body ← part "senders recovered" (fun _ => Bridge.body fork r.chainId block decoded)
      (fun x => (x.map (·.transactions.size)).getD 0)
    | do say "a transaction has no sender\n"; return 1
  let blk ← part "the block's environment (the headers hashed again)" (fun _ => Bridge.environment fork r.chainId block.header ancestors)
    (fun e => (e.blockHash (e.number - 1)).w0.toNat % 2)
  let backing ← part "the codes indexed" (fun _ => Bridge.backing known) (fun b => if (b.code Fast.emptyCodeHash).isSome then 1 else 0)
  let .ok out ← part "the block run" (fun _ => Fast.runBlock blk (Bridge.host fork) body ByteArray.empty (Fast.World.new backing))
      (fun x => match x with | .ok o => o.gasUsed.toNat | .error _ => 0)
    | do say "the block was refused\n"; return 1
  -- The same block with every precompiled contract answering at once that it failed: not the block that
  -- was, since what a contract does after a failed call differs, but a rough floor for what the engine
  -- takes without them.
  let quick : Fast.Host := { Bridge.host fork with precompile := fun _ _ _ => ⟨false, 0, ByteArray.empty⟩ }
  let _ ← part "the block run again, precompiled contracts failing at once (a rough floor)" (fun _ =>
    Fast.runBlock blk quick body ByteArray.empty (Fast.World.new backing))
      (fun x => match x with | .ok o => o.gasUsed.toNat | .error _ => 0)
  let _ ← part "the state root" (fun _ => Bridge.rootAfter known out.world) (fun x => match x with | .ok root => root.toNat % 2 | .error _ => 2)
  let _ ← part "the receipts root and the bloom" (fun _ => Bridge.receiptsRootAndBloom out.receipts) (fun x => x.1.toNat % 2)
  let kept : BlockOutput :=
    { BlockOutput.init with
      transactionsTrie := decoded.zipIdx.foldl (fun trie (tx, index) =>
        trie.insert (Rlp.Item.bytes index.toBytes).toBytes tx) BlockOutput.init.transactionsTrie
      withdrawalsTrie := processWithdrawalsTrie BlockOutput.init.withdrawalsTrie block.withdrawals }
  let _ ← part "the transactions root" (fun _ => getTransactionsRoot kept) (fun x => x.toNat % 2)
  let _ ← part "the withdrawals root" (fun _ => getWithdrawalsRoot kept) (fun x => x.toNat % 2)
  let _ ← part "the requests hash" (fun _ => computeRequestsHash (out.requests.toList.map (·.toList))) (fun x => x.toNat % 2)
  let t1 ← clockMillis
  say s!"in all: {(t1 - t0).toNat} ms\n"
  return 0
