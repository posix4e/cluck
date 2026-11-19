import Jaune.Transaction
import Evm.PowMod

/-! # Block import as a function from bytes to bytes

A request carries a chain's starting state, its genesis block and the blocks to import. The response says
how far the import got and what the chain's tip and state root then were. Everything between is Jaune's:
`rlpToBlockEAt` decodes, `State.root` hashes the accounts, `addBlockToChainAt` validates and executes each
block, which includes checking the state root its header claims.

Request, big-endian throughout:

    "JBLK1"
    fork (1 byte: 0 Cancun, 1 Prague, 2 Osaka), chain id (8)
    account count (4), then for each account:
      address (20), nonce (8), balance (32), code length (4), code,
      slot count (4), then for each slot: key (32), value (32)
    genesis block RLP length (4), genesis block RLP
    block count (4), then for each block: RLP length (4), RLP

Response, 69 bytes: status (1), blocks imported (4), tip block hash (32), state root (32).

    0  every block imported
    1  the genesis block does not decode
    2  the accounts do not hash to the genesis block's state root (the root they do hash to is returned)
    3  a block was rejected as invalid; the tip and root are those before it
    4  the import failed for a reason other than the block being invalid
    5  the request is malformed, or names a fork this build does not run

The whole state is in the request. There is no proof of an account against a root other than hashing all of
them, so this imports blocks onto a state small enough to send, not onto mainnet's. -/

open Jaune

namespace Evm.Service

structure Request where
  fork : Fork
  chainId : UInt64
  accounts : List (Address × Account)
  genesis : Bytes
  blocks : List Bytes

structure Response where
  status : UInt8
  imported : Nat
  tip : U256
  root : U256

def forkOf : Nat → Option Fork
  | 0 => some .cancun
  | 1 => some .prague
  | 2 => some .osaka
  | _ => none

def forkCode : Fork → Option Nat
  | .cancun => some 0
  | .prague => some 1
  | .osaka => some 2
  | _ => none

def magic : ByteArray := "JBLK1".toUTF8

/-! ## Writing -/

def be (width n : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray⟩

def sized (bytes : ByteArray) : ByteArray := be 4 bytes.size ++ bytes

def encodeAccount (entry : Address × Account) : ByteArray :=
  let (address, account) := entry
  let slots := Std.TreeMap.toList account.storage
  address.toBytes.toByteArray ++ be 8 account.nonce.toNat ++ account.balance.toBytes.toByteArray ++
    sized account.code ++ be 4 slots.length ++
    slots.foldl (fun out (key, value) => out ++ key.toBytes.toByteArray ++ value.toBytes.toByteArray) .empty

def Request.encode (r : Request) : Option ByteArray := do
  let fork ← forkCode r.fork
  pure <| magic ++ be 1 fork ++ be 8 r.chainId.toNat ++ be 4 r.accounts.length ++
    r.accounts.foldl (fun out entry => out ++ encodeAccount entry) .empty ++
    sized r.genesis.toByteArray ++ be 4 r.blocks.length ++
    r.blocks.foldl (fun out block => out ++ sized block.toByteArray) .empty

def Response.encode (r : Response) : ByteArray :=
  be 1 r.status.toNat ++ be 4 r.imported ++ r.tip.toBytes.toByteArray ++ r.root.toBytes.toByteArray

/-! ## Reading -/

abbrev P := StateT Nat Option

def stop {α} : P α := StateT.lift none

def take (input : ByteArray) (n : Nat) : P ByteArray := do
  let pos ← get
  if pos + n ≤ input.size then
    set (pos + n)
    pure (input.extract pos (pos + n))
  else stop

def nat (input : ByteArray) (n : Nat) : P Nat := do
  pure ((← take input n).foldl (fun acc x => acc * 256 + x.toNat) 0)

def many {α} (count : Nat) (p : P α) : P (List α) := do
  let mut out := #[]
  for _ in [0:count] do out := out.push (← p)
  pure out.toList

def word (input : ByteArray) : P U256 := do
  pure (Bytes.toU256 (← take input 32).toList)

def account (input : ByteArray) : P (Address × Account) := do
  let some address := Bytes.toAddress? (← take input 20).toList | stop
  let nonce ← nat input 8
  let balance ← word input
  let code ← take input (← nat input 4)
  let slots ← many (← nat input 4) do
    let key ← word input
    let value ← word input
    pure (key, value)
  pure (address, ⟨nonce.toUInt64, balance, Storage.ofList slots, code⟩)

def request (input : ByteArray) : P Request := do
  if (← take input magic.size) != magic then stop
  let some fork := forkOf (← nat input 1) | stop
  let chainId ← nat input 8
  let accounts ← many (← nat input 4) (account input)
  let genesis ← take input (← nat input 4)
  let blocks ← many (← nat input 4) do take input (← nat input 4)
  pure { fork, chainId := chainId.toUInt64, accounts, genesis := genesis.toList,
         blocks := blocks.map (·.toList) }

/-! ## Running -/

def finish (status : UInt8) (chain : BlockChain) (imported : Nat) : Response :=
  let tip := chain.blocks.getLast?.map fun b => (Header.toRlpItem b.header).toBytes.keccak
  ⟨status, imported, tip.getD 0, chain.state.root⟩

def importAll (fork : Fork) : BlockChain → Nat → List Bytes → Response
  | chain, imported, [] => finish 0 chain imported
  | chain, imported, block :: rest =>
    match addBlockToChainAt fork chain block with
    | .ok (.inl next) => importAll fork next (imported + 1) rest
    | .ok (.inr _) => finish 3 chain imported
    | .error _ => finish 4 chain imported

def run (r : Request) : Response :=
  match r.fork.rules with
  | .error _ => ⟨5, 0, 0, 0⟩
  | .ok rules =>
    match rlpToBlockEAt rules r.genesis with
    | .error _ => ⟨1, 0, 0, 0⟩
    | .ok (genesis, _) =>
      let state := State.ofPresentList r.accounts
      let root := state.root
      if root = genesis.header.stateRoot then
        importAll r.fork { blocks := [genesis], state, chainId := r.chainId } 0 r.blocks
      else ⟨2, 0, 0, root⟩

def serve (input : ByteArray) : ByteArray :=
  match (request input).run 0 with
  | some (r, pos) => if pos = input.size then (run r).encode else (⟨5, 0, 0, 0⟩ : Response).encode
  | none => (⟨5, 0, 0, 0⟩ : Response).encode

end Evm.Service
