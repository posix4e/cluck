import Evm.Service
import Evm.Trie

/-! # Validating one block against a state known only in part

`Evm.Service` imports blocks onto a state that is sent whole. A block of the real chain cannot be asked
that way. Here the request carries the block, the headers before it, and a witness: trie nodes named by
hash, contract code, and the addresses and slots whose hashes are the keys in those nodes.

Request, big-endian throughout, every item preceded by its length in 4 bytes:

    "JWIT1"
    fork (1 byte: 0 Cancun, 1 Prague, 2 Osaka, 3 BPO1, 4 BPO2, or 255 for whichever mainnet's schedule
      gives a block of this number and time, which needs chain id 1), chain id (8)
    the block's RLP
    header count (4), then the RLP of each header before the block, oldest first, ending with its parent:
      255 of them, or all of them when the block's number is below 255. Each names the one before it, so
      with the parent's own hash these give the 256 hashes BLOCKHASH can ask for
    node count (4), then each trie node
    code count (4), then each contract's code
    key count (4), then each key: 20 bytes for an address, 32 for a storage slot

Response, the 69 bytes of `Evm.Service`: status, blocks imported (0 or 1), a hash, a root.

    0  the block is valid on its parent: its own hash and the state root in its header
    3  the block is invalid, and everything that verdict rests on was proven by the witness
    4  the import failed for a reason other than the block being invalid
    5  the request is malformed, or names a fork this build does not run
    6  the witness falls short: the root field holds the hash of a node it lacks, or zero when what is
       lacking is a header, a contract's code or the address or slot behind a key
    7  the witness holds bytes that are not what their hash is used as
    8  the block was rejected while it ran, before what it had read could be checked against the
       witness. This is no verdict: a witness that leaves out an account makes a good block fail this way.

For every status but 0 the hash and root are the parent's.

What makes status 0 mean something: the witness is tied to the parent's state root, which is in the parent
header, whose hash is in the block. Everything read from the witness is checked against that root on the
way. Jaune treats an account it does not have as one that does not exist, so after the block has run,
every account and slot it read is looked up again: it must have been supplied, or the witness must prove
it absent. Upstream Jaune records reads only under the fork that puts them in the block; this package's
Jaune records them under every fork, with what is read in preparing a transaction before any code runs:
the account it is sent to, the one that account delegates to, and the signer of each authorization. So must every account and slot that is in
the state after the block and was not supplied before it, since a payment to an account that was left out
looks like the making of a new one. A block that touched anything else is answered with 6, never with a
verdict.

What it does not mean: that the parent is part of any chain. The answer is about this block on this
parent. And a fork named outright is the sender's choice: an answer about a mainnet block is worth
something only if the request said 255. -/

open Jaune

namespace Evm.Stateless

open Evm.Service (be take nat many P stop Response)
open Evm.Trie (Store Node)

structure Request where
  /-- `none` for mainnet's schedule. -/
  fork : Option Fork
  chainId : UInt64
  block : ByteArray
  headers : List ByteArray
  nodes : Array ByteArray
  codes : List ByteArray
  keys : List ByteArray

def magic : ByteArray := "JWIT1".toUTF8

def forkOf : Nat → Option Fork
  | 0 => some .cancun
  | 1 => some .prague
  | 2 => some .osaka
  | 3 => some .bpo1
  | 4 => some .bpo2
  | _ => none

def forkCode : Fork → Option Nat
  | .cancun => some 0
  | .prague => some 1
  | .osaka => some 2
  | .bpo1 => some 3
  | .bpo2 => some 4
  | _ => none

def sized (input : ByteArray) : P ByteArray := do take input (← nat input 4)

def request (input : ByteArray) : P Request := do
  if (← take input magic.size) != magic then stop
  let code ← nat input 1
  let fork ← if code == 255 then pure none else match forkOf code with
    | some fork => pure (some fork)
    | none => stop
  let chainId ← nat input 8
  let block ← sized input
  let headers ← many (← nat input 4) (sized input)
  let nodes ← many (← nat input 4) (sized input)
  let codes ← many (← nat input 4) (sized input)
  let keys ← many (← nat input 4) (sized input)
  pure { fork, chainId := chainId.toUInt64, block, headers, nodes := nodes.toArray, codes, keys }

def Request.encode (r : Request) : Option ByteArray := do
  let fork ← match r.fork with
    | some fork => forkCode fork
    | none => some 255
  let list (items : List ByteArray) : ByteArray :=
    items.foldl (fun out item => out ++ Evm.Service.sized item) (be 4 items.length)
  pure <| magic ++ be 1 fork ++ be 8 r.chainId.toNat ++ Evm.Service.sized r.block ++ list r.headers ++
    list r.nodes.toList ++ list r.codes ++ list r.keys

/-- Why there is no verdict. -/
inductive Shortfall where
  /-- The witness lacks the node with this hash, or (zero) a header, a code or a key's preimage. -/
  | lacking (hash : U256) (what : String := "")
  | malformed
  | failure

abbrev M := Except Shortfall

def ofTrie {α} : Except Trie.Fault α → M α
  | .ok a => .ok a
  | .error (.missing hash) => .error (.lacking hash)
  | .error _ => .error .malformed

/-- The same, saying what was being looked for: not part of the response, for whoever makes witnesses. -/
def ofTrieFor {α} (what : Unit → String) : Except Trie.Fault α → M α
  | .ok a => .ok a
  | .error (.missing hash) => .error (.lacking hash (what ()))
  | .error _ => .error .malformed

def hexOf (bytes : Bytes) : String :=
  bytes.foldl (fun out b => out ++ String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]) ""

def keyOf (bytes : Bytes) : Trie.Path := Trie.nibbles (Trie.wordBytes (Bytes.keccak bytes))

def emptyCodeHash : U256 := Trie.hashOf .empty

/-- An account as the state trie holds it. -/
structure Leaf where
  nonce : UInt64
  balance : U256
  storageRoot : U256
  codeHash : U256

def Leaf.read (bytes : ByteArray) : Option Leaf := do
  let fields ← Trie.strings bytes
  guard (fields.size == 4)
  let number (b : ByteArray) (most : Nat) : Option Bytes :=
    -- Scalars are written without leading zeros.
    if b.size ≤ most && (b.size == 0 || b[0]! != 0) then some b.toList else none
  let nonce ← number fields[0]! 8
  let balance ← number fields[1]! 32
  guard (fields[2]!.size == 32 && fields[3]!.size == 32)
  pure ⟨(Bytes.toNat nonce).toUInt64, Bytes.toU256 balance, Trie.word fields[2]! 0, Trie.word fields[3]! 0⟩

def Leaf.write (l : Leaf) : ByteArray :=
  let scalar (b : Bytes) : ByteArray := Trie.rlpString (Bytes.sig b).toByteArray
  Trie.rlpList (scalar l.nonce.toBytes ++ scalar l.balance.toBytes ++
    Trie.rlpString (Trie.wordBytes l.storageRoot) ++ Trie.rlpString (Trie.wordBytes l.codeHash))

def slotValue (v : U256) : ByteArray := Trie.rlpString (Bytes.sig v.toBytes).toByteArray

/-- What the witness gave: the accounts that could be named and filled in, and for each what the trie
says of it, which is needed again when the block has run. -/
structure Known where
  store : Store
  root : U256
  state : State
  leaves : Std.TreeMap Address Leaf compare

/-- Every account the witness holds whose address and code it also supplies, with every slot of its
storage the witness holds and names. The rest of the state is not here, and is not assumed empty: see
`checkReads`. -/
def materialise (r : Request) (root : U256) : M Known := do
  let store := Store.ofNodes r.nodes
  let codes : Std.TreeMap U256 ByteArray Trie.order :=
    r.codes.foldl (fun m code => m.insert (Trie.hashOf code) code) .empty
  let mut addresses : Std.TreeMap U256 Address Trie.order := .empty
  let mut slots : Std.TreeMap U256 U256 Trie.order := .empty
  for key in r.keys do
    let hash := Trie.hashOf key
    if key.size == 20 then
      let some address := Bytes.toAddress? key.toList | .error .malformed
      addresses := addresses.insert hash address
    else if key.size == 32 then slots := slots.insert hash (Trie.word key 0)
    else .error .malformed
  let mut accounts : List (Address × Account) := []
  let mut leaves : Std.TreeMap Address Leaf compare := .empty
  let accountLeaves ← ofTrie (Trie.leaves store (.sealed root))
  for (path, bytes) in accountLeaves do
    if path.size != 64 then .error .malformed
    let some leaf := Leaf.read bytes | .error .malformed
    let some address := addresses.get? (Trie.pathWord path) | continue
    let code ←
      if leaf.codeHash == emptyCodeHash then pure (some ByteArray.empty) else pure (codes.get? leaf.codeHash)
    let some code := code | continue
    let mut storage : List (U256 × U256) := []
    let slotLeaves ← ofTrie (Trie.leaves store (.sealed leaf.storageRoot))
    for (slotPath, valueBytes) in slotLeaves do
      if slotPath.size != 64 then .error .malformed
      let some value := Trie.string valueBytes | .error .malformed
      if value.size == 0 || value.size > 32 || value[0]! == 0 then .error .malformed
      let some slot := slots.get? (Trie.pathWord slotPath) | continue
      storage := (slot, Bytes.toU256 value.toList) :: storage
    accounts := (address, ⟨leaf.nonce, leaf.balance, Storage.ofList storage, code⟩) :: accounts
    leaves := leaves.insert address leaf
  pure { store, root, state := State.ofPresentList accounts, leaves }

/-- Every account and slot the block read was either supplied or is proven absent. An account or slot that
is in the trie and was not supplied (its address, its code or its slot's number was left out) was read as
if it did not exist, so the run means nothing. -/
def checkReads (known : Known) (accounts : List Address) (slots : List (Address × U256)) : M Unit := do
  for address in accounts do
    if known.leaves.contains address then continue
    let found ← ofTrieFor (fun _ => s!"account {hexOf address.toBytes}, which the block read")
      (Trie.get known.store (.sealed known.root) (keyOf address.toBytes))
    if found.isSome then
      .error (.lacking 0 s!"the address or code of account {hexOf address.toBytes}, which the block read")
  for (address, slot) in slots do
    -- A slot of an account that is not there was read as zero, and the loop above has shown it is not there.
    let some leaf := known.leaves.get? address | continue
    if ((known.state.get address).storage.get? slot).isSome then continue
    let found ← ofTrieFor (fun _ => s!"slot {hexOf slot.toBytes} of {hexOf address.toBytes}, which the block read")
      (Trie.get known.store (.sealed leaf.storageRoot) (keyOf slot.toBytes))
    if found.isSome then
      .error (.lacking 0 s!"the number of slot {hexOf slot.toBytes} of {hexOf address.toBytes}, which the block read")

/-- The state root after the block: the parent's trie with every account that changed written back. -/
def rootAfter (known : Known) (after : State) : M U256 := do
  let mut trie : Node := .sealed known.root
  let before := known.state
  -- Every account there is afterwards, and then every one there was that is gone. The two lists are not
  -- joined and searched for repeats: that is the square of their length, and the witness sets the length.
  for (address, account) in after.toList do
    let key := keyOf address.toBytes
    let old := before[address]?
    let leaf := known.leaves.get? address
    let oldStorage := (old.map (·.storage)).getD .empty
    let mut storage : Node := .sealed ((leaf.map (·.storageRoot)).getD Trie.emptyRoot)
    let mut changed := false
    -- In the same way: every slot the account has, then every one it had and has no more.
    let now := account.storage.toList
    let gone := (oldStorage.keys.filter fun slot => (account.storage.get? slot).isNone).map fun slot => (slot, (0 : U256))
    for (slot, value) in now ++ gone do
      if value != oldStorage.get slot then
        changed := true
        let slotKey := keyOf slot.toBytes
        storage ← ofTrieFor (fun _ => s!"{if value == 0 then "clearing" else "writing"} slot \
            {hexOf slot.toBytes} of {hexOf address.toBytes}") <|
          if value == 0 then Trie.remove known.store storage slotKey
          else Trie.put known.store storage slotKey (slotValue value)
    let sameCode := old.any (·.code.data == account.code.data)
    let unchanged := !changed && sameCode &&
      old.any fun o => o.nonce == account.nonce && o.balance == account.balance
    if unchanged then continue
    let codeHash := match leaf with
      | some l => if sameCode then l.codeHash else Trie.hashOf account.code
      | none => Trie.hashOf account.code
    let written : Leaf := ⟨account.nonce, account.balance, Trie.rootHash storage, codeHash⟩
    trie ← ofTrieFor (fun _ => s!"writing account {hexOf address.toBytes}") (Trie.put known.store trie key written.write)
  for address in before.keys do
    if (after[address]?).isNone then
      trie ← ofTrieFor (fun _ => s!"removing account {hexOf address.toBytes}")
        (Trie.remove known.store trie (keyOf address.toBytes))
  pure (Trie.rootHash trie)

def header (bytes : ByteArray) : Option Header := do
  let item ← Bytes.toRlpItem? bytes.toList
  match item.toExceptHeader with
  | .ok h => some h
  | .error _ => none

/-- The verdict on a block Jaune rejected or could not run. -/
def refused (e : TransitionError) : UInt8 :=
  match e.split with
  | .inl _ => 4
  | .inr _ => 3

structure Verdict where
  status : UInt8
  hash : U256 := 0
  /-- Jaune's own words for a rejection. Not part of the response: for whoever is making witnesses. -/
  reason : String := ""

def validate (r : Request) (fork : Fork) (parent : Header) (ancestors : List Header) (block : Block)
    (blockHash : U256) : M Verdict := do
  let rules := fork.ruleSet
  if let .error e := checkBlockRlpSize rules.block r.block.size then
    return ⟨3, 0, (TransitionError.block e).render⟩
  let known ← materialise r parent.stateRoot
  let chain : BlockChain :=
    { blocks := ancestors.map fun h => ⟨h, [], [], []⟩, state := known.state, chainId := r.chainId }
  -- Neither of these reads the state: a rejection here stands whatever the witness holds.
  if let .error e := validateHeader rules chain block.header then return ⟨refused e, 0, e.render⟩
  if let .error e := checkBlockOmmers rules chain block.header block.ommers then
    return ⟨refused e, 0, e.render⟩
  let benv := initBenv fork chain block.header
  match applyBody benv block.transactions block.ommers block.withdrawals with
  | .error e => return ⟨if refused e == 3 then 8 else 4, 0, e.render⟩
  | .ok (after, out) =>
    let reads := out.blockAccessListBuilder
    -- What the block made: accounts and slots it holds now that were not supplied. Each has to be new.
    let made := after.keys.filter fun address => !known.leaves.contains address
    let madeSlots := after.toList.flatMap fun (address, account) =>
      let old := (known.state.get address).storage
      (account.storage.keys.filter fun slot => (old.get? slot).isNone).map fun slot => (address, slot)
    checkReads known (reads.readAccounts.toList ++ made) (reads.readSlots.toList ++ madeSlots)
    let stateRoot ← rootAfter known after
    let requestsHash :=
      if rules.header.requestsHash then some (computeRequestsHash out.requests) else none
    let checks := do
      stateTransitionChecks out block.header (getTransactionsRoot out) stateRoot (getReceiptRoot out)
        (logsBloom out.blockLogs) (getWithdrawalsRoot out) requestsHash
      blockAccessListCheck rules out block.header
    match checks with
    | .error e => return ⟨3, 0, (TransitionError.block e).render⟩
    | .ok () => return ⟨0, blockHash, ""⟩

/-- The response, and Jaune's reason when there is one. -/
def runWithReason (r : Request) : Response × String :=
  let nothing : Response × String := (⟨5, 0, 0, 0⟩, "")
  match rlpToBlockE r.block.toList with
  | .error _ => nothing
  | .ok (block, blockHash) =>
    let fork := match r.fork with
      | some fork => some fork
      | none =>
        if r.chainId != 1 then none else
        match mainnetChainConfig.forkAt block.header.number block.header.timestamp with
        | .ok fork => if (forkCode fork).isSome then some fork else none
        | .error _ => none
    match fork, r.headers.mapM header with
    | none, _ | _, none => nothing
    | some fork, some ancestors =>
      -- Each header is the parent of the next, so the hashes BLOCKHASH gives are the chain's.
      let linked := (ancestors.zip (ancestors.drop 1)).all fun (a, b) => a.hash == b.parentHash
      match ancestors.getLast? with
      | none => (⟨6, 0, 0, 0⟩, "no headers")
      | some parent =>
        let answer (status : UInt8) (root : U256) (reason : String := "") : Response × String :=
          (⟨status, 0, parent.hash, root⟩, reason)
        if !linked || parent.hash != block.header.parentHash then nothing
        else if ancestors.length != min 255 block.header.number then answer 6 0
        else
          match validate r fork parent ancestors block blockHash with
          | .ok ⟨0, hash, _⟩ => (⟨0, 1, hash, block.header.stateRoot⟩, "")
          | .ok ⟨status, _, reason⟩ => answer status parent.stateRoot reason
          | .error (.lacking hash what) => answer 6 hash what
          | .error .malformed => answer 7 parent.stateRoot
          | .error .failure => answer 4 parent.stateRoot

def run (r : Request) : Response := (runWithReason r).1

def serve (input : ByteArray) : ByteArray :=
  match (request input).run 0 with
  | some (r, pos) => if pos = input.size then (run r).encode else (⟨5, 0, 0, 0⟩ : Response).encode
  | none => (⟨5, 0, 0, 0⟩ : Response).encode

end Evm.Stateless

/-- Either kind of request, told apart by how it begins: a chain with its whole state (`Evm.Service`), or
one block with a witness. -/
def Evm.serve (input : ByteArray) : ByteArray :=
  if input.extract 0 Evm.Stateless.magic.size == Evm.Stateless.magic then Evm.Stateless.serve input
  else Evm.Service.serve input
