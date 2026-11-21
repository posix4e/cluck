import Fast.Word
import Fast.Keccak
import Std.Data.HashMap

/-! The world the fast engine runs against: accounts and storage as it has come to know them, and a journal
by which a call that fails is undone.

Nothing is known at the start. An account or a storage slot is fetched the first time it is touched, from
whatever stands behind (`Backing`: a whole state, or a witness that proves each answer), and kept. The only
way an entry comes to exist is that fetch, so what the engine has read is exactly what it holds, and a
fetch that cannot be answered (`missing`) is remembered as its own outcome and never passes for an account
that is not there.

Changes are made in place and each records what was there before. A call notes how long the journal is when
it starts (`Checkpoint`) and a failed call walks the journal back to that point. That an entry was fetched
is never undone: it was read. -/

namespace Fast

/-- A word stirred into 64 bits, for the tables below. Addresses and slot numbers are often hashes
already, and often small numbers; this serves both. -/
def Word.mix (w : Word) : UInt64 :=
  let a : UInt64 := w.w0 * (0x9e3779b97f4a7c15 : UInt64)
  let b : UInt64 := (w.w1 + (0x7f4a7c15 : UInt64)) * (0xc2b2ae3d27d4eb4f : UInt64)
  let c : UInt64 := (w.w2 + (0x165667b1 : UInt64)) * (0xff51afd7ed558ccd : UInt64)
  let d : UInt64 := w.w3 * (0xc4ceb9fe1a85ec53 : UInt64)
  a ^^^ b ^^^ c ^^^ d ^^^ (w.w0 >>> 29)

instance : Hashable Word := ⟨Word.mix⟩

/-- A storage slot's name: whose it is and which. -/
structure SlotKey where
  address : Word
  key : Word
  deriving BEq

instance : Hashable SlotKey where
  hash k := mixHash (hash k.address) (hash k.key)

namespace Word

/-- A word from 32 bytes, most significant first, at `off`; bytes past the end count as zero only through
the caller, which must have checked that all 32 are there. -/
@[inline] def ofBytes (b : @& ByteArray) (off : USize) (h : off.toNat + 31 < b.size) : Word :=
  ⟨swap (loadAt b off 24 (by omega)), swap (loadAt b off 16 (by omega)),
   swap (loadAt b off 8 (by omega)), swap (loadAt b off 0 (by omega))⟩

/-- A digest as the number its 32 bytes spell, most significant first. -/
@[inline] def ofDigest (d : Keccak.Digest) : Word := ⟨swap d.w3, swap d.w2, swap d.w1, swap d.w0⟩

/-- The 32 bytes of a word, most significant first. -/
def bytes (x : Word) : ByteArray :=
  store (store (store (store (ByteArray.mk (Array.replicate 32 0)) 0 (swap x.w3)) 8 (swap x.w2)) 16 (swap x.w1))
    24 (swap x.w0)

/-- The low 160 bits: a word as an address. -/
@[inline] def address (x : Word) : Word := ⟨x.w0, x.w1, x.w2 &&& 0xffffffff, 0⟩

/-- The 20 bytes of an address. -/
def addressBytes (x : Word) : ByteArray := x.bytes.extract 12 32

end Word

/-- Keccak-256 of the whole of some bytes, as a word. -/
def keccak (b : @& ByteArray) : Word := Word.ofDigest (Keccak.hash b 0 b.size)

/-- The hash of no code. -/
def emptyCodeHash : Word := ⟨0x7bfad8045d85a470, 0xe500b653ca82273b, 0x927e7db2dcc703c0, 0xc5d2460186f7233c⟩

/-- What stands behind answers about an account: its entry in the state, or that it has none, or that
nothing here can say. -/
inductive Fetched (α : Type) where
  | found (value : α)
  | absent
  | missing
  deriving Inhabited

/-- An account as the state holds it, without its storage or its code's bytes. `storageEmpty` is whether its
storage has nothing in it. -/
structure Leaf where
  nonce : UInt64
  balance : Word
  codeHash : Word
  storageEmpty : Bool

/-- Where what is not yet known comes from. Each is a question that may be asked once per account, slot or
code; the answers are kept by the world. -/
structure Backing where
  account : Word → Fetched Leaf
  /-- A slot of an account that has storage; `absent` is a slot holding nothing. -/
  slot : Word → Word → Fetched Word
  /-- Code by its hash. -/
  code : Word → Option ByteArray

instance : Inhabited Backing := ⟨⟨fun _ => .absent, fun _ _ => .absent, fun _ => none⟩⟩

structure Account where
  /-- Whether the account is in the state. One that is not has nothing in any other field. -/
  present : Bool
  nonce : UInt64
  balance : Word
  codeHash : Word
  /-- The code's bytes, once they have been needed: until then `hasCode` is false and this is empty. -/
  code : ByteArray
  hasCode : Bool
  /-- Its storage is known to hold nothing but what is in this world: it was not in the state before, or it
  was created since. Slots of such an account are never asked of what stands behind. -/
  fresh : Bool
  /-- The transaction in which it became warm, by number; none is 0. -/
  warmAt : UInt64
  /-- The transaction in which it was created, by number; none is 0. -/
  createdAt : UInt64
  /-- Whether anything about it has been changed since it was fetched and not undone. -/
  dirty : Bool
  /-- What its storage was when fetched: nothing in it. -/
  storageWasEmpty : Bool
  deriving Inhabited

/-- Whether an account counts as nothing: no code, no nonce, no balance (EIP-161). One not in the state does. -/
@[inline] def Account.empty (a : Account) : Bool :=
  a.nonce == 0 && a.balance.isZero && a.codeHash == emptyCodeHash

structure Slot where
  value : Word
  /-- What it held when the transaction numbered `originalAt` first touched it: what SSTORE's price and
  refund are reckoned from. -/
  original : Word
  originalAt : UInt64
  warmAt : UInt64
  /-- What it held when fetched: what the state before the block had. -/
  before : Word
  deriving Inhabited

structure Log where
  address : Word
  topics : Array Word
  data : ByteArray

/-- What was there before a change. -/
inductive Undo where
  | account (address : Word) (old : Account)
  | slot (key : SlotKey) (old : Slot)
  | transient (key : SlotKey) (old : Word)
  | refund (old : UInt64)

/-- How far everything that a failed call must lose had got when the call began. -/
structure Checkpoint where
  journal : Nat
  logs : Nat
  destructs : Nat

structure World where
  backing : Backing
  accounts : Std.HashMap Word Account
  slots : Std.HashMap SlotKey Slot
  transient : Std.HashMap SlotKey Word
  /-- Which bytes of a code are jump destinations, by the code's hash: worked out once. -/
  jumps : Std.HashMap Word ByteArray
  journal : Array Undo
  logs : Array Log
  /-- Accounts that destroyed themselves in the transaction they were created in, to be removed at its end. -/
  destructs : Array Word
  /-- The refund counter. It is only ever added to and taken from in amounts that keep it from going
  under nothing, but it is held as a wrapping number so that the order does not matter. -/
  refund : UInt64
  /-- The number of the transaction running: one more for each, and for each call the block itself makes. -/
  epoch : UInt64
  /-- Whether something was asked that what stands behind could not answer. Once true it stays true, and
  nothing computed after it means anything. -/
  missing : Bool
  /-- The first thing that could not be answered: an address, or a code's hash. -/
  lacking : Word
  deriving Inhabited

namespace World

def new (backing : Backing) : World :=
  { backing, accounts := {}, slots := {}, transient := {}, jumps := {}, journal := #[], logs := #[],
    destructs := #[], refund := 0, epoch := 1, missing := false, lacking := Word.zero }

/-- An account that is not in the state. -/
def noAccount : Account :=
  { present := false, nonce := 0, balance := Word.zero, codeHash := emptyCodeHash, code := ByteArray.empty,
    hasCode := true, fresh := true, warmAt := 0, createdAt := 0, dirty := false, storageWasEmpty := true }

@[inline] def lack (w : World) (what : Word) : World :=
  if w.missing then w else { w with missing := true, lacking := what }

/-- The account at `a`, fetched if it has not been. When it cannot be fetched the world is marked and an
account that is not there is handed back, which the caller must not take for an answer. -/
def account (w : World) (a : Word) : World × Account :=
  match w.accounts[a]? with
  | some entry => (w, entry)
  | none =>
    match w.backing.account a with
    | .found leaf =>
      let entry : Account :=
        { present := true, nonce := leaf.nonce, balance := leaf.balance, codeHash := leaf.codeHash,
          code := ByteArray.empty, hasCode := leaf.codeHash == emptyCodeHash, fresh := false, warmAt := 0,
          createdAt := 0, dirty := false, storageWasEmpty := leaf.storageEmpty }
      ({ w with accounts := w.accounts.insert a entry }, entry)
    | .absent => ({ w with accounts := w.accounts.insert a noAccount }, noAccount)
    | .missing => (w.lack a, noAccount)

/-- An account's entry replaced, what was there going on the journal. -/
def setAccount (w : World) (a : Word) (old new : Account) : World :=
  { w with accounts := w.accounts.insert a { new with dirty := true }, journal := w.journal.push (.account a old) }

/-- The account at `a` with its code's bytes, fetched if they have not been. -/
def withCode (w : World) (a : Word) : World × Account :=
  let (w, entry) := w.account a
  if entry.hasCode then (w, entry)
  else
    match w.backing.code entry.codeHash with
    | some code =>
      -- Fetching is not a change: nothing goes on the journal, and `dirty` stays as it was.
      let entry := { entry with code, hasCode := true }
      ({ w with accounts := w.accounts.insert a entry }, entry)
    | none => (w.lack entry.codeHash, entry)

/-- Makes `a` warm for this transaction. The answer is whether it was cold. -/
def warm (w : World) (a : Word) : World × Bool :=
  let (w, entry) := w.account a
  if entry.warmAt == w.epoch then (w, false)
  else
    -- Warmth is undone with the call that caused it, so it goes on the journal, but it is no change to
    -- the state: `dirty` is put back as it was.
    let warmed := { entry with warmAt := w.epoch }
    ({ w with accounts := w.accounts.insert a warmed, journal := w.journal.push (.account a entry) }, true)

/-- The slot `key` of `a`, fetched if it has not been, and stamped for this transaction. -/
def slot (w : World) (a key : Word) : World × Slot :=
  let name : SlotKey := ⟨a, key⟩
  let (w, entry) :=
    match w.slots[name]? with
    | some entry => (w, entry)
    | none =>
      let (w, owner) := w.account a
      let fetched : Fetched Word := if owner.fresh || owner.storageWasEmpty then .absent else w.backing.slot a key
      match fetched with
      | .found value =>
        let entry : Slot := { value, original := value, originalAt := 0, warmAt := 0, before := value }
        ({ w with slots := w.slots.insert name entry }, entry)
      | .absent =>
        let entry : Slot :=
          { value := Word.zero, original := Word.zero, originalAt := 0, warmAt := 0, before := Word.zero }
        ({ w with slots := w.slots.insert name entry }, entry)
      | .missing => (w.lack a, default)
  if entry.originalAt == w.epoch then (w, entry)
  else
    -- First touch in this transaction: what it holds now is what the transaction began with. This is a
    -- fact about the transaction and not a change, so it is not journaled; a later undo puts back an
    -- entry with an older stamp, which is stamped again with the same value.
    let entry := { entry with original := entry.value, originalAt := w.epoch }
    ({ w with slots := w.slots.insert name entry }, entry)

/-- Makes a slot warm for this transaction. The answer is the slot as it was and whether it was cold. -/
def warmSlot (w : World) (a key : Word) : World × Slot × Bool :=
  let (w, entry) := w.slot a key
  if entry.warmAt == w.epoch then (w, entry, false)
  else
    let warmed := { entry with warmAt := w.epoch }
    ({ w with slots := w.slots.insert ⟨a, key⟩ warmed, journal := w.journal.push (.slot ⟨a, key⟩ entry) },
     warmed, true)

/-- A slot given a new value. `old` is the entry as `slot` or `warmSlot` last gave it. -/
def setSlot (w : World) (a key : Word) (old : Slot) (value : Word) : World :=
  { w with slots := w.slots.insert ⟨a, key⟩ { old with value }, journal := w.journal.push (.slot ⟨a, key⟩ old) }

def transientGet (w : World) (a key : Word) : Word := w.transient.getD ⟨a, key⟩ Word.zero

def transientSet (w : World) (a key value : Word) : World :=
  let name : SlotKey := ⟨a, key⟩
  let old := w.transient.getD name Word.zero
  { w with transient := w.transient.insert name value, journal := w.journal.push (.transient name old) }

def addRefund (w : World) (amount : UInt64) : World :=
  { w with refund := w.refund + amount, journal := w.journal.push (.refund w.refund) }

def subRefund (w : World) (amount : UInt64) : World :=
  { w with refund := w.refund - amount, journal := w.journal.push (.refund w.refund) }

def log (w : World) (entry : Log) : World := { w with logs := w.logs.push entry }

def checkpoint (w : World) : Checkpoint := ⟨w.journal.size, w.logs.size, w.destructs.size⟩

/-- One change put back. -/
def undo (w : World) : Undo → World
  | .account a old => { w with accounts := w.accounts.insert a old }
  | .slot key old =>
    -- The stamp for this transaction is a fact, not a change: it survives the undo when the old entry
    -- had it already, and when it had not, the value it is stamped with again is the same.
    { w with slots := w.slots.insert key old }
  | .transient key old => { w with transient := w.transient.insert key old }
  | .refund old => { w with refund := old }

/-- Everything since `mark` undone, the latest first. -/
def revert (w : World) (mark : Checkpoint) : World :=
  go ({ w with logs := w.logs.shrink mark.logs, destructs := w.destructs.shrink mark.destructs }) (w.journal.size - mark.journal)
where
  go (w : World) : Nat → World
    | 0 => w
    | n + 1 =>
      match w.journal.back? with
      | none => w
      | some change => go (({ w with journal := w.journal.pop }).undo change) n

/-! ## Changes to accounts -/

def setBalance (w : World) (a : Word) (balance : Word) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry { entry with present := true, balance }

/-- `amount` added to what `a` has. An account that was not in the state comes into it. -/
def credit (w : World) (a amount : Word) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry { entry with present := true, balance := entry.balance.add amount }

/-- `amount` taken from what `a` has, which the caller has checked is enough. -/
def debit (w : World) (a amount : Word) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry { entry with balance := entry.balance.sub amount }

def setNonce (w : World) (a : Word) (nonce : UInt64) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry { entry with present := true, nonce }

def setCode (w : World) (a : Word) (code : ByteArray) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry
    { entry with present := true, code, hasCode := true, codeHash := if code.size == 0 then emptyCodeHash else keccak code }

/-- An account made by CREATE or by a creating transaction: nonce 1, no code yet, and storage that holds
nothing whatever was fetched for the address before. What it had as balance stays. -/
def create (w : World) (a : Word) : World :=
  let (w, entry) := w.account a
  w.setAccount a entry
    { entry with present := true, nonce := 1, code := ByteArray.empty, hasCode := true, codeHash := emptyCodeHash,
                 fresh := true, createdAt := w.epoch }

/-- An account marked for removal at the end of the transaction. -/
def destruct (w : World) (a : Word) : World := { w with destructs := w.destructs.push a }

/-- An account taken out of the state, with everything in its storage. -/
def remove (w : World) (a : Word) : World :=
  let (w, entry) := w.account a
  let w := w.setAccount a entry { noAccount with warmAt := entry.warmAt }
  -- Its slots that are known are emptied; the rest are never asked for again, the account being fresh.
  let names := w.slots.fold (fun names name _ => if name.address == a then names.push name else names) #[]
  names.foldl (fun w name =>
    match w.slots[name]? with
    | some entry => { w with slots := w.slots.insert name { entry with value := Word.zero } }
    | none => w) w

/-- The end of a transaction: accounts that destroyed themselves are removed, what belongs to the
transaction alone is dropped, and the next one is numbered. Nothing can be undone past this. -/
def endTransaction (w : World) : World :=
  let w := w.destructs.foldl (fun w a => w.remove a) w
  { w with journal := #[], logs := #[], destructs := #[], transient := {}, refund := 0, epoch := w.epoch + 1 }

/-- Which bytes of `code` begin an instruction and are JUMPDEST: one bit each, in bytes of eight. -/
def jumpBits (code : @& ByteArray) : ByteArray :=
  go code 0 (ByteArray.mk (Array.replicate (code.size / 8 + 1) 0)) code.size
where
  go (code : @& ByteArray) (pc : Nat) (bits : ByteArray) : Nat → ByteArray
    | 0 => bits
    | fuel + 1 =>
      if pc < code.size then
        let op := code.get! pc
        if op == 0x5b then go code (pc + 1) (bits.set! (pc / 8) (bits.get! (pc / 8) ||| (1 <<< (pc % 8).toUInt8))) fuel
        else if op ≥ 0x60 && op ≤ 0x7f then go code (pc + 1 + (op.toNat - 0x5f)) bits fuel
        else go code (pc + 1) bits fuel
      else bits

/-- The jump destinations of a code that has a hash to be remembered by. -/
def jumpsOf (w : World) (hash : Word) (code : @& ByteArray) : World × ByteArray :=
  match w.jumps[hash]? with
  | some bits => (w, bits)
  | none =>
    let bits := jumpBits code
    ({ w with jumps := w.jumps.insert hash bits }, bits)

end World
end Fast
