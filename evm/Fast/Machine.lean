import Fast.State
import Fast.Wide

/-! What the fast engine's interpreter is handed and what it hands back: the block and the transaction it
runs in, the frame of one call, how a call ended, and the small things every instruction needs for memory
and gas. The loop itself is `Fast/Interp.lean`. -/

namespace Fast

/-- What the block fixes for everything that runs in it. -/
structure BlockEnv where
  coinbase : Word
  number : UInt64
  timestamp : UInt64
  gasLimit : UInt64
  prevRandao : Word
  baseFee : Word
  blobBaseFee : Word
  chainId : UInt64
  /-- The hash of the block with this number, for the 256 before this one; nothing for any other. -/
  blockHash : UInt64 → Word
  /-- Whether the rules are Osaka's or later (CLZ, a seventeenth precompile); otherwise Prague's. -/
  osaka : Bool

/-- What the transaction fixes. -/
structure TxEnv where
  origin : Word
  gasPrice : Word
  blobHashes : Array Word

/-- What a precompiled contract answered. A failure takes all the gas it was given. -/
structure Precompiled where
  success : Bool
  gasLeft : UInt64
  output : ByteArray

/-- What the engine does not do itself, yet: the precompiled contracts. -/
structure Host where
  isPrecompile : Word → Bool
  precompile : Word → ByteArray → UInt64 → Precompiled
  /-- What a call of a precompiled contract costs whoever runs it, by the address and the input, in a
  measure of the host's own (`World.work` is counted down in it). Gas does not say: it is priced for
  machines that do this arithmetic in a few microseconds. Nothing, where nobody counts. -/
  work : Word → ByteArray → UInt64 := fun _ _ => 0

/-- One call: whose code runs, on whose storage, for whom. -/
structure Frame where
  /-- The account whose storage and balance this is. -/
  address : Word
  caller : Word
  value : Word
  input : ByteArray
  code : ByteArray
  /-- A bit for each byte of the code: whether it may be jumped to. -/
  jumps : ByteArray
  static : Bool
  depth : UInt64
  /-- Where this call's stack begins in the stack all calls share, in words. -/
  base : USize

/-- How a call ended. `halt` is 0 for an end that keeps its changes (STOP, RETURN, SELFDESTRUCT), 1 for
REVERT, 2 for anything that takes all the gas. -/
structure Outcome where
  halt : UInt8
  gas : UInt64
  output : ByteArray
  stack : ByteArray
  world : World

/-- Where the engine picks up after a CALL or a CREATE: its own state as the instruction left it. `ok` false
is the instruction itself failing in a way that ends the caller (out of gas, a write in a static call). -/
structure Resumed where
  ok : Bool
  stack : ByteArray
  mem : ByteArray
  gas : UInt64
  ret : ByteArray
  world : World

/-- The words of stack a call may use. -/
def stackLimit : USize := 1024

/-- A run of zero bytes of at least `n`, made by doubling. -/
def zeros (n : Nat) : ByteArray :=
  go (ByteArray.mk (Array.replicate 64 0)) 64
where
  go (b : ByteArray) : Nat → ByteArray
    | 0 => b
    | fuel + 1 => if b.size < n then go (b ++ b) fuel else b

/-- A page of zeros, for the growth that is nearly always small. -/
def zeroPage : ByteArray := zeros 4096

/-- `b` made `size` bytes long with zeros, when it is shorter. -/
def grow (b : ByteArray) (size : Nat) : ByteArray :=
  if size ≤ b.size then b
  else
    let more := size - b.size
    if more ≤ zeroPage.size then zeroPage.copySlice 0 b b.size more
    else (zeros more).copySlice 0 b b.size more

/-- The shared stack made big enough for a call that begins at `base` to use all it may. -/
def room (stack : ByteArray) (base : USize) : ByteArray :=
  let need := (base.toNat + stackLimit.toNat) * 32
  if need ≤ stack.size then stack else grow stack (need + 16 * 1024 * 32)

/-- The gas that `words` words of memory cost in all. -/
@[inline] def memoryCost (words : UInt64) : UInt64 := 3 * words + words * words / 512

/-- A number no range of memory ends at: a range that can be paid for at no price. -/
def unpayable : UInt64 := 0xffffffffffffffff

/-- Where a range of memory ends, in bytes: nothing for an empty range wherever it is, and `unpayable` for
one that reaches past four gigabytes, which costs more gas than there is. -/
@[inline] def rangeEnd (off len : Word) : UInt64 :=
  if len.isZero then 0
  else if !off.small || !len.small || off.w0 > 0xffffffff || len.w0 > 0xffffffff then unpayable
  else off.w0 + len.w0

/-- The words in `bytes` bytes, rounded up. -/
@[inline] def wordsOf (bytes : UInt64) : UInt64 := (bytes + 31) >>> 5

/-- What it costs to have memory reach `stop`, given that it is `have_` bytes: nothing if it does already. -/
@[inline] def expansionCost (have_ stop : UInt64) : UInt64 :=
  if stop ≤ have_ then 0 else memoryCost (wordsOf stop) - memoryCost (have_ >>> 5)

/-- Memory grown to reach `stop`, in whole words. -/
@[inline] def reach (mem : ByteArray) (stop : UInt64) : ByteArray :=
  if stop ≤ mem.size.toUInt64 then mem else grow mem ((wordsOf stop) <<< 5).toNat

/-- `len` bytes of `src` from `srcOff` copied to `dst` in memory, with zeros for what `src` does not have.
Memory already reaches `dst + len`. -/
def copyIn (mem : ByteArray) (dst : Nat) (src : @& ByteArray) (srcOff : Word) (len : Nat) : ByteArray :=
  if len == 0 then mem else
  let start := if srcOff.small && srcOff.w0 < src.size.toUInt64 then srcOff.w0.toNat else src.size
  let there := min len (src.size - start)
  let mem := if there == 0 then mem else src.copySlice start mem dst there
  if there == len then mem
  else
    let rest := len - there
    if rest ≤ zeroPage.size then zeroPage.copySlice 0 mem (dst + there) rest
    else (zeros rest).copySlice 0 mem (dst + there) rest

/-- A word read from `b` at `off`, most significant byte first, with zeros for bytes that are not there. -/
def wordAt (b : @& ByteArray) (off : Word) : Word :=
  if !off.small || off.w0 ≥ b.size.toUInt64 then Word.zero
  else
    let start := off.w0.toUSize
    if h : start.toNat + 31 < b.size then Word.ofBytes b start h
    else
      let padded := copyIn (ByteArray.mk (Array.replicate 32 0)) 0 b off 32
      if h : (0 : USize).toNat + 31 < padded.size then Word.ofBytes padded 0 h else Word.zero

/-- A word written into memory at `off`, most significant byte first. Memory already reaches `off + 32`. -/
@[inline] def putWord (mem : ByteArray) (off : USize) (x : Word) : ByteArray :=
  store (store (store (store mem off (swap x.w3)) (off + 8) (swap x.w2)) (off + 16) (swap x.w1)) (off + 24) (swap x.w0)

/-- Whether byte `dest` of a code may be jumped to, by its bits. -/
@[inline] def jumpable (jumps : @& ByteArray) (dest : UInt64) : Bool :=
  let i := (dest >>> 3).toUSize
  if h : i.toNat < jumps.size then (jumps.uget i h >>> (dest &&& 7).toUInt8) &&& 1 == 1 else false

/-- The address a CREATE makes: the hash of the sender and its nonce as RLP. -/
def createAddress (sender : Word) (nonce : UInt64) : Word :=
  let n : ByteArray :=
    if nonce == 0 then ⟨#[0x80]⟩
    else if nonce < 0x80 then ⟨#[nonce.toUInt8]⟩
    else
      let digits := (Word.ofUInt64 nonce).bytes.extract (32 - nonce.toNat.log2 / 8 - 1) 32
      (ByteArray.mk #[(0x80 + digits.size).toUInt8]) ++ digits
  let body := (ByteArray.mk #[0x94]) ++ sender.addressBytes ++ n
  (keccak ((ByteArray.mk #[(0xc0 + body.size).toUInt8]) ++ body)).address

/-- The address a CREATE2 makes: the hash of 0xff, the sender, the salt and the hash of the code. -/
def create2Address (sender salt : Word) (initcode : @& ByteArray) : Word :=
  (keccak ((ByteArray.mk #[0xff]) ++ sender.addressBytes ++ salt.bytes ++ (keccak initcode).bytes)).address

/-- Whether a code is a delegation (EIP-7702): the three bytes that say so, then an address. -/
def delegate? (code : @& ByteArray) : Option Word :=
  if code.size == 23 && code.get! 0 == 0xef && code.get! 1 == 0x01 && code.get! 2 == 0x00 then
    some (wordAt ((ByteArray.mk (Array.replicate 12 0)) ++ code.extract 3 23) Word.zero)
  else none

end Fast
