import Fast.Machine

/-! The fast engine's interpreter: one loop over the instructions of a call.

The loop is the function `run`. What changes at nearly every instruction (the stack, how deep it is, the
program counter, the gas) is each an argument of its own, so an ordinary instruction is the loop going
round with new arguments and allocates nothing; the stack is one run of bytes that every call shares, each
call using the part above where it began. Memory, the last call's return data and the world are arguments
too. A CALL or a CREATE runs the loop again for the new call, as an ordinary call of the function, and
picks up where it was when that returns.

Instructions that are short and common are written into the loop. The rest are functions outside it that
take what they need and give it back, so that the loop stays a size the C compiler can do well by.

Every access to the stack is checked against the bytes that are there, and an instruction that would run a
call's stack under its beginning or over its limit ends the call with all its gas gone, as do an
instruction that is not one, a jump to what is not a destination, and a write in a call that may not
write. `fuel` is only there to show the loop ends: every instruction that does not end the call costs gas,
so there are never more to run than there is gas. -/

namespace Fast

/-- Where in the shared stack the word `i` down from the top is, in bytes: 1 is the top. -/
@[inline] def slot (sp i : USize) : USize := (sp - i) <<< 5

/-- The word at `off` handed to what follows, or `bad` if the stack does not reach. -/
@[inline] def rd {α : Type} (stack : @& ByteArray) (off : USize) (bad : Unit → α) (k : Word → α) : α :=
  if h : off.toNat + 31 < stack.size then
    k ⟨loadAt stack off 0 (by omega), loadAt stack off 8 (by omega),
       loadAt stack off 16 (by omega), loadAt stack off 24 (by omega)⟩
  else bad ()

@[inline] def wr (stack : ByteArray) (off : USize) (x : Word) : ByteArray :=
  store (store (store (store stack off x.w0) (off + 8) x.w1) (off + 16) x.w2) (off + 24) x.w3

/-- A word of the stack for code outside the loop, which may build it. -/
def peek (stack : @& ByteArray) (sp i : USize) : Word := rd stack (slot sp i) (fun _ => Word.zero) id

/-- A call ending with all its gas gone. -/
@[inline] def lost (stack : ByteArray) (world : World) : Outcome := ⟨2, 0, ByteArray.empty, stack, world⟩

/-! ## Instructions outside the loop -/

@[noinline] def mulOp (stack : ByteArray) (sp : USize) : ByteArray :=
  rd stack (slot sp 1) (fun _ => stack) fun a => rd stack (slot sp 2) (fun _ => stack) fun b =>
  wr stack (slot sp 2) (Word.mul a b)

/-- An operation on the top two words that is not worth a place in the loop: its number picks it. -/
@[noinline] def binaryOp (op : UInt8) (stack : ByteArray) (sp : USize) : ByteArray :=
  rd stack (slot sp 1) (fun _ => stack) fun a => rd stack (slot sp 2) (fun _ => stack) fun b =>
  wr stack (slot sp 2) (
    match op with
    | 0x04 => Word.div a b
    | 0x05 => Word.sdiv a b
    | 0x06 => Word.mod a b
    | 0x07 => Word.smod a b
    | 0x0a => Word.exp a b
    | 0x0b => Word.signExtend a b
    | 0x12 => Word.ofBool (Word.slt a b)
    | 0x13 => Word.ofBool (Word.sgt a b)
    | 0x1a => Word.byte a b
    | 0x1b => Word.shl a b
    | 0x1c => Word.shr a b
    | _ => Word.sar a b)

@[noinline] def ternaryOp (op : UInt8) (stack : ByteArray) (sp : USize) : ByteArray :=
  rd stack (slot sp 1) (fun _ => stack) fun a => rd stack (slot sp 2) (fun _ => stack) fun b =>
  rd stack (slot sp 3) (fun _ => stack) fun n =>
  wr stack (slot sp 3) (if op == 0x08 then Word.addmod a b n else Word.mulmod a b n)

/-- The word a PUSH pushes when its bytes run into the last 32 of the code, where they cannot be read as
a whole word: a byte at a time, with nothing for bytes past the end. -/
def pushedSlow (code : @& ByteArray) : Nat → USize → UInt64 → UInt64 → UInt64 → UInt64 → Word
  | 0, _, w0, w1, w2, w3 => ⟨w0, w1, w2, w3⟩
  | left + 1, i, w0, w1, w2, w3 =>
    let byte : UInt64 := if h : i.toNat < code.size then (code.uget i h).toUInt64 else 0
    pushedSlow code left (i + 1) ((w0 <<< 8) ||| byte) ((w1 <<< 8) ||| (w0 >>> 56)) ((w2 <<< 8) ||| (w1 >>> 56))
      ((w3 <<< 8) ||| (w2 >>> 56))

/-- The word a PUSH of `n` bytes at `pc` pushes, handed on as its four machine words. It is handed on that
way, and not as a word, because the two ways of reading it meet again afterwards, and where two ways meet
a word would have to be built to be carried across; four numbers are carried as they are. -/
@[inline] def pushed {α : Type} (code : @& ByteArray) (pc : USize) (n : UInt64)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  let from_ := pc + 1
  if h : from_.toNat + 31 < code.size then
    let w := (Word.ofBytes code from_ h).shrSmall ((32 - n) <<< 3)
    k w.w0 w.w1 w.w2 w.w3
  else
    let w := pushedSlow code n.toNat from_ 0 0 0 0
    k w.w0 w.w1 w.w2 w.w3

/-- SLOAD: the world, the value, and the gas left; `unpayable` gas left is not enough gas. The price is
known from whether the slot is warm, before anything is fetched, and a slot that cannot be paid for is not
fetched: what an instruction could not afford to read, it did not read, and a witness need not prove it. -/
def sload (world : World) (address key : Word) (gas : UInt64) : World × Word × UInt64 :=
  let cost : UInt64 := if world.slotIsWarm address key then 100 else 2100
  if gas < cost then (world, Word.zero, unpayable) else
  let (world, entry, _) := world.warmSlot address key
  (world, entry.value, gas - cost)

/-- SSTORE: the world, the gas left, and whether there was enough (EIP-2200, 2929, 3529). -/
def sstore (world : World) (address key value : Word) (gas : UInt64) : World × UInt64 × Bool :=
  if gas ≤ 2300 then (world, 0, false) else
  let (world, entry, cold) := world.warmSlot address key
  let current := entry.value
  let original := entry.original
  let base : UInt64 :=
    if value == current then 100
    else if current == original then (if original.isZero then 20000 else 2900)
    else 100
  let cost := base + (if cold then 2100 else 0)
  if gas < cost then (world, 0, false) else
  if value == current then (world, gas - cost, true) else
  let world :=
    if current == original then
      if !original.isZero && value.isZero then world.addRefund 4800 else world
    else
      let world :=
        if original.isZero then world
        else if current.isZero then world.subRefund 4800
        else if value.isZero then world.addRefund 4800
        else world
      if value == original then world.addRefund (if original.isZero then 19900 else 2800) else world
  (world.setSlot address key entry value, gas - cost, true)

/-- An account looked at from outside (BALANCE, EXTCODESIZE, EXTCODEHASH, EXTCODECOPY): the world with it
warm, the account, and the gas left after the look and `more` besides; `unpayable` gas left is not enough
gas, and then the account was not fetched. -/
def look (world : World) (address : Word) (code : Bool) (gas more : UInt64) : World × Account × UInt64 :=
  let (world, cold) := world.warm address
  let cost := (if cold then 2600 else 100) + more
  if gas < cost then (world, World.noAccount, unpayable) else
  let (world, entry) := if code then world.withCode address else world.account address
  (world, entry, gas - cost)

/-- The bytes of memory from `off` for `len`, as an array of their own. -/
def slice (mem : @& ByteArray) (off len : Word) : ByteArray :=
  if len.isZero then ByteArray.empty else mem.extract off.w0.toNat (off.w0.toNat + len.w0.toNat)

/-- What a call left in the caller's memory: as much of its output as the caller made room for. -/
def returned (mem : ByteArray) (retOff retLen : Word) (output : @& ByteArray) : ByteArray :=
  if retLen.isZero || output.size == 0 then mem
  else output.copySlice 0 mem retOff.w0.toNat (min retLen.w0.toNat output.size)

/-- A CALL or a CREATE made ready. Either there is a call to run (`enter`): `frame` with `childGas`, on
`stack` and `world`, and the rest says how to pick up after it. Or there is none, because the instruction
failed, or could not start a call, or the call was one the engine answers without running code; then this
is where the caller picks up, as `Resumed` has it. -/
structure Prepared where
  enter : Bool
  ok : Bool
  stack : ByteArray
  mem : ByteArray
  /-- The caller's gas, without what the call was given. -/
  gas : UInt64
  ret : ByteArray
  world : World
  frame : Frame
  childGas : UInt64
  /-- Where on the stack the answer goes. -/
  answerAt : USize
  retOff : Word
  retLen : Word
  mark : Checkpoint
  /-- The address being created, for a CREATE. -/
  target : Word

def noFrame : Frame :=
  { address := Word.zero, caller := Word.zero, value := Word.zero, input := ByteArray.empty, code := ByteArray.empty,
    jumps := ByteArray.empty, static := false, depth := 0, base := 0 }

/-- The instruction itself failed: the caller ends with its gas gone. -/
def Prepared.failed (stack mem : ByteArray) (world : World) : Prepared :=
  ⟨false, false, stack, mem, 0, ByteArray.empty, world, noFrame, 0, 0, Word.zero, Word.zero, ⟨0, 0, 0⟩, Word.zero⟩

/-- No call was run and the caller goes on. -/
def Prepared.resumed (r : Resumed) : Prepared :=
  ⟨false, r.ok, r.stack, r.mem, r.gas, r.ret, r.world, noFrame, 0, 0, Word.zero, Word.zero, ⟨0, 0, 0⟩, Word.zero⟩

/-- After a call: its answer on the stack, its output where the caller made room for it, its gas back, and
its changes undone unless it ended well. -/
def settleCall (answerAt : USize) (retOff retLen : Word) (mark : Checkpoint) (mem : ByteArray) (gas : UInt64)
    (out : Outcome) : Resumed :=
  if out.halt == 0 then
    ⟨true, wr out.stack answerAt Word.one, returned mem retOff retLen out.output, gas + out.gas, out.output, out.world⟩
  else if out.halt == 1 then
    ⟨true, wr out.stack answerAt Word.zero, returned mem retOff retLen out.output, gas + out.gas, out.output,
     out.world.revert mark⟩
  else ⟨true, wr out.stack answerAt Word.zero, mem, gas, ByteArray.empty, out.world.revert mark⟩

/-- After the code of a CREATE: what it returned becomes the new account's code, if it may and can be paid
for, and the address goes on the stack; otherwise nothing was created. -/
def settleCreate (answerAt : USize) (target : Word) (mark : Checkpoint) (mem : ByteArray) (gas : UInt64)
    (out : Outcome) : Resumed :=
  if out.halt == 0 then
    let code := out.output
    let deposit := 200 * code.size.toUInt64
    if code.size > 24576 || (code.size > 0 && code.get! 0 == 0xef) || out.gas < deposit then
      ⟨true, wr out.stack answerAt Word.zero, mem, gas, ByteArray.empty, out.world.revert mark⟩
    else
      ⟨true, wr out.stack answerAt target, mem, gas + (out.gas - deposit), ByteArray.empty, out.world.setCode target code⟩
  else if out.halt == 1 then
    ⟨true, wr out.stack answerAt Word.zero, mem, gas + out.gas, out.output, out.world.revert mark⟩
  else ⟨true, wr out.stack answerAt Word.zero, mem, gas, ByteArray.empty, out.world.revert mark⟩

/-- CALL, CALLCODE, DELEGATECALL and STATICCALL, by their numbers, up to the call itself. -/
def prepareCall (kind : UInt8) (host : @& Host) (f : @& Frame)
    (stack : ByteArray) (sp : USize) (mem : ByteArray) (gas : UInt64) (world : World) : Prepared :=
  let hasValue := kind == 0xf1 || kind == 0xf2
  let n : USize := if hasValue then 7 else 6
  if sp - f.base < n then .failed stack mem world else
  let gasWord := peek stack sp 1
  let target := (peek stack sp 2).address
  let value := if hasValue then peek stack sp 3 else Word.zero
  let argsOff := peek stack sp (n - 3)
  let argsLen := peek stack sp (n - 2)
  let retOff := peek stack sp (n - 1)
  let retLen := peek stack sp n
  if kind == 0xf1 && f.static && !value.isZero then .failed stack mem world else
  let stop := max (rangeEnd argsOff argsLen) (rangeEnd retOff retLen)
  if stop == unpayable then .failed stack mem world else
  let memoryGas := expansionCost mem.size.toUInt64 stop
  if gas < memoryGas then .failed stack mem world else
  let gas := gas - memoryGas
  let mem := reach mem stop
  let (world, cold) := world.warm target
  let access : UInt64 := if cold then 2600 else 100
  -- An account that cannot be paid for is not fetched.
  if gas < access then .failed stack mem world else
  let (world, account) := world.withCode target
  -- The code that runs: the account's own, or, when that is a delegation, the code of the account it
  -- names, which is looked at and paid for like any other. One step only.
  let (world, code, codeHash, delegation) : World × ByteArray × Word × UInt64 :=
    match delegate? account.code with
    | some named =>
      let (world, namedCold) := world.warm named
      let namedAccess : UInt64 := if namedCold then 2600 else 100
      if gas < access + namedAccess then (world, ByteArray.empty, emptyCodeHash, unpayable)
      else
        let (world, namedAccount) := world.withCode named
        (world, namedAccount.code, namedAccount.codeHash, namedAccess)
    | none => (world, account.code, account.codeHash, 0)
  if delegation == unpayable then .failed stack mem world else
  let extra : UInt64 := access + delegation + (if value.isZero then 0 else 9000) +
    (if kind == 0xf1 && !value.isZero && account.empty then 25000 else 0)
  if gas < extra then .failed stack mem world else
  let gas := gas - extra
  -- All but a 64th of what is left may go to the call, and no more than was asked for.
  let most := gas - gas / 64
  let given := if gasWord.small && gasWord.w0 < most then gasWord.w0 else most
  let gas := gas - given
  let childGas := given + (if value.isZero then 0 else 2300)
  let answerAt := slot sp n
  let (world, self) := world.account f.address
  if f.depth ≥ 1024 || (hasValue && self.balance.lt value) then
    .resumed ⟨true, wr stack answerAt Word.zero, mem, gas + childGas, ByteArray.empty, world⟩
  else
  let mark := world.checkpoint
  let world := if kind == 0xf1 && !value.isZero then (world.debit f.address value).credit target value else world
  let input := slice mem argsOff argsLen
  if host.isPrecompile target then
    -- A contract the transaction has no work left for is not run: the call fails, the world is marked.
    let (world, may) := world.afford (host.work target input)
    if !may then .resumed (settleCall answerAt retOff retLen mark mem gas (lost stack world)) else
    let answer := host.precompile target input childGas
    .resumed (settleCall answerAt retOff retLen mark mem gas
      (if answer.success then ⟨0, answer.gasLeft, answer.output, stack, world⟩ else lost stack world))
  else if code.size == 0 then
    .resumed (settleCall answerAt retOff retLen mark mem gas ⟨0, childGas, ByteArray.empty, stack, world⟩)
  else
    let (world, jumps) := world.jumpsOf codeHash code
    { enter := true, ok := true, stack, mem, gas, ret := ByteArray.empty, world, childGas, answerAt, retOff, retLen, mark,
      target := Word.zero,
      frame := { address := if kind == 0xf1 || kind == 0xfa then target else f.address,
                 caller := if kind == 0xf4 then f.caller else f.address,
                 value := if kind == 0xf4 then f.value else value,
                 input, code, jumps, static := f.static || kind == 0xfa, depth := f.depth + 1, base := sp } }

/-- CREATE and CREATE2, by their numbers, up to running the code that makes the account. -/
def prepareCreate (kind : UInt8) (f : @& Frame)
    (stack : ByteArray) (sp : USize) (mem : ByteArray) (gas : UInt64) (world : World) : Prepared :=
  let n : USize := if kind == 0xf5 then 4 else 3
  if sp - f.base < n || f.static then .failed stack mem world else
  let value := peek stack sp 1
  let off := peek stack sp 2
  let len := peek stack sp 3
  let salt := if kind == 0xf5 then peek stack sp 4 else Word.zero
  let stop := rangeEnd off len
  if stop == unpayable || len.w0 > 49152 then .failed stack mem world else
  let words := wordsOf len.w0
  let cost := expansionCost mem.size.toUInt64 stop + 32000 + 2 * words + (if kind == 0xf5 then 6 * words else 0)
  if gas < cost then .failed stack mem world else
  let gas := gas - cost
  let mem := reach mem stop
  let initcode := slice mem off len
  let answerAt := slot sp n
  let (world, self) := world.account f.address
  if f.depth ≥ 1024 || self.balance.lt value || self.nonce == 0xffffffffffffffff then
    .resumed ⟨true, wr stack answerAt Word.zero, mem, gas, ByteArray.empty, world⟩
  else
  let given := gas - gas / 64
  let gas := gas - given
  let world := world.setNonce f.address (self.nonce + 1)
  let target := if kind == 0xf5 then create2Address f.address salt initcode else createAddress f.address self.nonce
  let (world, _) := world.warm target
  let (world, there) := world.account target
  -- An address that already has a nonce, code or storage is not created over: the attempt fails and takes
  -- the gas it was given.
  if there.nonce != 0 || there.codeHash != emptyCodeHash || !(there.fresh || there.storageWasEmpty) then
    .resumed ⟨true, wr stack answerAt Word.zero, mem, gas, ByteArray.empty, world⟩
  else
  let mark := world.checkpoint
  let world := ((world.create target).debit f.address value).credit target value
  { enter := true, ok := true, stack, mem, gas, ret := ByteArray.empty, world, childGas := given, answerAt,
    retOff := Word.zero, retLen := Word.zero, mark, target,
    frame := { address := target, caller := f.address, value, input := ByteArray.empty, code := initcode,
               jumps := World.jumpBits initcode, static := false, depth := f.depth + 1, base := sp } }

/-- CREATE, CREATE2 and the four calls, by their numbers, up to the call. -/
@[noinline] def prepare (op : UInt8) (host : @& Host) (f : @& Frame)
    (stack : ByteArray) (sp : USize) (mem : ByteArray) (gas : UInt64) (world : World) : Prepared :=
  if op == 0xf0 || op == 0xf5 then prepareCreate op f stack sp mem gas world
  else prepareCall op host f stack sp mem gas world

/-- And after it. -/
@[noinline] def settle (op : UInt8) (answerAt : USize) (retOff retLen : Word) (mark : Checkpoint) (target : Word)
    (mem : ByteArray) (gas : UInt64) (out : Outcome) : Resumed :=
  if op == 0xf0 || op == 0xf5 then settleCreate answerAt target mark mem gas out
  else settleCall answerAt retOff retLen mark mem gas out

/-- How many words shorter the stack is after one of them: its arguments off and its answer on. -/
@[inline] def popped (op : UInt8) : USize :=
  if op == 0xf0 then 2 else if op == 0xf5 then 3 else if op == 0xf1 || op == 0xf2 then 6 else 5

/-- SELFDESTRUCT: the world, the gas left, and whether there was enough (EIP-6780). -/
def selfDestruct (world : World) (address beneficiary : Word) (gas : UInt64) : World × UInt64 × Bool :=
  let (world, cold) := world.warm beneficiary
  let access : UInt64 := 5000 + (if cold then 2600 else 0)
  if gas < access then (world, 0, false) else
  let (world, self) := world.account address
  let (world, heir) := world.account beneficiary
  let cost : UInt64 := access + (if !self.balance.isZero && heir.empty then 25000 else 0)
  if gas < cost then (world, 0, false) else
  let world :=
    if beneficiary == address then world
    else (world.debit address self.balance).credit beneficiary self.balance
  -- Only an account made in this same transaction is removed, at the transaction's end, with whatever it
  -- holds then. What it held now has gone to the beneficiary, and when that is itself it is burnt, now:
  -- an account that has destroyed itself and is called again in the same transaction has nothing.
  let world :=
    if self.createdAt == world.epoch then
      (if beneficiary == address then world.setBalance address Word.zero else world).destruct address
    else world
  (world, gas - cost, true)

/-- The topics of a LOG, read from under its two memory arguments. -/
def topicsOf (stack : @& ByteArray) (sp : USize) (count : USize) : Array Word :=
  go stack sp count.toNat 0 #[]
where
  go (stack : @& ByteArray) (sp : USize) : Nat → USize → Array Word → Array Word
    | 0, _, topics => topics
    | left + 1, i, topics => go stack sp left (i + 1) (topics.push (peek stack sp (3 + i)))

/-! ## The loop -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
/-- Runs the call `f` from where it stands until it ends. -/
def run (blk : @& BlockEnv) (tx : @& TxEnv) (host : @& Host) (f : @& Frame) :
    Nat → ByteArray → USize → ByteArray → USize → UInt64 → ByteArray → World → Outcome
  | 0, stack, _, _, _, _, _, world => lost stack world
  | fuel + 1, stack, sp, mem, pc, gas, ret, world =>
    if hpc : pc.toNat < f.code.size then
      let op := f.code.uget pc hpc
      let depth := sp - f.base
      if op ≥ 0x60 && op ≤ 0x7f then
        -- PUSH1 to PUSH32
        if gas < 3 || depth ≥ stackLimit then lost stack world else
        let n := (op - 0x5f).toUInt64
        pushed f.code pc n fun w0 w1 w2 w3 =>
        run blk tx host f fuel (wr stack (sp <<< 5) ⟨w0, w1, w2, w3⟩) (sp + 1) mem (pc + 1 + n.toUSize) (gas - 3) ret world
      else if op ≥ 0x80 && op ≤ 0x8f then
        -- DUP1 to DUP16
        let n := (op - 0x7f).toUSize
        if gas < 3 || depth < n || depth ≥ stackLimit then lost stack world else
        rd stack (slot sp n) (fun _ => lost stack world) fun a =>
        run blk tx host f fuel (wr stack (sp <<< 5) a) (sp + 1) mem (pc + 1) (gas - 3) ret world
      else if op ≥ 0x90 && op ≤ 0x9f then
        -- SWAP1 to SWAP16
        let n := (op - 0x8f).toUSize
        if gas < 3 || depth < n + 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a =>
        rd stack (slot sp (n + 1)) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr (wr stack (slot sp 1) b) (slot sp (n + 1)) a) sp mem (pc + 1) (gas - 3) ret world
      else
      match op with
      | 0x00 => ⟨0, gas, ByteArray.empty, stack, world⟩
      | 0x01 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.add a b)) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x02 =>
        if gas < 5 || depth < 2 then lost stack world else
        run blk tx host f fuel (mulOp stack sp) (sp - 1) mem (pc + 1) (gas - 5) ret world
      | 0x03 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.sub a b)) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x04 | 0x05 | 0x06 | 0x07 | 0x0b =>
        if gas < 5 || depth < 2 then lost stack world else
        run blk tx host f fuel (binaryOp op stack sp) (sp - 1) mem (pc + 1) (gas - 5) ret world
      | 0x08 | 0x09 =>
        if gas < 8 || depth < 3 then lost stack world else
        run blk tx host f fuel (ternaryOp op stack sp) (sp - 2) mem (pc + 1) (gas - 8) ret world
      | 0x0a =>
        -- EXP: ten, and fifty for each byte of the exponent
        if depth < 2 then lost stack world else
        rd stack (slot sp 2) (fun _ => lost stack world) fun e =>
        let cost := 10 + 50 * e.byteLength
        if gas < cost then lost stack world else
        run blk tx host f fuel (binaryOp op stack sp) (sp - 1) mem (pc + 1) (gas - cost) ret world
      | 0x10 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.ofBool (Word.lt a b))) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x11 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.ofBool (Word.gt a b))) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x12 | 0x13 | 0x1a | 0x1b | 0x1c | 0x1d =>
        if gas < 3 || depth < 2 then lost stack world else
        run blk tx host f fuel (binaryOp op stack sp) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x14 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.ofBool (Word.eq a b))) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x15 =>
        if gas < 3 || depth < 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a =>
        run blk tx host f fuel (wr stack (slot sp 1) (Word.ofBool a.isZero)) sp mem (pc + 1) (gas - 3) ret world
      | 0x16 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.and a b)) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x17 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.or a b)) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x18 =>
        if gas < 3 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a => rd stack (slot sp 2) (fun _ => lost stack world) fun b =>
        run blk tx host f fuel (wr stack (slot sp 2) (Word.xor a b)) (sp - 1) mem (pc + 1) (gas - 3) ret world
      | 0x19 =>
        if gas < 3 || depth < 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a =>
        run blk tx host f fuel (wr stack (slot sp 1) a.not) sp mem (pc + 1) (gas - 3) ret world
      | 0x1e =>
        -- CLZ, from Osaka on
        if !blk.osaka || gas < 5 || depth < 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun a =>
        run blk tx host f fuel (wr stack (slot sp 1) a.clz) sp mem (pc + 1) (gas - 5) ret world
      | 0x20 =>
        -- KECCAK256
        if depth < 2 then lost stack world else
        let off := peek stack sp 1
        let len := peek stack sp 2
        let stop := rangeEnd off len
        if stop == unpayable then lost stack world else
        let cost := 30 + 6 * wordsOf len.w0 + expansionCost mem.size.toUInt64 stop
        if gas < cost then lost stack world else
        let mem := reach mem stop
        let hash := Word.ofDigest (Keccak.hash mem off.w0.toNat len.w0.toNat)
        run blk tx host f fuel (wr stack (slot sp 2) hash) (sp - 1) mem (pc + 1) (gas - cost) ret world
      | 0x30 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) f.address) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x31 =>
        -- BALANCE
        if depth < 1 then lost stack world else
        let (world, account, gas) := look world (peek stack sp 1).address false gas 0
        if gas == unpayable then lost stack world else
        run blk tx host f fuel (wr stack (slot sp 1) account.balance) sp mem (pc + 1) gas ret world
      | 0x32 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) tx.origin) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x33 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) f.caller) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x34 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) f.value) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x35 =>
        -- CALLDATALOAD
        if gas < 3 || depth < 1 then lost stack world else
        run blk tx host f fuel (wr stack (slot sp 1) (wordAt f.input (peek stack sp 1))) sp mem (pc + 1) (gas - 3) ret world
      | 0x36 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 f.input.size.toUInt64)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x37 | 0x39 | 0x3e =>
        -- CALLDATACOPY, CODECOPY, RETURNDATACOPY: to memory, from an offset, so many bytes
        if depth < 3 then lost stack world else
        let dst := peek stack sp 1
        let from_ := peek stack sp 2
        let len := peek stack sp 3
        let stop := rangeEnd dst len
        if stop == unpayable then lost stack world else
        let cost := 3 + 3 * wordsOf len.w0 + expansionCost mem.size.toUInt64 stop
        if gas < cost then lost stack world else
        -- Return data, unlike the others, has no zeros past its end: reading there ends the call.
        -- (The sum of the two is not taken: it can wrap round past the end of a machine word.)
        if op == 0x3e && (!from_.small || !len.small || from_.w0 > ret.size.toUInt64 ||
            len.w0 > ret.size.toUInt64 - from_.w0) then lost stack world else
        let mem := reach mem stop
        let mem := copyIn mem dst.w0.toNat (if op == 0x37 then f.input else if op == 0x39 then f.code else ret) from_ len.w0.toNat
        run blk tx host f fuel stack (sp - 3) mem (pc + 1) (gas - cost) ret world
      | 0x38 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 f.code.size.toUInt64)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x3a =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) tx.gasPrice) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x3b =>
        -- EXTCODESIZE
        if depth < 1 then lost stack world else
        let (world, account, gas) := look world (peek stack sp 1).address true gas 0
        if gas == unpayable then lost stack world else
        run blk tx host f fuel (wr stack (slot sp 1) (Word.ofUInt64 account.code.size.toUInt64)) sp mem (pc + 1) gas ret world
      | 0x3c =>
        -- EXTCODECOPY
        if depth < 4 then lost stack world else
        let dst := peek stack sp 2
        let from_ := peek stack sp 3
        let len := peek stack sp 4
        let stop := rangeEnd dst len
        if stop == unpayable then lost stack world else
        let (world, account, gas) := look world (peek stack sp 1).address true gas
          (3 * wordsOf len.w0 + expansionCost mem.size.toUInt64 stop)
        if gas == unpayable then lost stack world else
        let mem := copyIn (reach mem stop) dst.w0.toNat account.code from_ len.w0.toNat
        run blk tx host f fuel stack (sp - 4) mem (pc + 1) gas ret world
      | 0x3d =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 ret.size.toUInt64)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x3f =>
        -- EXTCODEHASH: nothing for an account that is not there or counts as nothing
        if depth < 1 then lost stack world else
        let (world, account, gas) := look world (peek stack sp 1).address false gas 0
        if gas == unpayable then lost stack world else
        run blk tx host f fuel (wr stack (slot sp 1) (if account.empty then Word.zero else account.codeHash)) sp mem (pc + 1) gas ret world
      | 0x40 =>
        -- BLOCKHASH: of one of the 256 blocks before this one
        if gas < 20 || depth < 1 then lost stack world else
        let n := peek stack sp 1
        let hash := if n.small && n.w0 < blk.number && blk.number - n.w0 ≤ 256 then blk.blockHash n.w0 else Word.zero
        run blk tx host f fuel (wr stack (slot sp 1) hash) sp mem (pc + 1) (gas - 20) ret world
      | 0x41 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) blk.coinbase) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x42 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 blk.timestamp)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x43 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 blk.number)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x44 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) blk.prevRandao) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x45 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 blk.gasLimit)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x46 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 blk.chainId)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x47 =>
        -- SELFBALANCE
        if gas < 5 || depth ≥ stackLimit then lost stack world else
        let (world, account) := world.account f.address
        run blk tx host f fuel (wr stack (sp <<< 5) account.balance) (sp + 1) mem (pc + 1) (gas - 5) ret world
      | 0x48 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) blk.baseFee) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x49 =>
        -- BLOBHASH
        if gas < 3 || depth < 1 then lost stack world else
        let i := peek stack sp 1
        let hash := if i.small && i.w0 < tx.blobHashes.size.toUInt64 then tx.blobHashes.getD i.w0.toNat Word.zero else Word.zero
        run blk tx host f fuel (wr stack (slot sp 1) hash) sp mem (pc + 1) (gas - 3) ret world
      | 0x4a =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) blk.blobBaseFee) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x50 =>
        if gas < 2 || depth < 1 then lost stack world else
        run blk tx host f fuel stack (sp - 1) mem (pc + 1) (gas - 2) ret world
      | 0x51 =>
        -- MLOAD
        if depth < 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun off =>
        if !off.small || off.w0 > 0xffffffff then lost stack world else
        let cost := 3 + expansionCost mem.size.toUInt64 (off.w0 + 32)
        if gas < cost then lost stack world else
        let mem := reach mem (off.w0 + 32)
        let at_ := off.w0.toUSize
        if h : at_.toNat + 31 < mem.size then
          run blk tx host f fuel (wr stack (slot sp 1) (Word.ofBytes mem at_ h)) sp mem (pc + 1) (gas - cost) ret world
        else lost stack world
      | 0x52 =>
        -- MSTORE
        if depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun off =>
        rd stack (slot sp 2) (fun _ => lost stack world) fun value =>
        if !off.small || off.w0 > 0xffffffff then lost stack world else
        let cost := 3 + expansionCost mem.size.toUInt64 (off.w0 + 32)
        if gas < cost then lost stack world else
        run blk tx host f fuel stack (sp - 2) (putWord (reach mem (off.w0 + 32)) off.w0.toUSize value) (pc + 1) (gas - cost) ret world
      | 0x53 =>
        -- MSTORE8
        if depth < 2 then lost stack world else
        let off := peek stack sp 1
        let value := peek stack sp 2
        if !off.small || off.w0 > 0xffffffff then lost stack world else
        let cost := 3 + expansionCost mem.size.toUInt64 (off.w0 + 1)
        if gas < cost then lost stack world else
        run blk tx host f fuel stack (sp - 2) ((reach mem (off.w0 + 1)).set! off.w0.toNat value.w0.toUInt8) (pc + 1) (gas - cost) ret world
      | 0x54 =>
        -- SLOAD
        if depth < 1 then lost stack world else
        let (world, value, gas) := sload world f.address (peek stack sp 1) gas
        if gas == unpayable then lost stack world else
        run blk tx host f fuel (wr stack (slot sp 1) value) sp mem (pc + 1) gas ret world
      | 0x55 =>
        -- SSTORE
        if depth < 2 || f.static then lost stack world else
        let (world, gas, ok) := sstore world f.address (peek stack sp 1) (peek stack sp 2) gas
        if !ok then lost stack world else
        run blk tx host f fuel stack (sp - 2) mem (pc + 1) gas ret world
      | 0x56 =>
        -- JUMP
        if gas < 8 || depth < 1 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun dest =>
        if !dest.small || !jumpable f.jumps dest.w0 then lost stack world else
        run blk tx host f fuel stack (sp - 1) mem dest.w0.toUSize (gas - 8) ret world
      | 0x57 =>
        -- JUMPI
        if gas < 10 || depth < 2 then lost stack world else
        rd stack (slot sp 1) (fun _ => lost stack world) fun dest =>
        rd stack (slot sp 2) (fun _ => lost stack world) fun condition =>
        if condition.isZero then run blk tx host f fuel stack (sp - 2) mem (pc + 1) (gas - 10) ret world
        else if !dest.small || !jumpable f.jumps dest.w0 then lost stack world
        else run blk tx host f fuel stack (sp - 2) mem dest.w0.toUSize (gas - 10) ret world
      | 0x58 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 pc.toUInt64)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x59 =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 mem.size.toUInt64)) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x5a =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) (Word.ofUInt64 (gas - 2))) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0x5b =>
        if gas < 1 then lost stack world else run blk tx host f fuel stack sp mem (pc + 1) (gas - 1) ret world
      | 0x5c =>
        -- TLOAD
        if gas < 100 || depth < 1 then lost stack world else
        let value := world.transientGet f.address (peek stack sp 1)
        run blk tx host f fuel (wr stack (slot sp 1) value) sp mem (pc + 1) (gas - 100) ret world
      | 0x5d =>
        -- TSTORE
        if gas < 100 || depth < 2 || f.static then lost stack world else
        let world := world.transientSet f.address (peek stack sp 1) (peek stack sp 2)
        run blk tx host f fuel stack (sp - 2) mem (pc + 1) (gas - 100) ret world
      | 0x5e =>
        -- MCOPY: within memory, which must reach both ends
        if depth < 3 then lost stack world else
        let dst := peek stack sp 1
        let from_ := peek stack sp 2
        let len := peek stack sp 3
        let stop := max (rangeEnd dst len) (rangeEnd from_ len)
        if stop == unpayable then lost stack world else
        let cost := 3 + 3 * wordsOf len.w0 + expansionCost mem.size.toUInt64 stop
        if gas < cost then lost stack world else
        let mem := reach mem stop
        -- The bytes are taken out before they are put in: a copy from an array into itself would copy
        -- the whole array first.
        let moved := slice mem from_ len
        let mem := if len.isZero then mem else moved.copySlice 0 mem dst.w0.toNat len.w0.toNat
        run blk tx host f fuel stack (sp - 3) mem (pc + 1) (gas - cost) ret world
      | 0x5f =>
        if gas < 2 || depth ≥ stackLimit then lost stack world else
        run blk tx host f fuel (wr stack (sp <<< 5) Word.zero) (sp + 1) mem (pc + 1) (gas - 2) ret world
      | 0xa0 | 0xa1 | 0xa2 | 0xa3 | 0xa4 =>
        -- LOG0 to LOG4
        let topics := (op - 0xa0).toUSize
        if depth < 2 + topics || f.static then lost stack world else
        let off := peek stack sp 1
        let len := peek stack sp 2
        let stop := rangeEnd off len
        if stop == unpayable then lost stack world else
        let cost := 375 + 375 * topics.toUInt64 + 8 * len.w0 + expansionCost mem.size.toUInt64 stop
        if gas < cost then lost stack world else
        let mem := reach mem stop
        let world := world.log ⟨f.address, topicsOf stack sp topics, slice mem off len⟩
        run blk tx host f fuel stack (sp - 2 - topics) mem (pc + 1) (gas - cost) ret world
      | 0xf0 | 0xf1 | 0xf2 | 0xf4 | 0xf5 | 0xfa =>
        -- CREATE, CALL, CALLCODE, DELEGATECALL, CREATE2, STATICCALL: made ready outside the loop, the new
        -- call run here by the loop itself, and settled outside again.
        let p := prepare op host f stack sp mem gas world
        if !p.enter then
          if !p.ok then lost p.stack p.world else
          run blk tx host f fuel p.stack (sp - popped op) p.mem (pc + 1) p.gas p.ret p.world
        else
          let out := run blk tx host p.frame fuel (room p.stack p.frame.base) p.frame.base ByteArray.empty 0 p.childGas
            ByteArray.empty p.world
          let r := settle op p.answerAt p.retOff p.retLen p.mark p.target p.mem p.gas out
          run blk tx host f fuel r.stack (sp - popped op) r.mem (pc + 1) r.gas r.ret r.world
      | 0xf3 | 0xfd =>
        -- RETURN and REVERT
        if depth < 2 then lost stack world else
        let off := peek stack sp 1
        let len := peek stack sp 2
        let stop := rangeEnd off len
        if stop == unpayable then lost stack world else
        let cost := expansionCost mem.size.toUInt64 stop
        if gas < cost then lost stack world else
        ⟨if op == 0xf3 then 0 else 1, gas - cost, slice (reach mem stop) off len, stack, world⟩
      | 0xff =>
        -- SELFDESTRUCT
        if depth < 1 || f.static then lost stack world else
        let (world, gas, ok) := selfDestruct world f.address (peek stack sp 1).address gas
        if !ok then lost stack world else ⟨0, gas, ByteArray.empty, stack, world⟩
      | _ => lost stack world
    else ⟨0, gas, ByteArray.empty, stack, world⟩

/-- A call run from its beginning with `gas`. -/
def execute (blk : @& BlockEnv) (tx : @& TxEnv) (host : @& Host) (f : Frame) (stack : ByteArray) (gas : UInt64)
    (world : World) : Outcome :=
  run blk tx host f (gas.toNat + 1) (room stack f.base) f.base ByteArray.empty 0 gas ByteArray.empty world

end Fast
