/-! A trial of how the fast engine holds its stack, on eight instructions. Two layouts are compared: the
stack as bytes (`runBytes`), 32 to a word, and the stack as 32-bit limbs (`runLimbs`), eight to a word, in
an array whose elements the runtime keeps unboxed. Each is one loop whose stack, stack pointer, program
counter and gas are arguments of their own, so that nothing is allocated per instruction. -/

namespace Fast.Spike

/-- How a run ended: 0 stopped, 1 out of gas, 2 stack, 3 bad jump, 4 bad instruction, 5 out of fuel. -/
structure Out where
  halt : UInt8
  gas : UInt64
  depth : USize

theorem within {n : Nat} {off : USize} (k : Nat) (h : off.toNat + k < n) : (off + USize.ofNat k).toNat < n := by
  have h1 : (off + USize.ofNat k).toNat ≤ off.toNat + (USize.ofNat k).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_le _ _
  have h2 : (USize.ofNat k).toNat ≤ k := by
    rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  omega

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) : (a.uset i v h).size = a.size := by
  cases a; simp [ByteArray.uset, ByteArray.size]

/-! ## The stack as bytes -/

/-- Eight bytes from `off`, least significant first. -/
@[inline] def load (a : ByteArray) (off : USize) (h : off.toNat + 7 < a.size) : UInt64 :=
  (a.uget off (by omega)).toUInt64 |||
  ((a.uget (off + 1) (within 1 (by omega))).toUInt64 <<< 8) |||
  ((a.uget (off + 2) (within 2 (by omega))).toUInt64 <<< 16) |||
  ((a.uget (off + 3) (within 3 (by omega))).toUInt64 <<< 24) |||
  ((a.uget (off + 4) (within 4 (by omega))).toUInt64 <<< 32) |||
  ((a.uget (off + 5) (within 5 (by omega))).toUInt64 <<< 40) |||
  ((a.uget (off + 6) (within 6 (by omega))).toUInt64 <<< 48) |||
  ((a.uget (off + 7) (within 7 (by omega))).toUInt64 <<< 56)

/-- One byte written, with the array's size carried along so that the next write needs no new check. -/
@[inline] def set1 {n : Nat} (a : {a : ByteArray // a.size = n}) (off : USize) (v : UInt8) (h : off.toNat < n) :
    {a : ByteArray // a.size = n} :=
  ⟨a.1.uset off v (by rw [a.2]; exact h), by rw [size_uset]; exact a.2⟩

/-- Eight bytes written at `off`, least significant first, when they fit; the array as it was when not. -/
@[inline] def store (a : ByteArray) (off : USize) (x : UInt64) : ByteArray :=
  if h : off.toNat + 7 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r off x.toUInt8 (by omega)
    let r := set1 r (off + USize.ofNat 1) (x >>> 8).toUInt8 (within 1 (by omega))
    let r := set1 r (off + USize.ofNat 2) (x >>> 16).toUInt8 (within 2 (by omega))
    let r := set1 r (off + USize.ofNat 3) (x >>> 24).toUInt8 (within 3 (by omega))
    let r := set1 r (off + USize.ofNat 4) (x >>> 32).toUInt8 (within 4 (by omega))
    let r := set1 r (off + USize.ofNat 5) (x >>> 40).toUInt8 (within 5 (by omega))
    let r := set1 r (off + USize.ofNat 6) (x >>> 48).toUInt8 (within 6 (by omega))
    (set1 r (off + USize.ofNat 7) (x >>> 56).toUInt8 (within 7 (by omega))).1
  else a

@[inline] def store4 (a : ByteArray) (off : USize) (w0 w1 w2 w3 : UInt64) : ByteArray :=
  store (store (store (store a off w0) (off + 8) w1) (off + 16) w2) (off + 24) w3

/-- The word at `off` as four limbs, least significant first, handed to what follows. -/
@[inline] def word {α : Type} (a : ByteArray) (off : USize) (h : off.toNat + 31 < a.size)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  k (load a off (by omega))
    (load a (off + USize.ofNat 8) (by have := within (n := a.size - 7) (off := off) 8 (by omega); omega))
    (load a (off + USize.ofNat 16) (by have := within (n := a.size - 7) (off := off) 16 (by omega); omega))
    (load a (off + USize.ofNat 24) (by have := within (n := a.size - 7) (off := off) 24 (by omega); omega))

/-- The carry out of `x + y + c`, for `c` 0 or 1. -/
@[inline] def carry (x y s : UInt64) : UInt64 := ((x &&& y) ||| ((x ||| y) &&& ~~~s)) >>> 63

def runBytes (code : ByteArray) : Nat → ByteArray → USize → USize → UInt64 → Out
  | 0, _, sp, _, gas => ⟨5, gas, sp⟩
  | fuel + 1, stack, sp, pc, gas =>
    if hpc : pc.toNat < code.size then
      let op := code.uget pc hpc
      match op with
      | 0x00 => ⟨0, gas, sp⟩
      | 0x01 =>   -- ADD
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 5
        let b := (sp - 2) <<< 5
        if h : a.toNat + 31 < stack.size ∧ b.toNat + 31 < stack.size then
          word stack a h.1 fun a0 a1 a2 a3 =>
          word stack b h.2 fun b0 b1 b2 b3 =>
          let s0 := a0 + b0
          let c0 := carry a0 b0 s0
          let s1 := a1 + b1 + c0
          let c1 := carry a1 b1 s1
          let s2 := a2 + b2 + c1
          let c2 := carry a2 b2 s2
          let s3 := a3 + b3 + c2
          runBytes code fuel (store4 stack b s0 s1 s2 s3) (sp - 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | 0x11 =>   -- GT: the top greater than the one under it
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 5
        let b := (sp - 2) <<< 5
        if h : a.toNat + 31 < stack.size ∧ b.toNat + 31 < stack.size then
          word stack a h.1 fun a0 a1 a2 a3 =>
          word stack b h.2 fun b0 b1 b2 b3 =>
          let gt : Bool :=
            if a3 != b3 then a3 > b3 else if a2 != b2 then a2 > b2 else if a1 != b1 then a1 > b1 else a0 > b0
          runBytes code fuel (store4 stack b (if gt then 1 else 0) 0 0 0) (sp - 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | 0x57 =>   -- JUMPI: to the top if the one under it is not zero
        if gas < 10 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 5
        let b := (sp - 2) <<< 5
        if h : a.toNat + 31 < stack.size ∧ b.toNat + 31 < stack.size then
          word stack a h.1 fun a0 a1 a2 a3 =>
          word stack b h.2 fun b0 b1 b2 b3 =>
          if (b0 ||| b1 ||| b2 ||| b3) == 0 then runBytes code fuel stack (sp - 2) (pc + 1) (gas - 10)
          else
            let dest := a0.toUSize
            if (a1 ||| a2 ||| a3) != 0 || a0 ≥ 0x100000000 then ⟨3, gas, sp⟩ else
            if hd : dest.toNat < code.size then
              if code.uget dest hd == 0x5b then runBytes code fuel stack (sp - 2) dest (gas - 10) else ⟨3, gas, sp⟩
            else ⟨3, gas, sp⟩
        else ⟨2, gas, sp⟩
      | 0x5b => if gas < 1 then ⟨1, gas, sp⟩ else runBytes code fuel stack sp (pc + 1) (gas - 1)
      | 0x60 =>   -- PUSH1
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let v : UInt64 := if h : (pc + 1).toNat < code.size then (code.uget (pc + 1) h).toUInt64 else 0
        runBytes code fuel (store4 stack (sp <<< 5) v 0 0 0) (sp + 1) (pc + 2) (gas - 3)
      | 0x62 =>   -- PUSH3
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let x : UInt64 := if h : (pc + 1).toNat < code.size then (code.uget (pc + 1) h).toUInt64 else 0
        let y : UInt64 := if h : (pc + 2).toNat < code.size then (code.uget (pc + 2) h).toUInt64 else 0
        let z : UInt64 := if h : (pc + 3).toNat < code.size then (code.uget (pc + 3) h).toUInt64 else 0
        runBytes code fuel (store4 stack (sp <<< 5) ((x <<< 16) ||| (y <<< 8) ||| z) 0 0 0) (sp + 1) (pc + 4) (gas - 3)
      | 0x80 =>   -- DUP1
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 1 || sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 5
        if h : a.toNat + 31 < stack.size then
          word stack a h fun a0 a1 a2 a3 =>
          runBytes code fuel (store4 stack (sp <<< 5) a0 a1 a2 a3) (sp + 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | _ => ⟨4, gas, sp⟩
    else ⟨0, gas, sp⟩

def bytesRun (code : ByteArray) (gas : UInt64) : Out :=
  runBytes code (gas.toNat + 1) (ByteArray.mk (Array.replicate (1024 * 32) 0)) 0 0 gas

/-! ## The stack as 32-bit limbs -/

abbrev Limbs := Array UInt32

@[inline] def lset {n : Nat} (a : {a : Limbs // a.size = n}) (i : USize) (v : UInt32) (h : i.toNat < n) :
    {a : Limbs // a.size = n} :=
  ⟨a.1.uset i v (by rw [a.2]; exact h), by rw [Array.size_uset]; exact a.2⟩

/-- A word written as eight limbs from `i`, when they fit. -/
@[inline] def lstore4 (a : Limbs) (i : USize) (w0 w1 w2 w3 : UInt64) : Limbs :=
  if h : i.toNat + 7 < a.size then
    let r : {b : Limbs // b.size = a.size} := ⟨a, rfl⟩
    let r := lset r i w0.toUInt32 (by omega)
    let r := lset r (i + USize.ofNat 1) (w0 >>> 32).toUInt32 (within 1 (by omega))
    let r := lset r (i + USize.ofNat 2) w1.toUInt32 (within 2 (by omega))
    let r := lset r (i + USize.ofNat 3) (w1 >>> 32).toUInt32 (within 3 (by omega))
    let r := lset r (i + USize.ofNat 4) w2.toUInt32 (within 4 (by omega))
    let r := lset r (i + USize.ofNat 5) (w2 >>> 32).toUInt32 (within 5 (by omega))
    let r := lset r (i + USize.ofNat 6) w3.toUInt32 (within 6 (by omega))
    (lset r (i + USize.ofNat 7) (w3 >>> 32).toUInt32 (within 7 (by omega))).1
  else a

@[inline] def lpair (a : Limbs) (i : USize) (k : Nat) (h : i.toNat + k + 1 < a.size) : UInt64 :=
  (a.uget (i + USize.ofNat k) (within k (by omega))).toUInt64 |||
  ((a.uget (i + USize.ofNat (k + 1)) (within (k + 1) (by omega))).toUInt64 <<< 32)

@[inline] def lword {α : Type} (a : Limbs) (i : USize) (h : i.toNat + 7 < a.size)
    (k : UInt64 → UInt64 → UInt64 → UInt64 → α) : α :=
  k (lpair a i 0 (by omega)) (lpair a i 2 (by omega)) (lpair a i 4 (by omega)) (lpair a i 6 (by omega))

def runLimbs (code : ByteArray) : Nat → Limbs → USize → USize → UInt64 → Out
  | 0, _, sp, _, gas => ⟨5, gas, sp⟩
  | fuel + 1, stack, sp, pc, gas =>
    if hpc : pc.toNat < code.size then
      let op := code.uget pc hpc
      match op with
      | 0x00 => ⟨0, gas, sp⟩
      | 0x01 =>
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 3
        let b := (sp - 2) <<< 3
        if h : a.toNat + 7 < stack.size ∧ b.toNat + 7 < stack.size then
          lword stack a h.1 fun a0 a1 a2 a3 =>
          lword stack b h.2 fun b0 b1 b2 b3 =>
          let s0 := a0 + b0
          let c0 := carry a0 b0 s0
          let s1 := a1 + b1 + c0
          let c1 := carry a1 b1 s1
          let s2 := a2 + b2 + c1
          let c2 := carry a2 b2 s2
          let s3 := a3 + b3 + c2
          runLimbs code fuel (lstore4 stack b s0 s1 s2 s3) (sp - 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | 0x11 =>
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 3
        let b := (sp - 2) <<< 3
        if h : a.toNat + 7 < stack.size ∧ b.toNat + 7 < stack.size then
          lword stack a h.1 fun a0 a1 a2 a3 =>
          lword stack b h.2 fun b0 b1 b2 b3 =>
          let gt : Bool :=
            if a3 != b3 then a3 > b3 else if a2 != b2 then a2 > b2 else if a1 != b1 then a1 > b1 else a0 > b0
          runLimbs code fuel (lstore4 stack b (if gt then 1 else 0) 0 0 0) (sp - 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | 0x57 =>
        if gas < 10 then ⟨1, gas, sp⟩ else
        if sp < 2 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 3
        let b := (sp - 2) <<< 3
        if h : a.toNat + 7 < stack.size ∧ b.toNat + 7 < stack.size then
          lword stack a h.1 fun a0 a1 a2 a3 =>
          lword stack b h.2 fun b0 b1 b2 b3 =>
          if (b0 ||| b1 ||| b2 ||| b3) == 0 then runLimbs code fuel stack (sp - 2) (pc + 1) (gas - 10)
          else
            let dest := a0.toUSize
            if (a1 ||| a2 ||| a3) != 0 || a0 ≥ 0x100000000 then ⟨3, gas, sp⟩ else
            if hd : dest.toNat < code.size then
              if code.uget dest hd == 0x5b then runLimbs code fuel stack (sp - 2) dest (gas - 10) else ⟨3, gas, sp⟩
            else ⟨3, gas, sp⟩
        else ⟨2, gas, sp⟩
      | 0x5b => if gas < 1 then ⟨1, gas, sp⟩ else runLimbs code fuel stack sp (pc + 1) (gas - 1)
      | 0x60 =>
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let v : UInt64 := if h : (pc + 1).toNat < code.size then (code.uget (pc + 1) h).toUInt64 else 0
        runLimbs code fuel (lstore4 stack (sp <<< 3) v 0 0 0) (sp + 1) (pc + 2) (gas - 3)
      | 0x62 =>
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let x : UInt64 := if h : (pc + 1).toNat < code.size then (code.uget (pc + 1) h).toUInt64 else 0
        let y : UInt64 := if h : (pc + 2).toNat < code.size then (code.uget (pc + 2) h).toUInt64 else 0
        let z : UInt64 := if h : (pc + 3).toNat < code.size then (code.uget (pc + 3) h).toUInt64 else 0
        runLimbs code fuel (lstore4 stack (sp <<< 3) ((x <<< 16) ||| (y <<< 8) ||| z) 0 0 0) (sp + 1) (pc + 4) (gas - 3)
      | 0x80 =>
        if gas < 3 then ⟨1, gas, sp⟩ else
        if sp < 1 || sp ≥ 1024 then ⟨2, gas, sp⟩ else
        let a := (sp - 1) <<< 3
        if h : a.toNat + 7 < stack.size then
          lword stack a h fun a0 a1 a2 a3 =>
          runLimbs code fuel (lstore4 stack (sp <<< 3) a0 a1 a2 a3) (sp + 1) (pc + 1) (gas - 3)
        else ⟨2, gas, sp⟩
      | _ => ⟨4, gas, sp⟩
    else ⟨0, gas, sp⟩

def limbsRun (code : ByteArray) (gas : UInt64) : Out :=
  runLimbs code (gas.toNat + 1) (Array.replicate (1024 * 8) 0) 0 0 gas

end Fast.Spike
