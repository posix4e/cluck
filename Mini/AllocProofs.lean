import Mini.Run
import Mini.Alloc

/-! # What is proved about the allocator

Statements about the program in `Mini/Alloc.lean` as `Mini/Run.lean` defines its meaning: for every input,
not the ones a test tried. Nothing here runs; no image imports it. -/

namespace Mini.Alloc

/-- A block of a small class holds sixteen bytes for each step of the class, whatever the state, and asking
changes nothing. -/
theorem classBytes_small (outside : Outside) (fuel : Nat) (c : UInt64) (s : State) (h : c < 257) :
    program.call outside (fuel + 4) "class_bytes" [c] s = .ok (.gave (c * 16), s) := by
  simp [Program.call, program, classBytes, listGet, listSet, malloc, free, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, small, smallClasses, first, largeFirst, Expr.lt, Expr.shl, h]
  rfl

/-- The class a small request is given: enough sixteens to hold it. -/
def smallClass (size : UInt64) : UInt64 := (size + 15) / 16

/-- A small request's class is a small class, and its block holds the request with fewer than sixteen bytes
to spare. This is the arithmetic `rt_malloc` does for a request of 1 to 4096 bytes. -/
theorem smallClass_fits (size : UInt64) (low : 1 ≤ size) (high : size ≤ 4096) :
    smallClass size < 257 ∧ size ≤ smallClass size * 16 ∧ smallClass size * 16 < size + 16 := by
  have l : 1 ≤ size.toNat := by simpa [UInt64.le_iff_toNat_le] using low
  have h : size.toNat ≤ 4096 := by simpa [UInt64.le_iff_toNat_le] using high
  have n15 : (15 : UInt64).toNat = 15 := rfl
  have n16 : (16 : UInt64).toNat = 16 := rfl
  have n257 : (257 : UInt64).toNat = 257 := rfl
  have c : (smallClass size).toNat = (size.toNat + 15) / 16 := by
    simp only [smallClass, UInt64.toNat_div, UInt64.toNat_add, n15, n16]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [UInt64.lt_iff_toNat_lt, c, n257]; omega
  · simp only [UInt64.le_iff_toNat_le, UInt64.toNat_mul, c, n16]; omega
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, UInt64.toNat_add, c, n16]; omega

/-- So a small request is always given a block that holds it: the class `rt_malloc` picks is small, and
`class_bytes` of it, as the program computes it, is at least the size asked for. -/
theorem small_request_fits (outside : Outside) (fuel : Nat) (size : UInt64) (s : State)
    (low : 1 ≤ size) (high : size ≤ 4096) :
    ∃ bytes, program.call outside (fuel + 4) "class_bytes" [smallClass size] s = .ok (.gave bytes, s) ∧ size ≤ bytes :=
  ⟨smallClass size * 16, classBytes_small outside fuel _ s (smallClass_fits size low high).1,
    (smallClass_fits size low high).2.1⟩

end Mini.Alloc
