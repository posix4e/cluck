import Mini.Run
import Mini.Memory
import Mini.Number
import Mini.AllocProofs
import Runtime.BigProofs

/-! # What is proved about numbers in memory

Statements about the program in `Mini/Number.lean` as `Mini/Run.lean` defines its meaning. The arithmetic
itself is `Runtime/Big.lean`, proved in `Runtime/BigProofs.lean` to return the limbs of the right number;
this is about the two ends of a call: that the limbs handed to it are those of the number that came in, and
that what goes back to compiled Lean is the number in the limbs it returned. Nothing here runs; no image
imports it.

What the program calls outside itself is an assumption in each statement: here, that `lean_alloc_object`
returns some address, and that `lean_dec` returns. Nothing is assumed of the memory there.

Proved so far for numbers that fit in a tagged word, natural numbers and integers both. -/

namespace Mini.Number

theorem find_arrayNew : program.functions.find? (fun f => f.name == "array_new") = some arrayNew := rfl
theorem find_limbsOfWord : program.functions.find? (fun f => f.name == "limbs_of_word") = some limbsOfWord := rfl

/-- The header of an array with one reference. -/
def arrayHeader : UInt64 := UInt64.ofNat (1 + arrayKind * 2 ^ 56)

/-- `array_new` asks for room for the header, the size, the capacity and the elements, and writes the first
three. -/
theorem arrayNew_runs (outside : Outside) (fuel : Nat) (count array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [24 + count * 8] s = .ok (array, s')) :
    program.call outside (fuel + 10) "array_new" [count] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (writeBytes (writeBytes s'.memory array arrayHeader 8) (array + 8) count 8)
            (array + 16) count 8 }) := by
  simp [Program.call, find_arrayNew, arrayNew, runAll, Stmt.run, Expr.run, Op.run, bind, put, header, alloc]
  rfl

/-- Memory with the first three words of an array written: its header, its size and its capacity. -/
def headed (memory : UInt64 → Option UInt8) (array count : UInt64) : UInt64 → Option UInt8 :=
  writeBytes (writeBytes (writeBytes memory array arrayHeader 8) (array + 8) count 8) (array + 16) count 8

/-- A limb as an element of a Lean array: a tagged word. -/
def boxed (limb : UInt64) : UInt64 := (limb <<< 1) ||| 1

theorem limbsOfWord_zero (outside : Outside) (fuel : Nat) (array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [24] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [0] s =
      .ok (.gave array, { s' with memory := headed s'.memory array 0 }) := by
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc]
  rfl

theorem limbsOfWord_one (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (hz : value ≠ 0) (hs : value ≤ 4294967295)
    (alloc : outside "lean_alloc_object" [32] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [value] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (headed s'.memory array 1) (array + 24) (boxed (value &&& 4294967295)) 8 }) := by
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc, hz, hs]
  rfl

theorem limbsOfWord_two (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (hl : (4294967295 : UInt64) < value)
    (alloc : outside "lean_alloc_object" [40] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [value] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (writeBytes (headed s'.memory array 2) (array + 24) (boxed (value &&& 4294967295)) 8)
            (array + 32) (boxed (value >>> 32)) 8 }) := by
  have hz : value ≠ 0 := by intro h; subst h; exact absurd hl (by decide)
  have hn : ¬ value ≤ 4294967295 := by simpa [UInt64.not_le] using hl
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc, hz, hn]
  rfl

/-! ## Words apart -/

/-- A word written eight bytes or more from another, either way round, leaves the other as it was. -/
theorem read_apart (memory : UInt64 → Option UInt8) (p q word : UInt64)
    (low : 8 ≤ (q - p).toNat) (high : (q - p).toNat ≤ 18446744073709551608) :
    readBytes (writeBytes memory p word 8) q 8 = readBytes memory q 8 := by
  have back : p + (q - p) = q := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_sub]
    have := p.toNat_lt
    have := q.toNat_lt
    omega
  exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => by
    have := words_apart p (q - p) low high i hi k hk
    rwa [back] at this)

/-- The same for two places counted from one address. -/
theorem read_off (memory : UInt64 → Option UInt8) (a word : UInt64) (x y : Nat)
    (hx : x < 9223372036854775808) (hy : y < 9223372036854775808) (apart : x + 8 ≤ y ∨ y + 8 ≤ x) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word 8) (a + UInt64.ofNat y) 8
      = readBytes memory (a + UInt64.ofNat y) 8 := by
  have d : (a + UInt64.ofNat y - (a + UInt64.ofNat x)).toNat
      = (y + 18446744073709551616 - x) % 18446744073709551616 := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

/-- A write inside the first `n` bytes from an address leaves everything outside them as it was. -/
theorem write_inside (memory : UInt64 → Option UInt8) (a word p : UInt64) (off n : Nat) (h : off + 8 ≤ n)
    (outside : ∀ k, k < n → a + UInt64.ofNat k ≠ p) :
    writeBytes memory (a + UInt64.ofNat off) word 8 p = memory p := by
  refine writeBytes_other _ _ _ _ _ (fun k hk => ?_)
  have := outside (off + k) (by omega)
  rwa [UInt64.ofNat_add, ← UInt64.add_assoc] at this

/-! ## An array of limbs in memory -/

/-- A Lean array of limbs at an address, as much of it as this program makes and reads: its header, its
size, and each limb as a tagged word. -/
def ArrayOf (memory : UInt64 → Option UInt8) (array : UInt64) (limbs : Runtime.Big.Limbs) : Prop :=
  readBytes memory array 8 = .ok arrayHeader ∧
  readBytes memory (array + 8) 8 = .ok (UInt64.ofNat limbs.size) ∧
  ∀ i, (h : i < limbs.size) →
    readBytes memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64)

/-- The limbs of a number that fits in a word: none for zero, one below 2^32, otherwise two. -/
def wordLimbs (value : UInt64) : Runtime.Big.Limbs :=
  if value = 0 then #[] else if value ≤ 4294967295 then #[value.toUInt32]
  else #[value.toUInt32, (value >>> 32).toUInt32]

/-- They are the limbs of that number. -/
theorem wordLimbs_value (value : UInt64) : Runtime.Big.value (wordLimbs value) = value.toNat := by
  have lt := value.toNat_lt
  unfold wordLimbs
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h1 h2
      have small : value.toNat ≤ 4294967295 := by simpa [UInt64.le_iff_toNat_le] using h2
      simp [Runtime.Big.value, Runtime.Big.valueList]
      omega
    · rename_i h1 h2
      simp [Runtime.Big.value, Runtime.Big.valueList, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      omega

/-- And they have no zero limb on top, which is how the arithmetic expects a number. -/
theorem wordLimbs_trimmed (value : UInt64) : Runtime.Big.Trimmed (wordLimbs value) := by
  have lt := value.toNat_lt
  unfold wordLimbs
  split
  · exact Or.inl rfl
  · split
    · rename_i h1 h2
      have nz : value.toNat ≠ 0 := fun z => h1 (UInt64.toNat_inj.mp (by rw [z]; rfl))
      have small : value.toNat ≤ 4294967295 := by simpa [UInt64.le_iff_toNat_le] using h2
      refine Or.inr ?_
      simp [Runtime.Big.digit]
      omega
    · rename_i h1 h2
      have large : 4294967295 < value.toNat := by simpa [UInt64.le_iff_toNat_le] using h2
      refine Or.inr ?_
      simp [Runtime.Big.digit, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      omega

/-! ## What `limbs_of_word` leaves in memory -/

theorem read_base (memory : UInt64 → Option UInt8) (a word : UInt64) (x : Nat)
    (hx : 8 ≤ x) (hx' : x < 9223372036854775808) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word 8) a 8 = readBytes memory a 8 := by
  have d : (a - (a + UInt64.ofNat x)).toNat = 18446744073709551616 - x := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

theorem read_from_base (memory : UInt64 → Option UInt8) (a word : UInt64) (y : Nat)
    (hy : 8 ≤ y) (hy' : y < 9223372036854775808) :
    readBytes (writeBytes memory a word 8) (a + UInt64.ofNat y) 8 = readBytes memory (a + UInt64.ofNat y) 8 := by
  have d : (a + UInt64.ofNat y - a).toNat = y := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

theorem headed_header (memory : UInt64 → Option UInt8) (a count : UInt64) :
    readBytes (headed memory a count) a 8 = .ok arrayHeader := by
  exact (read_base _ a _ 16 (by omega) (by omega)).trans
    ((read_base _ a _ 8 (by omega) (by omega)).trans (readBytes_writeBytes_word _ _ _))

theorem headed_size (memory : UInt64 → Option UInt8) (a count : UInt64) :
    readBytes (headed memory a count) (a + 8) 8 = .ok count := by
  exact (read_off _ a _ 16 8 (by omega) (by omega) (by omega)).trans (readBytes_writeBytes_word _ _ _)

/-- The header, size and capacity are the first 24 bytes: writing them leaves the elements as they were. -/
theorem headed_element (memory : UInt64 → Option UInt8) (a count : UInt64) (y : Nat)
    (hy : 24 ≤ y) (hy' : y < 9223372036854775808) :
    readBytes (headed memory a count) (a + UInt64.ofNat y) 8 = readBytes memory (a + UInt64.ofNat y) 8 := by
  exact (read_off _ a _ 16 y (by omega) hy' (by omega)).trans
    ((read_off _ a _ 8 y (by omega) hy' (by omega)).trans (read_from_base _ a _ y (by omega) hy'))

theorem headed_outside (memory : UInt64 → Option UInt8) (a count p : UInt64) (n : Nat) (hn : 24 ≤ n)
    (outside : ∀ k, k < n → a + UInt64.ofNat k ≠ p) : headed memory a count p = memory p := by
  have first : writeBytes memory a arrayHeader 8 p = memory p := by
    simpa using write_inside memory a arrayHeader p 0 n (by omega) outside
  exact (write_inside _ a _ p 16 n (by omega) outside).trans
    ((write_inside _ a _ p 8 n (by omega) outside).trans first)

theorem low_limb (value : UInt64) : value &&& 4294967295 = value.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem high_limb (value : UInt64) : value >>> 32 = (value >>> 32).toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := value.toNat_lt
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- `limbs_of_word` hands the arithmetic the right limbs: given room for them, it leaves in memory an array
holding the limbs of the word (`wordLimbs`, whose number is the word and which has no zero limb on top),
does nothing C leaves open, and changes nothing outside the room it was given. -/
theorem limbsOfWord_array (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs value).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 20) "limbs_of_word" [value] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs value)
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs value).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  by_cases hz : value = 0
  · subst hz
    have w : wordLimbs 0 = #[] := rfl
    rw [w] at alloc ⊢
    exact ⟨_, limbsOfWord_zero outside fuel array s s' alloc,
      ⟨headed_header _ _ _, headed_size _ _ _, fun i h => absurd h (by simp)⟩,
      fun p out => headed_outside _ _ _ _ 24 (by omega) out⟩
  · by_cases hs : value ≤ 4294967295
    · have w : wordLimbs value = #[value.toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc ⊢
      refine ⟨_, limbsOfWord_one outside fuel value array s s' hz hs alloc, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (read_base _ array _ 24 (by omega) (by omega)).trans (headed_header _ _ _)
      · exact (read_off _ array _ 24 8 (by omega) (by omega) (by omega)).trans (headed_size _ _ _)
      · intro i h
        have i0 : i = 0 := by simp at h; omega
        subst i0
        show readBytes _ (array + 24) 8 = _
        rw [readBytes_writeBytes_word, low_limb]
        rfl
      · intro p out
        exact (write_inside _ array _ p 24 32 (by omega) out).trans (headed_outside _ _ _ _ 32 (by omega) out)
    · have hl : (4294967295 : UInt64) < value := by simpa [UInt64.not_le] using hs
      have w : wordLimbs value = #[value.toUInt32, (value >>> 32).toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc ⊢
      refine ⟨_, limbsOfWord_two outside fuel value array s s' hl alloc, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (read_base _ array _ 32 (by omega) (by omega)).trans
          ((read_base _ array _ 24 (by omega) (by omega)).trans (headed_header _ _ _))
      · exact (read_off _ array _ 32 8 (by omega) (by omega) (by omega)).trans
          ((read_off _ array _ 24 8 (by omega) (by omega) (by omega)).trans (headed_size _ _ _))
      · intro i h
        have i01 : i = 0 ∨ i = 1 := by simp at h; omega
        rcases i01 with rfl | rfl
        · show readBytes _ (array + 24) 8 = _
          refine (read_off _ array _ 32 24 (by omega) (by omega) (by omega)).trans ?_
          refine (readBytes_writeBytes_word _ _ _).trans ?_
          rw [low_limb]
          rfl
        · show readBytes _ (array + 32) 8 = _
          exact (readBytes_writeBytes_word _ _ _).trans
            (congrArg (fun x => Except.ok (boxed x)) (high_limb value))
      · intro p out
        exact (write_inside _ array _ p 32 40 (by omega) out).trans
          ((write_inside _ array _ p 24 40 (by omega) out).trans (headed_outside _ _ _ _ 40 (by omega) out))

/-! ## A natural number that arrives as a tagged word -/

theorem find_natLimbs : program.functions.find? (fun f => f.name == "nat_limbs") = some natLimbs := rfl

/-- What calling a function by name says about running its body. -/
theorem runAll_of_call (p : Program) (outside : Outside) (fuel : Nat) (function : String) (f : Function)
    (arguments : List UInt64) (s after : State) (ending : Ending)
    (found : p.functions.find? (fun f => f.name == function) = some f)
    (call : p.call outside fuel function arguments s = .ok (ending, after)) :
    ∃ locals, runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments)
      = .ok (ending, after, locals) := by
  unfold Program.call at call
  rw [found] at call
  dsimp only at call
  cases run : runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments) with
  | error e =>
    rw [run] at call
    cases call
  | ok r =>
    obtain ⟨e, st, l⟩ := r
    rw [run] at call
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at call
    injection call with same
    injection same with e1 e2
    exact ⟨l, by rw [e1, e2]⟩

/-- A natural number below 2^63 arrives as a tagged word: the number moved up one bit, with the lowest bit
set. `nat_limbs` hands the arithmetic the limbs of that number. -/
theorem natLimbs_word (outside : Outside) (fuel : Nat) (o array : UInt64) (s s' : State) (tagged : o &&& 1 ≠ 0)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (o >>> 1)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 24) "nat_limbs" [o] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (o >>> 1))
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (o >>> 1)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  obtain ⟨memory, run, holds, frame⟩ := limbsOfWord_array outside fuel (o >>> 1) array s s' alloc
  obtain ⟨l, hl⟩ := runAll_of_call program outside (fuel + 20) "limbs_of_word" limbsOfWord [o >>> 1] s _ _
    find_limbsOfWord run
  refine ⟨memory, ?_, holds, frame⟩
  simp [Program.call, find_natLimbs, find_limbsOfWord, natLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
    isWord, unbox, Expr.ne, Expr.and, Expr.shr, tagged, hl]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]

/-! ## Reading an answer: the zero limbs on top -/

theorem find_trimmed : program.functions.find? (fun f => f.name == "trimmed") = some trimmed := rfl

/-- How many of the first `n` limbs are left when the zero ones on top are dropped: what `trimmed` counts. -/
def trimCount (limbs : Runtime.Big.Limbs) : Nat → Nat
  | 0 => 0
  | n + 1 => if limbs.getD n 0 = 0 then trimCount limbs n else n + 1

theorem trimCount_le (limbs : Runtime.Big.Limbs) (n : Nat) : trimCount limbs n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => unfold trimCount; split <;> omega

/-- A tagged word with its tag taken off is the limb it held. -/
theorem unbox_boxed (limb : UInt32) : boxed limb.toUInt64 >>> 1 = limb.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have lt := limb.toNat_lt
  have e : (limb.toNat <<< 1 ||| 1) = limb.toNat <<< 1 + 1 :=
    (Nat.shiftLeft_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) limb.toNat).symm
  simp only [boxed, UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show (1 : UInt64).toNat = 1 from rfl, show 1 % 64 = 1 from rfl]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), e, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The loop in `trimmed`, under a name of its own. -/
def trimLoop (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :=
  Stmt.run p outside fuel (.loop (Expr.lt 0 "count")
    [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)]) s locals

/-- The address of the limb below a count that is not zero. -/
theorem below_count (array : UInt64) (n : Nat) :
    array + 24 + (UInt64.ofNat (n + 1) - 1) * 8 = array + UInt64.ofNat (24 + 8 * n) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
    show (24 : UInt64).toNat = 24 from rfl, show (8 : UInt64).toNat = 8 from rfl,
    show (1 : UInt64).toNat = 1 from rfl]
  omega

/-- The loop, from any count: it reads only limbs below the count, changes nothing, and stops at the first
limb from the top that is not zero, giving the count there; or runs out of limbs and goes on with a count
of zero. -/
theorem trim_loop (p : Program) (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64)) :
    ∀ (n : Nat) (locals : Locals) (extra : Nat), n ≤ limbs.size →
      locals "count" = some (UInt64.ofNat n) → locals "array" = some array →
      ∃ after, trimLoop p outside (n + extra + 6) s locals =
          .ok (if trimCount limbs n = 0 then .on else .gave (UInt64.ofNat (trimCount limbs n)), s, after) ∧
        after "count" = some (UInt64.ofNat (trimCount limbs n)) := by
  intro n
  induction n with
  | zero =>
    intro locals extra _ hcount harray
    refine ⟨locals, ?_, by simpa [trimCount] using hcount⟩
    simp [trimLoop, Stmt.run, Expr.run, Op.run, Expr.lt, hcount, trimCount]
    rfl
  | succ n ih =>
    intro locals extra hn hcount harray
    have read := elements n (by omega)
    rw [← below_count] at read
    have value : limbs.getD n 0 = limbs[n]'(by omega) := by simp [Array.getD, show n < limbs.size by omega]
    generalize hc : UInt64.ofNat (n + 1) = c at hcount read
    have cpos : c ≠ 0 := by
      intro z
      have := congrArg UInt64.toNat (hc.trans z)
      simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
      omega
    have cless : c - 1 = UInt64.ofNat n := by
      rw [← hc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
      omega
    unfold trimLoop
    rw [show n + 1 + extra + 6 = (n + extra + 6) + 1 from by omega, Mini.Alloc.loop_turn]
    by_cases top : limbs[n]'(by omega) = 0
    · have hz : (limbs[n]'(by omega)).toUInt64 = 0 := by rw [top]; rfl
      obtain ⟨after, hrun, hafter⟩ := ih (put locals "count" (some (c - 1))) extra (by omega)
        (by simp [put, cless]) (by simp [put, harray])
      refine ⟨after, ?_, ?_⟩
      · unfold trimLoop at hrun
        generalize hround : Stmt.run p outside (n + extra + 6) (.loop (Expr.lt 0 "count")
          [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)])
          = round at hrun ⊢
        simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.ne, Expr.shr, limbAt, unbox, hcount, harray, read,
          hz, cpos]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, hcount, hrun, trimCount,
          value, top, show boxed 0 >>> 1 = 0 from by decide]
      · simpa [trimCount, value, top] using hafter
    · have nz : (limbs[n]'(by omega)).toUInt64 ≠ 0 := fun h => top (UInt32.toNat_inj.mp (by
        have := congrArg UInt64.toNat h
        simpa using this))
      refine ⟨locals, ?_, by simpa [trimCount, value, top, hc] using hcount⟩
      generalize hround : Stmt.run p outside (n + extra + 6) (.loop (Expr.lt 0 "count")
        [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)])
        = round
      simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.ne, Expr.shr, limbAt, unbox, hcount, harray, read,
        cpos]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, trimCount, value, top, hc, unbox_boxed, nz]

/-- `trimmed` gives the count without the zero limbs on top, and changes nothing. -/
theorem trimmed_runs (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64))
    (n extra : Nat) (hn : n ≤ limbs.size) :
    program.call outside (n + extra + 8) "trimmed" [array, UInt64.ofNat n] s
      = .ok (.gave (UInt64.ofNat (trimCount limbs n)), s) := by
  obtain ⟨after, hrun, hafter⟩ := trim_loop program outside array limbs s small elements n
    (bind (fun _ => none) ["array", "count"] [array, UInt64.ofNat n]) (extra + 1) hn
    (by simp [bind, put]) (by simp [bind, put])
  have step : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n])
      = (do
          match ← trimLoop program outside (n + (extra + 1) + 6) s
              (bind (fun _ => none) ["array", "count"] [array, UInt64.ofNat n]) with
          | (.on, s, locals) => runAll program outside (n + (extra + 1) + 6) [.give "count"] s locals
          | ended => pure ended) := by
    rw [show n + extra + 8 = (n + (extra + 1) + 6) + 1 from by omega]
    rfl
  unfold Program.call
  rw [find_trimmed]
  dsimp only
  rw [step, hrun]
  by_cases z : trimCount limbs n = 0
  · rw [z] at hafter
    simp [z, runAll, Stmt.run, Expr.run, hafter, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [z, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The number in the limbs is the number in those `trimmed` keeps. -/
theorem value_trimCount (limbs : Runtime.Big.Limbs) (n : Nat) (h : Runtime.Big.tail limbs n = 0) :
    Runtime.Big.value limbs = Runtime.Big.lower limbs (trimCount limbs n) := by
  induction n with
  | zero => rw [Runtime.Big.tail_zero] at h; rw [h]; rfl
  | succ n ih =>
    unfold trimCount
    split
    · rename_i z
      have step := Runtime.Big.tail_step limbs n
      have d : Runtime.Big.digit limbs n = 0 := by simp [Runtime.Big.digit, z]
      rw [h, d, Nat.zero_add] at step
      exact ih (step.trans (Nat.mul_zero _))
    · have split := Runtime.Big.value_split limbs (n + 1)
      rw [h, Nat.mul_zero, Nat.add_zero] at split
      exact split

/-- And the top one of those is not zero. -/
theorem trimCount_top (limbs : Runtime.Big.Limbs) (n m : Nat) (h : trimCount limbs n = m + 1) :
    Runtime.Big.digit limbs m ≠ 0 := by
  induction n with
  | zero => simp [trimCount] at h
  | succ n ih =>
    unfold trimCount at h
    split at h
    · exact ih h
    · rename_i nz
      have e : m = n := by omega
      subst e
      intro z
      exact nz (UInt32.toNat_inj.mp (show (limbs.getD m 0).toNat = (0 : UInt32).toNat from z))

/-! ## Reading an answer that fits in a tagged word -/

theorem find_natResult : program.functions.find? (fun f => f.name == "nat_result") = some natResult := rfl

/-- A number below 2^63 as a tagged word: twice the number, and one. -/
theorem boxed_small (x : UInt64) (h : x.toNat < 9223372036854775808) :
    boxed x = UInt64.ofNat (2 * x.toNat + 1) := by
  apply UInt64.toNat_inj.mp
  have e : (x.toNat <<< 1 ||| 1) = x.toNat <<< 1 + 1 :=
    (Nat.shiftLeft_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) x.toNat).symm
  simp only [boxed, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    show (1 : UInt64).toNat = 1 from rfl, show 1 % 64 = 1 from rfl]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), e, Nat.shiftLeft_eq]
  omega

/-- `nat_result` reads an answer rightly where the answer is below 2^63: from an array of limbs in memory
it gives back the tagged word for the number those limbs are, and changes nothing. The limbs may have zero
limbs on top, as the arithmetic can leave them. -/
theorem natResult_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State) (extra : Nat)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs)
    (fits : Runtime.Big.value limbs < 9223372036854775808) :
    program.call outside (limbs.size + extra + 10) "nat_result" [array, UInt64.ofNat limbs.size] s
      = .ok (.gave (UInt64.ofNat (2 * Runtime.Big.value limbs + 1)), s) := by
  have elements := holds.2.2
  have run := trimmed_runs outside array limbs s small elements limbs.size extra (Nat.le_refl _)
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := value_trimCount limbs limbs.size (Runtime.Big.tail_of_le limbs _ (Nat.le_refl _))
  have hle := trimCount_le limbs limbs.size
  generalize hc : trimCount limbs limbs.size = c at hl hv hle
  rcases c with _ | _ | _ | c
  · have v0 : Runtime.Big.value limbs = 0 := hv
    have hl0 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 0, s, l) := hl
    rw [v0]
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl0, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]
  · have size1 : 0 < limbs.size := by omega
    have hl1 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 1, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 size1
    have v1 : Runtime.Big.value limbs = limbs[0].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size1]
    have fin : boxed limbs[0].toUInt64 = UInt64.ofNat (2 * Runtime.Big.value limbs + 1) := by
      rw [v1]
      have lt := limbs[0].toNat_lt
      have := boxed_small limbs[0].toUInt64 (by simp; omega)
      simpa using this
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl1, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, r0, unbox_boxed]
    simpa [boxed] using fin
  · have size2 : 1 < limbs.size := by omega
    have hl2 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 2, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 (by omega)
    have r1 : readBytes s.memory (array + 24 + 8) 8 = .ok (boxed limbs[1].toUInt64) := by
      rw [UInt64.add_assoc]; exact elements 1 size2
    have v2 : Runtime.Big.value limbs = limbs[0].toNat + 4294967296 * limbs[1].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size2, show 0 < limbs.size by omega]
    have l0 := limbs[0].toNat_lt
    have l1 := limbs[1].toNat_lt
    have h1 : limbs[1].toUInt64 < 2147483648 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have both : ((limbs[1].toUInt64 <<< 32) ||| limbs[0].toUInt64).toNat = Runtime.Big.value limbs := by
      rw [Runtime.Big.two_limbs_word _ _ (by simp; omega) (by simp; omega), v2]; simp; omega
    have fin : boxed ((limbs[1].toUInt64 <<< 32) ||| limbs[0].toUInt64)
        = UInt64.ofNat (2 * Runtime.Big.value limbs + 1) := by
      rw [← both]; exact boxed_small _ (by rw [both]; exact fits)
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl2, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, Expr.and, Expr.lt, top, r0, r1, unbox_boxed, h1]
    simpa [boxed] using fin
  · exfalso
    have topd := trimCount_top limbs limbs.size (c + 2) hc
    have big : 4294967296 ^ 2 ≤ 4294967296 ^ (c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have one : 4294967296 ^ (c + 2) * 1 ≤ 4294967296 ^ (c + 2) * Runtime.Big.digit limbs (c + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have lower : Runtime.Big.lower limbs (c + 2 + 1)
        = Runtime.Big.lower limbs (c + 2) + 4294967296 ^ (c + 2) * Runtime.Big.digit limbs (c + 2) := rfl
    have hv' : Runtime.Big.value limbs = Runtime.Big.lower limbs (c + 2 + 1) := hv
    rw [Nat.mul_one] at one
    have sq : (4294967296 : Nat) ^ 2 = 18446744073709551616 := by decide
    generalize 4294967296 ^ (c + 2) = P at *
    omega

theorem find_natFrom : program.functions.find? (fun f => f.name == "nat_from") = some natFrom := rfl

/-- `nat_from`, which every operation on natural numbers ends with: from the array the arithmetic returned
it gives back the tagged word for the number in it, where that is below 2^63, and gives the array up. What
giving up does is the allocator's; nothing else changes. -/
theorem natFrom_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s after : State)
    (extra : Nat) (unused : UInt64)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs)
    (fits : Runtime.Big.value limbs < 9223372036854775808)
    (dec : outside "lean_dec" [array] s = .ok (unused, after)) :
    program.call outside (limbs.size + extra + 12) "nat_from" [array] s
      = .ok (.gave (UInt64.ofNat (2 * Runtime.Big.value limbs + 1)), after) := by
  have size := holds.2.1
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "nat_result" natResult _ s _ _ find_natResult
    (natResult_word outside array limbs s extra small holds fits)
  simp [Program.call, find_natFrom, find_natResult, natFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
    sizeOf, drop, size]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl, dec]

/-! ## An integer that arrives as a tagged word -/

theorem find_intSign : program.functions.find? (fun f => f.name == "int_sign") = some intSign := rfl
theorem find_intLimbs : program.functions.find? (fun f => f.name == "int_limbs") = some intLimbs := rfl

/-- An integer from -2^31 to 2^31 - 1 as compiled Lean holds it: its 32 bits, as a tagged word. This is
`lean_box((unsigned)n)` in `<lean/lean.h>`; the bits above the 32 are zero, whatever the sign. -/
def intWord (i : Int) : UInt64 := boxed (UInt64.ofNat (i % 4294967296).toNat)

/-- The 32 bits of an integer in that range, as a number. -/
theorem bits_lt (i : Int) : (i % 4294967296).toNat < 4294967296 := by omega

theorem intWord_toNat (i : Int) : (intWord i).toNat = 2 * (i % 4294967296).toNat + 1 := by
  have lt := bits_lt i
  rw [intWord, boxed_small _ (by simp only [UInt64.toNat_ofNat']; omega)]
  simp only [UInt64.toNat_ofNat']
  omega

theorem intWord_tagged (i : Int) : intWord i &&& 1 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_and, intWord_toNat, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod] at this
  have z : (0 : UInt64).toNat = 0 := rfl
  omega

/-- `int_sign` of a tagged word is bit 32 of it: the top bit of the 32 it holds. -/
theorem intSign_tagged (outside : Outside) (fuel : Nat) (o : UInt64) (s : State) (tagged : o &&& 1 ≠ 0) :
    program.call outside (fuel + 4) "int_sign" [o] s = .ok (.gave ((o >>> 32) &&& 1), s) := by
  simp [Program.call, find_intSign, intSign, runAll, Stmt.run, Expr.run, Op.run, bind, put, isWord, Expr.ne,
    Expr.and, Expr.shr, tagged]
  rfl

/-- `int_sign` says rightly whether an integer that arrives as a tagged word is below zero. -/
theorem intSign_word (outside : Outside) (fuel : Nat) (i : Int) (s : State)
    (lo : -2147483648 ≤ i) (hi : i < 2147483648) :
    program.call outside (fuel + 4) "int_sign" [intWord i] s = .ok (.gave (if i < 0 then 1 else 0), s) := by
  rw [intSign_tagged outside fuel _ s (intWord_tagged i)]
  have bit : (intWord i >>> 32) &&& 1 = if i < 0 then 1 else 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, intWord_toNat, show (1 : UInt64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
    split
    · show _ = 1
      omega
    · show _ = 0
      omega
  rw [bit]

/-- What a tagged word holds without its sign: its 32 bits, or for a word whose top bit of those is set, what
they are the negation of within 32 bits. -/
def magnitude (o : UInt64) : UInt64 :=
  if (2147483648 : UInt64) ≤ (o >>> 1) &&& 4294967295 then -((o >>> 1) &&& 4294967295) &&& 4294967295
  else (o >>> 1) &&& 4294967295

/-- For an integer in the range a tagged word holds, that is the integer without its sign. -/
theorem magnitude_intWord (i : Int) (lo : -2147483648 ≤ i) (hi : i < 2147483648) :
    magnitude (intWord i) = UInt64.ofNat i.natAbs := by
  have low : ((intWord i >>> 1) &&& 4294967295).toNat = (i % 4294967296).toNat := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, intWord_toNat,
      show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (1 : UInt64).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]
    omega
  apply UInt64.toNat_inj.mp
  unfold magnitude
  split
  · rename_i h
    rw [UInt64.le_iff_toNat_le, low] at h
    rw [UInt64.toNat_and, UInt64.toNat_neg, low, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat', show UInt64.size = 18446744073709551616 from rfl]
    have t : (2147483648 : UInt64).toNat = 2147483648 := rfl
    omega
  · rename_i h
    rw [UInt64.le_iff_toNat_le, low] at h
    rw [low, UInt64.toNat_ofNat']
    have t : (2147483648 : UInt64).toNat = 2147483648 := rfl
    omega

/-- `int_limbs` hands the arithmetic the limbs of what a tagged word holds without its sign. -/
theorem intLimbs_tagged (outside : Outside) (fuel : Nat) (o array : UInt64) (s s' : State) (tagged : o &&& 1 ≠ 0)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (magnitude o)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 26) "int_limbs" [o] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (magnitude o))
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (magnitude o)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  obtain ⟨memory, run, holds, frame⟩ := limbsOfWord_array outside fuel (magnitude o) array s s' alloc
  obtain ⟨l, hl⟩ := runAll_of_call program outside (fuel + 20) "limbs_of_word" limbsOfWord [magnitude o] s _ _
    find_limbsOfWord run
  refine ⟨memory, ?_, holds, frame⟩
  by_cases neg : (2147483648 : UInt64) ≤ (o >>> 1) &&& 4294967295
  · have m : magnitude o = -((o >>> 1) &&& 4294967295) &&& 4294967295 := by simp [magnitude, neg]
    have nlt : ¬ (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_lt.mpr neg
    rw [m] at hl
    simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, nlt]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]
  · have m : magnitude o = (o >>> 1) &&& 4294967295 := by simp [magnitude, neg]
    have lt : (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_le.mp neg
    rw [m] at hl
    simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, lt]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]

/-- `int_limbs` hands the arithmetic the right limbs for an integer that arrives as a tagged word: those of
the integer without its sign, with no zero limb on top. -/
theorem intLimbs_word (outside : Outside) (fuel : Nat) (i : Int) (array : UInt64) (s s' : State)
    (lo : -2147483648 ≤ i) (hi : i < 2147483648)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (UInt64.ofNat i.natAbs)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 26) "int_limbs" [intWord i] s
        = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (UInt64.ofNat i.natAbs))
      ∧ Runtime.Big.value (wordLimbs (UInt64.ofNat i.natAbs)) = i.natAbs
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (UInt64.ofNat i.natAbs)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  rw [← magnitude_intWord i lo hi] at alloc ⊢
  obtain ⟨memory, run, holds, frame⟩ := intLimbs_tagged outside fuel _ array s s' (intWord_tagged i) alloc
  refine ⟨memory, run, holds, ?_, frame⟩
  rw [wordLimbs_value, magnitude_intWord i lo hi, UInt64.toNat_ofNat']
  omega

/-! ## Reading an integer answer that fits in a tagged word -/

theorem find_intResult : program.functions.find? (fun f => f.name == "int_result") = some intResult := rfl
theorem find_intFrom : program.functions.find? (fun f => f.name == "int_from") = some intFrom := rfl

/-- The number in the first `n` limbs is the number in those `trimmed` keeps. -/
theorem lower_trimCount (limbs : Runtime.Big.Limbs) (n : Nat) :
    Runtime.Big.lower limbs n = Runtime.Big.lower limbs (trimCount limbs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold trimCount
    split
    · rename_i z
      have d : Runtime.Big.digit limbs n = 0 := by simp [Runtime.Big.digit, z]
      rw [← ih]
      show Runtime.Big.lower limbs n + 4294967296 ^ n * Runtime.Big.digit limbs n = _
      rw [d, Nat.mul_zero, Nat.add_zero]
    · rfl

/-- The integer with a size and a sign, the sign as the program passes it: a word that is zero for none. -/
def withSign (negative : UInt64) (size : Nat) : Int := if negative = 0 then (size : Int) else -(size : Int)

theorem intWord_nat (m : Nat) (h : m < 4294967296) : intWord (m : Int) = boxed (UInt64.ofNat m) := by
  rw [intWord, show ((m : Int) % 4294967296).toNat = m from by omega]

theorem intWord_neg (x : UInt64) (pos : 0 < x.toNat) (h : x.toNat ≤ 2147483648) :
    intWord (-(x.toNat : Int)) = boxed (-x &&& 4294967295) := by
  rw [intWord]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_neg, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat', show UInt64.size = 18446744073709551616 from rfl]
  omega

/-- `int_result` reads an answer rightly where the answer is in the range a tagged word holds: from a sign
and the first `n` limbs of an array in memory it gives back the tagged word for that integer, and changes
nothing. The limbs may have zero limbs on top, and a sign on zero comes back as plain zero. -/
theorem intResult_word (outside : Outside) (array negative : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (n extra : Nat) (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64))
    (hn : n ≤ limbs.size)
    (lo : -2147483648 ≤ withSign negative (Runtime.Big.lower limbs n))
    (hi : withSign negative (Runtime.Big.lower limbs n) < 2147483648) :
    program.call outside (n + extra + 10) "int_result" [negative, array, UInt64.ofNat n] s
      = .ok (.gave (intWord (withSign negative (Runtime.Big.lower limbs n))), s) := by
  have run := trimmed_runs outside array limbs s small elements n extra hn
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := lower_trimCount limbs n
  have hle := trimCount_le limbs n
  have bound : Runtime.Big.lower limbs n ≤ 2147483648 := by
    by_cases z : negative = 0 <;> simp [withSign, z] at lo hi <;> omega
  generalize hc : trimCount limbs n = c at hl hv hle
  rcases c with _ | _ | c
  · have v0 : Runtime.Big.lower limbs n = 0 := hv
    have hl0 : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n]) = .ok (.gave 0, s, l) := hl
    have w : withSign negative 0 = 0 := by unfold withSign; split <;> rfl
    rw [v0, w]
    simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl0, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]
    rfl
  · have size1 : 0 < limbs.size := by omega
    have hl1 : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n]) = .ok (.gave 1, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 size1
    have v1 : Runtime.Big.lower limbs n = limbs[0].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size1]
    have nz : limbs[0].toNat ≠ 0 := by
      have := trimCount_top limbs n 0 hc
      simpa [Runtime.Big.digit, Array.getD, size1] using this
    rw [v1] at lo hi bound ⊢
    by_cases z : negative = 0
    · subst z
      have w : withSign 0 limbs[0].toNat = (limbs[0].toNat : Int) := rfl
      rw [w] at hi ⊢
      have h1 : limbs[0].toUInt64 < 2147483648 := by
        rw [UInt64.lt_iff_toNat_lt]; simp; omega
      have fin : boxed limbs[0].toUInt64 = intWord (limbs[0].toNat : Int) := by
        rw [intWord_nat _ (by omega)]
        congr 1
        apply UInt64.toNat_inj.mp
        simp
      simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        hl1, box, Expr.eq, Expr.or, Expr.shl]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
        unbox, Expr.shr, Expr.and, Expr.lt, top, r0, unbox_boxed, h1]
      simpa [boxed] using fin
    · have w : withSign negative limbs[0].toNat = -(limbs[0].toNat : Int) := by simp [withSign, z]
      rw [w] at lo hi ⊢
      have h1 : limbs[0].toUInt64 ≤ 2147483648 := by
        rw [UInt64.le_iff_toNat_le]; simp; omega
      have fin : boxed (-limbs[0].toUInt64 &&& 4294967295) = intWord (-(limbs[0].toNat : Int)) := by
        have := intWord_neg limbs[0].toUInt64 (by simp; omega) (by simp; omega)
        simpa using this.symm
      simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        hl1, box, Expr.eq, Expr.or, Expr.shl]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
        unbox, Expr.shr, Expr.and, Expr.lt, Expr.le, Expr.ne, top, low32, r0, unbox_boxed, h1, z]
      simpa [boxed] using fin
  · exfalso
    have topd := trimCount_top limbs n (c + 1) hc
    have big : 4294967296 ^ 1 ≤ 4294967296 ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have one : 4294967296 ^ (c + 1) * 1 ≤ 4294967296 ^ (c + 1) * Runtime.Big.digit limbs (c + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have lower : Runtime.Big.lower limbs (c + 1 + 1)
        = Runtime.Big.lower limbs (c + 1) + 4294967296 ^ (c + 1) * Runtime.Big.digit limbs (c + 1) := rfl
    have hv' : Runtime.Big.lower limbs n = Runtime.Big.lower limbs (c + 1 + 1) := hv
    rw [Nat.mul_one] at one
    rw [Nat.pow_one] at big
    generalize 4294967296 ^ (c + 1) = P at *
    omega

theorem lower_congr (a b : Runtime.Big.Limbs) (n : Nat)
    (h : ∀ i, i < n → Runtime.Big.digit a i = Runtime.Big.digit b i) :
    Runtime.Big.lower a n = Runtime.Big.lower b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Runtime.Big.lower a n + 4294967296 ^ n * Runtime.Big.digit a n
      = Runtime.Big.lower b n + 4294967296 ^ n * Runtime.Big.digit b n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- An array without its last element is the number in the limbs below that one. -/
theorem value_pop_lower (a : Runtime.Big.Limbs) :
    Runtime.Big.value a.pop = Runtime.Big.lower a (a.size - 1) := by
  rw [← Runtime.Big.lower_size a.pop, Array.size_pop]
  exact lower_congr _ _ _ (fun i hi => by
    simp [Runtime.Big.digit, Array.getD, hi, show i < a.size by omega])

/-- `int_from`, which every operation on integers ends with: from the array the arithmetic returned, limbs
and then a sign, it gives back the tagged word for the integer in it (`signedValue`, which is what
`Runtime/BigProofs.lean` proves the arithmetic's answers about), where that is in the range a tagged word
holds, and gives the array up. What giving up does is the allocator's; nothing else changes. -/
theorem intFrom_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s after : State)
    (n extra : Nat) (unused : UInt64)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs) (size : limbs.size = n + 1)
    (lo : -2147483648 ≤ Runtime.Big.signedValue limbs) (hi : Runtime.Big.signedValue limbs < 2147483648)
    (dec : outside "lean_dec" [array] s = .ok (unused, after)) :
    program.call outside (n + extra + 14) "int_from" [array] s
      = .ok (.gave (intWord (Runtime.Big.signedValue limbs)), after) := by
  have hsize := holds.2.1
  rw [size] at hsize
  have read := holds.2.2 n (by omega)
  rw [← below_count] at read
  have pop : Runtime.Big.value limbs.pop = Runtime.Big.lower limbs n := by
    rw [value_pop_lower, size, Nat.add_sub_cancel]
  generalize hc : UInt64.ofNat (n + 1) = c at hsize read
  have cpos : c ≠ 0 := by
    intro z
    have := congrArg UInt64.toNat (hc.trans z)
    simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
    omega
  have cless : UInt64.ofNat n = c - 1 := by
    rw [← hc]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
    omega
  by_cases top : limbs[n]'(by omega) = 0
  · have sv : Runtime.Big.signedValue limbs = withSign 0 (Runtime.Big.lower limbs n) := by
      simp [Runtime.Big.signedValue, Runtime.Big.intOf, size, Array.getD, top, pop, withSign]
    rw [sv] at lo hi ⊢
    obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult
      (intResult_word outside array 0 limbs s n extra small holds.2.2 (by omega) lo hi)
    rw [cless] at hl
    have hz : (limbs[n]'(by omega)).toUInt64 = 0 := by rw [top]; rfl
    simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hz, hl, dec,
      show boxed 0 >>> 1 = 0 from by decide]
  · have nz : (limbs[n]'(by omega)).toUInt64 ≠ 0 := fun h => top (UInt32.toNat_inj.mp (by
      have := congrArg UInt64.toNat h
      simpa using this))
    have sv : Runtime.Big.signedValue limbs = withSign 1 (Runtime.Big.lower limbs n) := by
      simp [Runtime.Big.signedValue, Runtime.Big.intOf, size, Array.getD, top, pop, withSign]
    rw [sv] at lo hi ⊢
    obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult
      (intResult_word outside array 1 limbs s n extra small holds.2.2 (by omega) lo hi)
    rw [cless] at hl
    simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hl, dec,
      unbox_boxed, nz]

end Mini.Number
