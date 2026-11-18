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
returns some address. Nothing is assumed of the memory there. -/

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

end Mini.Number
