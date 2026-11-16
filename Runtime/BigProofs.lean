import Runtime.Big

/-! # What the runtime's arithmetic computes

`Runtime/Big.lean` works on limbs. This says what number a row of limbs is, and proves that each operation
returns the limbs of the number it should: the sum, the difference, the product, and so on, as Lean's `Nat`
defines them. Nothing here runs; no image imports it. -/

namespace Runtime.Big

local notation "B" => (4294967296 : Nat)

/-- The number a list of limbs is, least significant first. -/
def valueList : List UInt32 → Nat
  | [] => 0
  | x :: xs => x.toNat + B * valueList xs

/-- The number an array of limbs is. -/
def value (a : Limbs) : Nat := valueList a.toList

/-- The number the limbs from `i` up are. -/
def tail (a : Limbs) (i : Nat) : Nat := valueList (a.toList.drop i)

/-- Limb `i` as a number; zero beyond the end. -/
def digit (a : Limbs) (i : Nat) : Nat := (a.getD i 0).toNat

theorem valueList_append (xs ys : List UInt32) :
    valueList (xs ++ ys) = valueList xs + B ^ xs.length * valueList ys := by
  induction xs with
  | nil => simp [valueList]
  | cons x xs ih =>
    simp only [List.cons_append, valueList, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm, Nat.mul_assoc]

theorem value_push (a : Limbs) (x : UInt32) : value (a.push x) = value a + B ^ a.size * x.toNat := by
  simp [value, Array.toList_push, valueList_append, valueList]

theorem tail_zero (a : Limbs) : tail a 0 = value a := by simp [tail, value]

theorem digit_lt (a : Limbs) (i : Nat) : digit a i < B := (a.getD i 0).toNat_lt

theorem tail_step (a : Limbs) (i : Nat) : tail a i = digit a i + B * tail a (i + 1) := by
  by_cases h : i < a.size
  · have : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]; simp
    simp [tail, digit, this, valueList, Array.getD, h]
  · have h1 : a.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : a.toList.drop (i + 1) = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [tail, digit, h1, h2, valueList, Array.getD, h]

theorem tail_of_le (a : Limbs) (i : Nat) (h : a.size ≤ i) : tail a i = 0 := by
  simp [tail, valueList, List.drop_eq_nil_of_le (show a.toList.length ≤ i by simpa using h)]

theorem limb_toNat (a : Limbs) (i : Nat) : (limb a i).toNat = digit a i := by
  simp [limb, digit]

/-! ## Addition -/

theorem addLoop_value (a b : Limbs) (n i : Nat) (carry : UInt64) (r : Limbs)
    (ha : a.size ≤ n) (hb : b.size ≤ n) (hc : carry.toNat ≤ 1) :
    value (addLoop a b n i carry r) = value r + B ^ r.size * (carry.toNat + tail a i + tail b i) := by
  fun_induction addLoop a b n i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have ht : t.toNat = digit a i + digit b i + carry.toNat := by
      simp only [t, UInt64.toNat_add, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, tail_step b i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega), tail_of_le b i (by omega)]
    simp

/-- The limbs `add` returns are those of the sum. -/
theorem add_value (a b : Limbs) : value (add a b) = value a + value b := by
  simp only [add]
  split <;> rw [addLoop_value _ _ _ _ _ _ (by omega) (by omega) (by decide)] <;>
    simp [value, valueList, tail]

/-! ## Subtraction -/

theorem subLoop_value (a b : Limbs) (i : Nat) (borrow : UInt64) (r : Limbs)
    (hb : borrow.toNat ≤ 1) (h : tail b i + borrow.toNat ≤ tail a i) :
    value (subLoop a b i borrow r) = value r + B ^ r.size * (tail a i - tail b i - borrow.toNat) := by
  fun_induction subLoop a b i borrow r with
  | case1 i borrow r hi t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have sa := tail_step a i; have sb := tail_step b i
    have ht : t.toNat = (digit a i + 18446744073709551616 - digit b i - borrow.toNat) % 18446744073709551616 := by
      simp only [t, UInt64.toNat_sub, limb_toNat]; omega
    have hhigh : (t >>> 63).toNat = t.toNat / 9223372036854775808 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega) (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i borrow r hi =>
    have := tail_of_le a i (by omega)
    have : tail a i - tail b i - borrow.toNat = 0 := by omega
    simp [this]

/-- For `a` at least `b`, the limbs `sub` returns are those of the difference. -/
theorem sub_value (a b : Limbs) (h : value b ≤ value a) : value (sub a b) = value a - value b := by
  simp only [sub]
  rw [subLoop_value _ _ _ _ _ (by decide) (by simpa [tail_zero] using h)]
  simp [value, valueList, tail]

/-! ## Zero limbs on top -/

theorem value_pop (a : Limbs) (h : a.size ≠ 0) (top : a.getD (a.size - 1) 0 = 0) : value a.pop = value a := by
  have ne : a.toList ≠ [] := by intro e; apply h; simpa using congrArg List.length e
  have last : a.toList.getLast ne = 0 := by
    rw [List.getLast_eq_getElem]
    have hlt : a.size - 1 < a.size := by omega
    have := top
    simp [Array.getD, hlt] at this
    simpa using this
  have split := List.dropLast_concat_getLast ne
  rw [last] at split
  have := congrArg valueList split
  rw [valueList_append] at this
  simpa [value, Array.toList_pop, valueList] using this

/-- Taking the zero limbs off the top leaves the same number. -/
theorem trim_value (a : Limbs) : value (trim a) = value a := by
  fun_induction trim a with
  | case1 a h => rfl
  | case2 a h top ih => rw [ih, value_pop a h (by simpa using top)]
  | case3 a h top => rfl

/-! ## Writing a limb -/

theorem value_set (r : Limbs) (k : Nat) (v : UInt32) (h : k < r.size) :
    value (r.setIfInBounds k v) + B ^ k * digit r k = value r + B ^ k * v.toNat := by
  have hk : k < r.toList.length := by simpa using h
  have before : r.toList = r.toList.take k ++ r[k] :: r.toList.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k r.toList, List.drop_eq_getElem_cons hk]
    simp
  have after : (r.setIfInBounds k v).toList = r.toList.take k ++ v :: r.toList.drop (k + 1) := by
    simp [Array.toList_setIfInBounds, List.set_eq_take_append_cons_drop]
    intro hle; omega
  have len : (r.toList.take k).length = k := by simp; omega
  have d : digit r k = r[k].toNat := by simp [digit, Array.getD, h]
  rw [value, after, valueList_append, len, d]
  conv => rhs; rw [value, before, valueList_append, len]
  simp only [valueList]
  generalize valueList (r.toList.take k) = low
  generalize valueList (r.toList.drop (k + 1)) = high
  generalize B ^ k = P
  rw [Nat.mul_add, Nat.mul_add]
  omega

theorem digit_set_ne (r : Limbs) (k m : Nat) (v : UInt32) (h : m ≠ k) :
    digit (r.setIfInBounds k v) m = digit r m := by
  simp [digit, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-! ## Multiplication by one limb, and decimal literals -/

theorem scaleLoop_value (a : Limbs) (m : UInt64) (i : Nat) (carry : UInt64) (r : Limbs)
    (hm : m.toNat < B) (hc : carry.toNat < B) :
    value (scaleLoop a m i carry r) = value r + B ^ r.size * (carry.toNat + m.toNat * tail a i) := by
  fun_induction scaleLoop a m i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i
    have bound : digit a i * m.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have ht : t.toNat = digit a i * m.toNat + carry.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_add m.toNat, Nat.mul_left_comm m.toNat,
      Nat.mul_comm m.toNat (digit a i)]
    congr 2
    generalize m.toNat * tail a (i + 1) = rest
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega)]
    simp

/-- One more digit of a decimal literal. -/
theorem decimal_value (a : Limbs) (d : UInt32) : value (decimal a d) = value a * 10 + d.toNat := by
  have hd := d.toNat_lt
  rw [decimal, trim_value, scaleLoop_value _ _ _ _ _ (by decide) (by simpa using hd)]
  simp [value, valueList, tail_zero, Nat.mul_comm, Nat.add_comm]

/-! ## Multiplication -/

theorem mulRow_size (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs) :
    (mulRow a x i j carry r).size = r.size := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih => simp [ih]
  | case2 j carry r h => simp

theorem mulRow_digit (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs) (m : Nat)
    (hm : i + a.size < m) : digit (mulRow a x i j carry r) m = digit r m := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih => rw [ih, digit_set_ne _ _ _ _ (by omega)]
  | case2 j carry r h => rw [digit_set_ne _ _ _ _ (by omega)]

/-- A row of the multiplication adds `x` times what is left of `a`, and the carry, at its place. -/
theorem mulRow_value (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs)
    (hx : x.toNat < B) (hc : carry.toNat < B) (hj : j ≤ a.size) (hsize : i + a.size < r.size)
    (htop : digit r (i + a.size) = 0) :
    value (mulRow a x i j carry r) = value r + B ^ (i + j) * (carry.toNat + x.toNat * tail a j) := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih =>
    have la := digit_lt a j; have ld := digit_lt r (i + j)
    have bound : digit a j * x.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have ht : t.toNat = digit a j * x.toNat + digit r (i + j) + carry.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    have written := value_set r (i + j) t.toUInt32 (by omega)
    rw [ih (by rw [hhigh]; omega) (by omega) (by simpa using hsize) (by rw [digit_set_ne _ _ _ _ (by omega)]; exact htop),
      hhigh, show i + (j + 1) = i + j + 1 from rfl, Nat.pow_succ, tail_step a j, Nat.mul_add x.toNat,
      Nat.mul_left_comm x.toNat, Nat.mul_comm x.toNat (digit a j)]
    rw [hlow] at written
    generalize digit a j * x.toNat = product at *
    generalize x.toNat * tail a (j + 1) = rest at *
    generalize value (r.setIfInBounds (i + j) t.toUInt32) = after at *
    generalize B ^ (i + j) = P at *
    generalize t.toNat = T at *
    have inner : T % B + B * (T / B + rest) = carry.toNat + (product + B * rest) + digit r (i + j) := by omega
    have scaled := congrArg (P * ·) inner
    simp only [Nat.mul_add, Nat.mul_assoc] at scaled written ⊢
    omega
  | case2 j carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    have written := value_set r (i + a.size) carry.toUInt32 hsize
    rw [htop, hlow] at written
    have : j = a.size := by omega
    subst this
    rw [tail_of_le a _ (Nat.le_refl _)]
    simpa using written

theorem valueList_replicate (n : Nat) : valueList (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, valueList, ih]

theorem value_zeros (n : Nat) : value (zeros n) = 0 := by
  simp [value, zeros, low, valueList_replicate]

theorem digit_zeros (n m : Nat) : digit (zeros n) m = 0 := by
  unfold digit zeros low
  by_cases h : m < n <;> simp [Array.getD, h]

theorem mulLoop_value (a b : Limbs) (i : Nat) (r : Limbs)
    (hsize : r.size = a.size + b.size) (hzero : ∀ m, i + a.size ≤ m → digit r m = 0) :
    value (mulLoop a b i r) = value r + B ^ i * (value a * tail b i) := by
  fun_induction mulLoop a b i r with
  | case1 i r h ih =>
    have lb := digit_lt b i
    have row := mulRow_value a (limb b i) i 0 0 r (by rw [limb_toNat]; exact lb) (by decide) (Nat.zero_le _)
      (by omega) (hzero _ (Nat.le_refl _))
    rw [ih (by rw [mulRow_size]; exact hsize)
        (fun m hm => by rw [mulRow_digit _ _ _ _ _ _ _ (by omega)]; exact hzero m (by omega)),
      row, limb_toNat, tail_zero, Nat.pow_succ, tail_step b i, Nat.mul_add (value a), Nat.mul_left_comm (value a)]
    simp only [Nat.add_zero, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_add, Nat.mul_comm (digit b i) (value a)]
    generalize value a * digit b i = product
    generalize value a * tail b (i + 1) = rest
    generalize B ^ i = P
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  | case2 i r h => simp [tail_of_le b i (by omega)]

/-- The limbs `mul` returns are those of the product. -/
theorem mul_value (a b : Limbs) : value (mul a b) = value a * value b := by
  rw [mul, mulLoop_value a b 0 _ (by simp [zeros]) (fun m _ => digit_zeros _ m), value_zeros, tail_zero]
  simp

/-! ## Comparison -/

/-- The number the limbs below `i` are. -/
def lower (a : Limbs) : Nat → Nat
  | 0 => 0
  | i + 1 => lower a i + B ^ i * digit a i

theorem value_split (a : Limbs) (i : Nat) : value a = lower a i + B ^ i * tail a i := by
  induction i with
  | zero => simp [lower, tail_zero]
  | succ i ih =>
    rw [ih, tail_step a i, lower, Nat.pow_succ]
    generalize B ^ i = P
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

theorem lower_lt (a : Limbs) (i : Nat) : lower a i < B ^ i := by
  induction i with
  | zero => simp [lower]
  | succ i ih =>
    have d := digit_lt a i
    have : B ^ i * digit a i ≤ B ^ i * 4294967295 := Nat.mul_le_mul_left _ (by omega)
    rw [lower, Nat.pow_succ]
    generalize B ^ i = P at *
    omega

/-- 0, 1 or 2 as the first is smaller than, equal to or larger than the second: what `compare` answers. -/
def order (x y : Nat) : UInt8 := if x < y then 0 else if x = y then 1 else 2

theorem compareFrom_order (a b : Limbs) (i : Nat) (same : tail a i = tail b i) :
    compareFrom a b i = order (value a) (value b) := by
  induction i with
  | zero => simp [compareFrom, order, ← tail_zero, same]
  | succ i ih =>
    have sa := value_split a (i + 1); have sb := value_split b (i + 1)
    have la := lower_lt a i; have lb := lower_lt b i
    have da := digit_lt a i; have db := digit_lt b i
    rw [same] at sa
    simp only [lower, Nat.pow_succ] at sa sb
    simp only [compareFrom, UInt64.lt_iff_toNat_lt, limb_toNat]
    by_cases h1 : digit a i < digit b i
    · have : B ^ i * (digit a i + 1) ≤ B ^ i * digit b i := Nat.mul_le_mul_left _ (by omega)
      simp only [h1, ↓reduceIte, order]
      generalize B ^ i = P at *
      generalize P * B * tail b (i + 1) = high at *
      simp only [Nat.mul_add, Nat.mul_one] at this
      have : value a < value b := by omega
      simp [this]
    · by_cases h2 : digit b i < digit a i
      · have : B ^ i * (digit b i + 1) ≤ B ^ i * digit a i := Nat.mul_le_mul_left _ (by omega)
        simp only [h1, h2, ↓reduceIte, order]
        generalize B ^ i = P at *
        generalize P * B * tail b (i + 1) = high at *
        simp only [Nat.mul_add, Nat.mul_one] at this
        have : value b < value a := by omega
        have h3 : ¬ value a < value b := by omega
        have h4 : value a ≠ value b := by omega
        simp [h3, h4]
      · have eq : digit a i = digit b i := by omega
        simp only [h1, h2, ↓reduceIte]
        exact ih (by rw [tail_step a i, tail_step b i, eq, same])

/-- No zero limb on top: how a number arrives, and what `trim` leaves. -/
def Trimmed (a : Limbs) : Prop := a.size = 0 ∨ digit a (a.size - 1) ≠ 0

theorem value_lt_pow (a : Limbs) : value a < B ^ a.size := by
  have := value_split a a.size
  rw [tail_of_le a _ (Nat.le_refl _)] at this
  have := lower_lt a a.size
  omega

theorem pow_le_value (a : Limbs) (h : a.size ≠ 0) (t : Trimmed a) : B ^ (a.size - 1) ≤ value a := by
  have top : digit a (a.size - 1) ≠ 0 := by rcases t with z | nz; exact absurd z h; exact nz
  have s := value_split a (a.size - 1)
  rw [tail_step a (a.size - 1)] at s
  have : B ^ (a.size - 1) * 1 ≤ B ^ (a.size - 1) * (digit a (a.size - 1) + B * tail a (a.size - 1 + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem value_lt_of_shorter (a b : Limbs) (h : a.size < b.size) (t : Trimmed b) : value a < value b := by
  have ha := value_lt_pow a
  have hb := pow_le_value b (by omega) t
  have : B ^ a.size ≤ B ^ (b.size - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- On numbers with no zero limb on top, `compare` says which is larger. -/
theorem compare_order (a b : Limbs) (ta : Trimmed a) (tb : Trimmed b) : compare a b = order (value a) (value b) := by
  simp only [compare]
  by_cases h1 : a.size < b.size
  · simp [h1, order, value_lt_of_shorter a b h1 tb]
  · by_cases h2 : b.size < a.size
    · have := value_lt_of_shorter b a h2 ta
      have h3 : ¬ value a < value b := by omega
      have h4 : value a ≠ value b := by omega
      simp [h1, h2, order, h3, h4]
    · simp only [h1, h2, ↓reduceIte]
      exact compareFrom_order a b a.size (by rw [tail_of_le a _ (Nat.le_refl _), tail_of_le b _ (by omega)])

/-- Subtraction of natural numbers: the difference, or zero where there is none. -/
theorem natSub_value (a b : Limbs) (ta : Trimmed a) (tb : Trimmed b) : value (natSub a b) = value a - value b := by
  simp only [natSub, compare_order a b ta tb, order]
  by_cases h1 : value a < value b
  · have z : value a - value b = 0 := by omega
    simp only [h1, ↓reduceIte, show ((0 : UInt8) == 2) = false from rfl, Bool.false_eq_true, z]
    rfl
  · by_cases h2 : value a = value b
    · simp only [h2, Nat.lt_irrefl, ↓reduceIte, show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true,
        Nat.sub_self]
      rfl
    · simp only [h1, h2, ↓reduceIte, show ((2 : UInt8) == 2) = true from rfl]
      exact sub_value a b (by omega)

/-! ## Integers -/

/-- The integer with this sign and these limbs. -/
def intOf (negative : Bool) (limbs : Limbs) : Int := if negative then -(value limbs : Int) else value limbs

/-- The integer a result is: its limbs, then one more element that is not zero if it is below zero. -/
def signedValue (r : Limbs) : Int := intOf (r.getD (r.size - 1) 0 != 0) r.pop

theorem signedValue_signed (negative : Bool) (limbs : Limbs) :
    signedValue (signed negative limbs) = intOf negative limbs := by
  cases negative <;> simp [signedValue, signed, low, Array.getD]

/-- A sign as the runtime passes it: 0, or 1 for a number below zero. -/
def IsSign (s : UInt8) : Prop := s = 0 ∨ s = 1

theorem intMul_value (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn) :
    signedValue (intMul an a bn b) = intOf (an != 0) a * intOf (bn != 0) b := by
  rw [intMul, signedValue_signed]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [intOf, mul_value, Int.natCast_mul, Int.mul_neg, Int.neg_mul]

end Runtime.Big
