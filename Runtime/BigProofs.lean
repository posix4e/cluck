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

/-! ## And, or -/

/-- What `bitsLoop` does to a pair of limbs, done to a pair of numbers. -/
def bitOp (either : Bool) (x y : Nat) : Nat := if either then x ||| y else x &&& y

/-- The bits of a number are the bits of its lowest limb and the bits of the rest. -/
theorem bitOp_split (either : Bool) (x y p q : Nat) (hx : x < B) (hy : y < B) :
    bitOp either (x + B * p) (y + B * q) = bitOp either x y + B * bitOp either p q := by
  have ex : x + B * p = 2 ^ 32 * p + x := by omega
  have ey : y + B * q = 2 ^ 32 * q + y := by omega
  have hx' : x < 2 ^ 32 := by omega
  have hy' : y < 2 ^ 32 := by omega
  cases either
  · have hr : x &&& y < 2 ^ 32 := Nat.and_lt_two_pow x hy'
    have er : (x &&& y) + B * (p &&& q) = 2 ^ 32 * (p &&& q) + (x &&& y) := by omega
    simp only [bitOp, Bool.false_eq_true, ↓reduceIte]
    rw [ex, ey, er]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hx', Nat.testBit_two_pow_mul_add _ hy',
      Nat.testBit_two_pow_mul_add _ hr]
    split <;> simp [Nat.testBit_and]
  · have hr : x ||| y < 2 ^ 32 := Nat.or_lt_two_pow hx' hy'
    have er : (x ||| y) + B * (p ||| q) = 2 ^ 32 * (p ||| q) + (x ||| y) := by omega
    simp only [bitOp, ↓reduceIte]
    rw [ex, ey, er]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hx', Nat.testBit_two_pow_mul_add _ hy',
      Nat.testBit_two_pow_mul_add _ hr]
    split <;> simp [Nat.testBit_or]

theorem bitsLoop_value (a b : Limbs) (either : Bool) (n i : Nat) (r : Limbs)
    (hend : ∀ k, n ≤ k → bitOp either (tail a k) (tail b k) = 0) :
    value (bitsLoop a b either n i r) = value r + B ^ r.size * bitOp either (tail a i) (tail b i) := by
  fun_induction bitsLoop a b either n i r with
  | case1 i r h x ih =>
    have hx : x.toNat = bitOp either (digit a i) (digit b i) := by
      cases either <;> simp [x, bitOp, digit]
    rw [ih, value_push, Array.size_push, Nat.pow_succ, hx, tail_step a i, tail_step b i,
      bitOp_split _ _ _ _ _ (digit_lt a i) (digit_lt b i), Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
  | case2 i r h => simp [hend i (by omega)]

/-- The limbs `and` returns are those of the number with the bits both have. -/
theorem and_value (a b : Limbs) : value (Runtime.Big.and a b) = value a &&& value b := by
  have hend : ∀ k, (if a.size < b.size then a.size else b.size) ≤ k → bitOp false (tail a k) (tail b k) = 0 := by
    intro k hk
    by_cases h : a.size ≤ k
    · simp [bitOp, tail_of_le a k h]
    · have : b.size ≤ k := by split at hk <;> omega
      simp [bitOp, tail_of_le b k this]
  simp only [Runtime.Big.and]
  rw [bitsLoop_value _ _ _ _ _ _ hend]
  simp [bitOp, value, valueList, tail]

/-- The limbs `or` returns are those of the number with the bits either has. -/
theorem or_value (a b : Limbs) : value (Runtime.Big.or a b) = value a ||| value b := by
  have hend : ∀ k, (if a.size < b.size then b.size else a.size) ≤ k → bitOp true (tail a k) (tail b k) = 0 := by
    intro k hk
    have ha : a.size ≤ k := by split at hk <;> omega
    have hb : b.size ≤ k := by split at hk <;> omega
    simp [bitOp, tail_of_le a k ha, tail_of_le b k hb]
  simp only [Runtime.Big.or]
  rw [bitsLoop_value _ _ _ _ _ _ hend]
  simp [bitOp, value, valueList, tail]

/-! ## Shifts -/

theorem tail_eq_div (a : Limbs) (i : Nat) : tail a i = value a / B ^ i := by
  rw [value_split a i, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt (lower_lt a i),
    Nat.zero_add]

theorem shiftLeftLoop_value (a : Limbs) (bits : UInt64) (i : Nat) (carry : UInt64) (r : Limbs)
    (hb : bits.toNat < 32) (hc : carry.toNat < 2 ^ bits.toNat) :
    value (shiftLeftLoop a bits i carry r) = value r + B ^ r.size * (carry.toNat + 2 ^ bits.toNat * tail a i) := by
  have hp : 2 ^ bits.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  fun_induction shiftLeftLoop a bits i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i
    have scaled : digit a i * 2 ^ bits.toNat ≤ 4294967295 * 2 ^ bits.toNat := Nat.mul_le_mul_right _ (by omega)
    have ht : t.toNat = digit a i * 2 ^ bits.toNat + carry.toNat := by
      have e1 : bits.toNat % 64 = bits.toNat := Nat.mod_eq_of_lt (by omega)
      have e2 : digit a i <<< bits.toNat = digit a i * 2 ^ bits.toNat := Nat.shiftLeft_eq _ _
      simp only [t, UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat, e1]
      rw [Nat.mod_eq_of_lt (by rw [e2]; generalize 2 ^ bits.toNat = P at *; omega),
        ← Nat.shiftLeft_add_eq_or_of_lt hc, e2]
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; generalize 2 ^ bits.toNat = P at *; omega), value_push, Array.size_push, Nat.pow_succ,
      hhigh, hlow, tail_step a i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_add (2 ^ bits.toNat),
      Nat.mul_left_comm (2 ^ bits.toNat), Nat.mul_comm (2 ^ bits.toNat) (digit a i)]
    congr 2
    generalize 2 ^ bits.toNat * tail a (i + 1) = rest
    generalize 2 ^ bits.toNat = P at *
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega)]
    simp

/-- `shiftLeft` multiplies by two for every bit and 2^32 for every whole limb. -/
theorem shiftLeft_value (a : Limbs) (whole : Nat) (bits : UInt64) (hb : bits.toNat < 32) :
    value (shiftLeft a whole bits) = value a * 2 ^ (32 * whole + bits.toNat) := by
  have hB : B ^ whole = 2 ^ (32 * whole) := by rw [Nat.pow_mul]
  rw [shiftLeft, shiftLeftLoop_value _ _ _ _ _ hb (Nat.two_pow_pos _), value_zeros, tail_zero, Nat.pow_add, ← hB]
  simp [zeros, Nat.mul_comm, Nat.mul_assoc]

/-- A shift left by any number of bits a machine word can count multiplies by two that many times. -/
theorem shiftLeftBy_value (a : Limbs) (shift : USize) :
    value (shiftLeftBy a shift) = value a * 2 ^ shift.toNat := by
  have h32 : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
  have whole : (shift / 32).toNat = shift.toNat / 32 := by rw [USize.toNat_div, h32]
  have bits : (shift % 32).toUInt64.toNat = shift.toNat % 32 := by rw [USize.toNat_toUInt64, USize.toNat_mod, h32]
  rw [shiftLeftBy, shiftLeft_value _ _ _ (by rw [bits]; omega), whole, bits]
  congr 2
  omega

/-- Dividing two limbs and all above them by a power of two that divides the base: the lowest limb of the
answer comes from the lowest two, and the rest is the same division one limb up. -/
theorem shift_split (K M N d0 d1 T : Nat) (hK : 0 < K) (hN : K * M = N) (h0 : d0 < N) :
    (d0 + N * (d1 + N * T)) / K = (d0 + N * d1) / K % N + N * ((d1 + N * T) / K) := by
  subst hN
  have e1 : d0 + K * M * (d1 + K * M * T) = (d0 + K * M * d1) + K * (M * (K * M) * T) := by
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have e2 : d1 + K * M * T = d1 + K * (M * T) := by rw [Nat.mul_assoc]
  have e3 : (d0 + K * M * d1) / K / (K * M) = d1 / K := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm K (K * M), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h0, Nat.zero_add]
  have e4 := Nat.mod_add_div ((d0 + K * M * d1) / K) (K * M)
  rw [e3] at e4
  rw [e1, Nat.add_mul_div_left _ _ hK, e2, Nat.add_mul_div_left _ _ hK, Nat.mul_add, ← Nat.add_assoc, e4]
  congr 1
  rw [Nat.mul_comm M (K * M), Nat.mul_assoc]

theorem shiftRightLoop_value (a : Limbs) (bits : UInt64) (n i : Nat) (r : Limbs)
    (hb : bits.toNat < 32) (hn : a.size ≤ n) :
    value (shiftRightLoop a bits n i r) = value r + B ^ r.size * (tail a i / 2 ^ bits.toNat) := by
  fun_induction shiftRightLoop a bits n i r with
  | case1 i r h t ih =>
    have l0 := digit_lt a i; have l1 := digit_lt a (i + 1)
    have ht : t.toNat = (digit a i + B * digit a (i + 1)) / 2 ^ bits.toNat := by
      have e1 : bits.toNat % 64 = bits.toNat := Nat.mod_eq_of_lt (by omega)
      have e2 : digit a (i + 1) <<< 32 % 2 ^ 64 = digit a (i + 1) <<< 32 :=
        Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
      simp only [t, UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat, e1]
      rw [show (32 : UInt64).toNat % 64 = 32 from rfl, e2,
        ← Nat.shiftLeft_add_eq_or_of_lt (show digit a i < 2 ^ 32 by omega), Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow,
        show digit a (i + 1) * 2 ^ 32 + digit a i = digit a i + B * digit a (i + 1) by omega]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    have hKM : 2 ^ bits.toNat * 2 ^ (32 - bits.toNat) = B := by
      rw [← Nat.pow_add, show bits.toNat + (32 - bits.toNat) = 32 by omega]
    have key : tail a i / 2 ^ bits.toNat = t.toNat % B + B * (tail a (i + 1) / 2 ^ bits.toNat) := by
      rw [ht, tail_step a i, tail_step a (i + 1)]
      exact shift_split _ _ _ _ _ _ (Nat.two_pow_pos _) hKM l0
    rw [ih, value_push, Array.size_push, Nat.pow_succ, hlow, key, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
  | case2 i r h => simp [tail_of_le a i (by omega)]

/-- `shiftRight` over the whole of a number divides by two for every bit and 2^32 for every whole limb,
rounding down. -/
theorem shiftRight_value (a : Limbs) (whole n : Nat) (bits : UInt64) (hb : bits.toNat < 32) (hn : a.size ≤ n) :
    value (shiftRight a whole n bits) = value a / 2 ^ (32 * whole + bits.toNat) := by
  have hB : B ^ whole = 2 ^ (32 * whole) := by rw [Nat.pow_mul]
  rw [shiftRight, shiftRightLoop_value _ _ _ _ _ hb hn, tail_eq_div, Nat.div_div_eq_div_mul, Nat.pow_add, ← hB]
  simp [value, valueList]

/-- A shift right by any number of bits a machine word can count halves that many times, rounding down. -/
theorem shiftRightBy_value (a : Limbs) (shift : USize) :
    value (shiftRightBy a shift) = value a / 2 ^ shift.toNat := by
  have h32 : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
  have whole : (shift / 32).toNat = shift.toNat / 32 := by rw [USize.toNat_div, h32]
  have bits : (shift % 32).toUInt64.toNat = shift.toNat % 32 := by rw [USize.toNat_toUInt64, USize.toNat_mod, h32]
  rw [shiftRightBy, shiftRight_value _ _ _ _ (by rw [bits]; omega) (Nat.le_refl _), whole, bits]
  congr 2
  omega

/-! ## Division, where the divisor is one limb or the dividend is shorter

Long division by two limbs or more (`divideLong`, Knuth's algorithm D) is not proved here. -/

theorem lower_size (a : Limbs) : lower a a.size = value a := by
  have := value_split a a.size
  rw [tail_of_le a _ (Nat.le_refl _)] at this
  simpa using this.symm

/-- Division by one limb, from limb `i` down, with `rest` carried in from above: what it adds to the
quotient, times the divisor, and what it leaves, make up `rest` and the limbs below `i`. -/
theorem divideSmallLoop_value (a : Limbs) (d rest : UInt64) (q : Limbs) (i : Nat)
    (hd : d.toNat < B) (hr : rest.toNat < d.toNat) (hi : i ≤ q.size) (hz : ∀ m, m < i → digit q m = 0) :
    value (divideSmallLoop a d rest q i).1 * d.toNat + value (divideSmallLoop a d rest q i).2
        = value q * d.toNat + rest.toNat * B ^ i + lower a i
      ∧ value (divideSmallLoop a d rest q i).2 < d.toNat := by
  induction i generalizing rest q with
  | zero =>
    have low : rest.toUInt32.toNat = rest.toNat := by simp only [UInt64.toNat_toUInt32]; omega
    simp only [divideSmallLoop, value_push, lower, low]
    simp [value, valueList]
    exact hr
  | succ i ih =>
    have la := digit_lt a i
    have dpos : 0 < d.toNat := by omega
    simp only [divideSmallLoop]
    generalize hp : (rest <<< 32) ||| limb a i = part
    have hpart : part.toNat = rest.toNat * B + digit a i := by
      subst hp
      have e : rest.toNat <<< 32 % 2 ^ 64 = rest.toNat <<< 32 :=
        Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
      simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat]
      rw [show (32 : UInt64).toNat % 64 = 32 from rfl, e,
        ← Nat.shiftLeft_add_eq_or_of_lt (show digit a i < 2 ^ 32 by omega), Nat.shiftLeft_eq]
    have hq : (part / d).toNat = part.toNat / d.toNat := UInt64.toNat_div _ _
    have hm : (part % d).toNat = part.toNat % d.toNat := UInt64.toNat_mod _ _
    have qlt : part.toNat / d.toNat < B := by
      rw [Nat.div_lt_iff_lt_mul dpos]
      have : (rest.toNat + 1) * B ≤ d.toNat * B := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlow : (part / d).toUInt32.toNat = part.toNat / d.toNat := by
      simp only [UInt64.toNat_toUInt32, hq]; omega
    have step := ih (part % d) (q.setIfInBounds i (part / d).toUInt32) (by rw [hm]; exact Nat.mod_lt _ dpos)
      (by simp; omega) (fun m hm' => by rw [digit_set_ne _ _ _ _ (by omega)]; exact hz m (by omega))
    have written := value_set q i (part / d).toUInt32 (by omega)
    rw [hz i (by omega), hlow] at written
    have e : value (q.setIfInBounds i (part / d).toUInt32) = value q + B ^ i * (part.toNat / d.toNat) := by
      simpa using written
    have dm := Nat.div_add_mod part.toNat d.toNat
    have key : B ^ i * (part.toNat / d.toNat) * d.toNat + part.toNat % d.toNat * B ^ i
        = rest.toNat * (B ^ i * B) + B ^ i * digit a i := by
      calc B ^ i * (part.toNat / d.toNat) * d.toNat + part.toNat % d.toNat * B ^ i
          = B ^ i * (d.toNat * (part.toNat / d.toNat) + part.toNat % d.toNat) := by
            rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (part.toNat / d.toNat),
              Nat.mul_comm (part.toNat % d.toNat)]
        _ = B ^ i * (rest.toNat * B + digit a i) := by rw [dm, hpart]
        _ = rest.toNat * (B ^ i * B) + B ^ i * digit a i := by rw [Nat.mul_add, Nat.mul_left_comm]
    refine ⟨?_, step.2⟩
    rw [step.1, e, hm, lower, Nat.pow_succ, Nat.add_mul]
    omega

/-- Division by a single limb that is not zero gives the quotient and the remainder. -/
theorem divideSmall_value (a : Limbs) (d : UInt64) (hd : d.toNat < B) (hz : d.toNat ≠ 0) :
    value (divideSmallLoop a d 0 (zeros a.size) a.size).1 = value a / d.toNat ∧
    value (divideSmallLoop a d 0 (zeros a.size) a.size).2 = value a % d.toNat := by
  have zero : (0 : UInt64).toNat = 0 := rfl
  have h := divideSmallLoop_value a d 0 (zeros a.size) a.size hd (by omega) (by simp [zeros])
    (fun m _ => digit_zeros _ m)
  rw [value_zeros, zero, lower_size] at h
  have whole : value (divideSmallLoop a d 0 (zeros a.size) a.size).2 +
      d.toNat * value (divideSmallLoop a d 0 (zeros a.size) a.size).1 = value a := by
    rw [Nat.add_comm, Nat.mul_comm]; simpa using h.1
  have both := (Nat.div_mod_unique (by omega : 0 < d.toNat)).mpr ⟨whole, h.2⟩
  exact ⟨both.1.symm, both.2.symm⟩

theorem value_single (b : Limbs) (h : b.size = 1) : value b = digit b 0 := by
  have s := value_split b 1
  rw [tail_of_le b 1 (by omega)] at s
  simpa [lower] using s

/-- `divide`, for a divisor of one limb that is not zero: the quotient rounded down and the remainder. -/
theorem divide_value_single (a b : Limbs) (h : b.size = 1) (hz : value b ≠ 0) :
    value (divide a b).1 = value a / value b ∧ value (divide a b).2 = value a % value b := by
  have vb := value_single b h
  have lb := digit_lt b 0
  unfold divide
  by_cases short : a.size < b.size
  · have empty : value a = 0 := by
      have := value_lt_pow a
      rw [show a.size = 0 by omega] at this
      simpa using this
    simp only [short, ↓reduceIte]
    rw [empty, Nat.zero_div, Nat.zero_mod]
    exact ⟨rfl, rfl⟩
  · simp only [short, ↓reduceIte]
    simp only [h, beq_self_eq_true, ↓reduceIte]
    rw [vb, ← limb_toNat]
    exact divideSmall_value a (limb b 0) (by rw [limb_toNat]; exact lb) (by rw [limb_toNat]; omega)

/-- `divide`, for a dividend with fewer limbs than the divisor: nothing, and the dividend left over. -/
theorem divide_value_shorter (a b : Limbs) (h : a.size < b.size) (tb : Trimmed b) :
    value (divide a b).1 = value a / value b ∧ value (divide a b).2 = value a % value b := by
  have lt := value_lt_of_shorter a b h tb
  simp only [divide, h, ↓reduceIte]
  rw [Nat.div_eq_of_lt lt, Nat.mod_eq_of_lt lt]
  exact ⟨rfl, rfl⟩

/-! ## Powers -/

theorem value_one : value (one ()) = 1 := by simp [one, low, value, valueList]

theorem powerLoop_value (power result : Limbs) (exponent : USize) (fuel : Nat) (h : exponent.toNat < 2 ^ fuel) :
    value (powerLoop power result exponent fuel) = value result * value power ^ exponent.toNat := by
  induction fuel generalizing power result exponent with
  | zero =>
    have z : exponent.toNat = 0 := by simpa using h
    simp [powerLoop, z]
  | succ fuel ih =>
    have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
    have half : (exponent >>> 1).toNat = exponent.toNat / 2 := by
      have : (1 : USize).toNat % System.Platform.numBits = 1 := by
        rw [one]; rcases System.Platform.numBits_eq with e | e <;> rw [e]
      rw [USize.toNat_shiftRight, this, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have bit : (exponent &&& 1).toNat = exponent.toNat % 2 := by
      rw [USize.toNat_and, one, Nat.and_one_is_mod]
    have step : value power ^ exponent.toNat =
        value power ^ (exponent.toNat % 2) * (value power * value power) ^ (exponent.toNat / 2) := by
      conv => lhs; rw [← Nat.mod_add_div exponent.toNat 2]
      rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]
    have hr : value (if exponent &&& 1 != 0 then trim (mul result power) else result) =
        value result * value power ^ (exponent.toNat % 2) := by
      by_cases o : exponent &&& 1 = 0
      · have : exponent.toNat % 2 = 0 := by rw [← bit, o]; rfl
        simp [o, this]
      · have : (exponent &&& 1).toNat ≠ 0 := fun e => o (USize.toNat_inj.mp (by simpa using e))
        have : exponent.toNat % 2 = 1 := by omega
        simp [o, this, trim_value, mul_value]
    unfold powerLoop
    by_cases z : exponent = 0
    · simp [z]
    · by_cases z2 : exponent >>> 1 = 0
      · have : exponent.toNat / 2 = 0 := by rw [← half, z2]; rfl
        simp only [beq_iff_eq, z, z2, ↓reduceIte]
        rw [hr, step, this, Nat.pow_zero, Nat.mul_one]
      · simp only [beq_iff_eq, z, z2, ↓reduceIte]
        rw [ih _ _ _ (by rw [half, Nat.pow_succ] at *; omega), hr, trim_value, mul_value, half, step, Nat.mul_assoc]

/-- The limbs `power` returns are those of the power, for any exponent a machine word holds. Anything to
the power 0 is 1. -/
theorem power_value (a : Limbs) (exponent : USize) : value (power a exponent) = value a ^ exponent.toNat := by
  rw [power, powerLoop_value _ _ _ _ (USize.toNat_lt exponent), value_one, Nat.one_mul]

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

/-- Signed addition, on numbers with no zero limb on top: `compare` has to say which is larger. -/
theorem intAdd_value (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn)
    (ta : Trimmed a) (tb : Trimmed b) :
    signedValue (intAdd an a bn b) = intOf (an != 0) a + intOf (bn != 0) b := by
  have same : ∀ s : UInt8, signedValue (intAdd s a s b) = intOf (s != 0) a + intOf (s != 0) b := by
    intro s
    simp only [intAdd, beq_self_eq_true, ↓reduceIte, signedValue_signed, intOf, add_value]
    split <;> omega
  have differ : ∀ s t : UInt8, (s == t) = false →
      signedValue (intAdd s a t b) =
        if value a < value b then intOf (t != 0) (sub b a)
        else if value a = value b then 0 else intOf (s != 0) (sub a b) := by
    intro s t h
    simp only [intAdd, h, Bool.false_eq_true, ↓reduceIte, compare_order a b ta tb, order]
    by_cases h1 : value a < value b
    · simp only [h1, ↓reduceIte, show ((0 : UInt8) == 1) = false from rfl, show ((0 : UInt8) == 2) = false from rfl,
        Bool.false_eq_true, signedValue_signed]
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, show ((1 : UInt8) == 1) = true from rfl, signedValue_signed]
        simp [intOf, value, valueList]
      · simp only [h1, h2, ↓reduceIte, show ((2 : UInt8) == 1) = false from rfl, show ((2 : UInt8) == 2) = true from rfl,
          Bool.false_eq_true, signedValue_signed]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact same 0
  · rw [differ 0 1 rfl]
    by_cases h1 : value a < value b
    · have := sub_value b a (by omega)
      simp only [h1, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl, show ((0 : UInt8) != 0) = false from rfl,
        Bool.false_eq_true, this]
      omega
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true]
        omega
      · have := sub_value a b (by omega)
        simp only [h1, h2, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, this]
        omega
  · rw [differ 1 0 rfl]
    by_cases h1 : value a < value b
    · have := sub_value b a (by omega)
      simp only [h1, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl, show ((0 : UInt8) != 0) = false from rfl,
        Bool.false_eq_true, this]
      omega
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true]
        omega
      · have := sub_value a b (by omega)
        simp only [h1, h2, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, this]
        omega
  · exact same 1

/-- 0, 1 or 2 as the first integer is less than, equal to or greater than the second. -/
def intOrder (x y : Int) : UInt8 := if x < y then 0 else if x = y then 1 else 2

/-- Signed comparison, on numbers with no zero limb on top. A number passed as below zero is not zero:
the runtime has no "minus zero", and `intCompare` would call it less than zero. -/
theorem intCompare_order (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn)
    (ta : Trimmed a) (tb : Trimmed b) (za : an = 1 → value a ≠ 0) (zb : bn = 1 → value b ≠ 0) :
    intCompare an a bn b = intOrder (intOf (an != 0) a) (intOf (bn != 0) b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp only [intCompare, show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      compare_order a b ta tb, order, intOrder, intOf]
    by_cases h1 : value a < value b
    · have : (value a : Int) < value b := by omega
      simp [h1, this]
    · by_cases h2 : value a = value b
      · simp [h2]
      · have h3 : ¬ (value a : Int) < value b := by omega
        have h4 : (value a : Int) ≠ value b := by omega
        simp [h1, h2, h3, h4]
  · have := zb rfl
    have h3 : ¬ (value a : Int) < -(value b : Int) := by omega
    have h4 : (value a : Int) ≠ -(value b : Int) := by omega
    simp [intCompare, intOrder, intOf, h3, h4]
  · have := za rfl
    have h3 : -(value a : Int) < (value b : Int) := by omega
    simp [intCompare, intOrder, intOf, h3]
  · simp only [intCompare, show ((1 : UInt8) != 1) = false from rfl, show ((1 : UInt8) != 0) = true from rfl,
      Bool.false_eq_true, ↓reduceIte, compare_order a b ta tb, order, intOrder, intOf]
    by_cases h1 : value a < value b
    · have h3 : ¬ -(value a : Int) < -(value b : Int) := by omega
      have h4 : -(value a : Int) ≠ -(value b : Int) := by omega
      simp only [h1, ↓reduceIte, h3, h4]
      rfl
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, Int.lt_irrefl, ↓reduceIte]
        rfl
      · have h3 : -(value a : Int) < -(value b : Int) := by omega
        simp only [h1, h2, ↓reduceIte, h3]
        rfl

end Runtime.Big
