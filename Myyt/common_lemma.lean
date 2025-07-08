import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.RCLike.Basic

open Nat

-- nat lemmas

lemma nat_add_mul_left_div_left {a b c : ℕ} (c_pos : 0 < c) : (c * a + b) / c = a + b / c := by
  rw [add_comm]
  rw [Nat.add_mul_div_left _ _ c_pos]
  ring

lemma nat_add_mul_left_mod_left {a b c : ℕ} : (c * a + b) % c = b % c := by
  rw [add_comm, Nat.add_mul_mod_self_left]

lemma add_mul_congr_factor_lt_contra {a b c d e : ℕ} :
    c < a → b < d → ¬ (a * b + c = a * d + e) := by
  intro cp ep h
  have h3 : a * b + c < a * (b + 1) := by
    apply add_lt_add_left
    linarith
  have h4 : a * (b + 1) ≤ a * d := by
    apply mul_le_mul
    linarith
    exact Nat.succ_le_of_lt ep
    exact Nat.zero_le (b + 1)
    exact Nat.zero_le a
  linarith

lemma add_mul_congr_factor {a b c d e : ℕ} :
    c < a → e < a → a * b + c = a * d + e → b = d := by
  intro cp ep h
  by_contra h1
  cases Nat.lt_or_gt_of_ne h1 with
  | inl h2 => exact add_mul_congr_factor_lt_contra cp h2 h
  | inr h2 => exact add_mul_congr_factor_lt_contra ep h2 h.symm

lemma add_mul_congr {a b c d e : ℕ} :
    a * b + c = a * d + e → c < a → e < a → b = d ∧ c = e := by
  intro h cp ep
  cases add_mul_congr_factor cp ep h with
  | refl =>
    simp
    simp at h
    exact h


section nat_mod

variable (n : ℕ) {m : ℕ}

lemma nat_decomposable_mul_add : 0 < m → ∃ r s, s < m ∧ n = m * r + s := by
  intro mh
  induction n with
  | zero =>
    use 0, 0
    constructor
    exact mh
    simp
  | succ n ih =>
    rcases ih with ⟨r', s', ⟨h1, h2⟩⟩
    by_cases c : s' + 1 < m
    use r', (s' + 1)
    constructor
    assumption
    rw [h2]
    ring
    have c' : m = s' + 1 := by linarith
    use (r' + 1), (s' + 1 - m)
    rw [c']
    constructor
    simp
    rw [h2, c']
    simp
    ring


lemma nat_decompose_mul_add : 0 < m → n = m * (n / m) + (n % m) := by
  intro mh
  rcases nat_decomposable_mul_add n mh with ⟨r, s, ⟨h1, h2⟩⟩
  apply Eq.trans h2
  congr
  rw [h2, add_comm, Nat.add_mul_div_left]
  rw [Nat.div_eq_of_lt h1]
  simp
  exact mh
  rw [h2, Nat.add_mod, Nat.mod_eq_of_lt h1]
  simp
  symm
  exact Nat.mod_eq_of_lt h1

end nat_mod

-- fin coe simplication lemmas

--@[simp]
--lemma fin_coe_coe_nat_eq_self (n : ℕ) : ((n : Fin (n.succ)) : ℕ) = n := by

-- fin lemmas
lemma fin_has_zero {n : ℕ} (i : Fin n) : 0 < n := by
  cases i with | mk i hi =>
  have h: 0 ≤ i := by
    simp
  exact Nat.lt_of_le_of_lt h hi


lemma fin_mul_left_has_zero {m p : ℕ} (i : Fin (m * p)) : 0 < m := by
  apply Nat.pos_of_mul_pos_right
  exact Fin.pos i

lemma fin_mul_right_has_zero {m p : ℕ} (i : Fin (m * p)) : 0 < p := by
  apply Nat.pos_of_mul_pos_left
  exact Fin.pos i

lemma fin_add_mul_lt {m p : ℕ} (r : Fin m) (v : Fin p) :
    p * r + v < m * p := by
  cases r with | mk r hr =>
  cases v with | mk v hv =>
  simp only [Fin.val_mk]
  have f1 : p * (r + 1) ≤ p * m := by
    apply Nat.mul_le_mul
    linarith
    apply Nat.add_one_le_of_lt
    exact hr
  calc p * r + v < p * r + p := by linarith
               _ = p * (r + 1) := by ring
               _ ≤ p * m := f1
               _ = m * p := by ring


-- `cast` reduction: `fin n` cast to `fin n'` coe'd to `ℕ`.
lemma coe_cast_fin_h {n n'} (h : n = n') (i : Fin n) :
    (((cast (congrArg Fin h) (i : Fin n)) : Fin n') : Nat) = (i : Nat) := by
  cases h
  rfl

lemma coe_cast_fin {n n'} (h : n = n') (i : Fin n) :
    (((cast (congrArg Fin h) (i : Fin n)) : Fin n') : Nat) = i := by
  rw [coe_cast_fin_h]
  exact h

--------------------------------------------------------------------------------
-- `cast` helpers

section cast

variable {A B : Type}
variable {a : A}
variable {b : B}

lemma cast_roundtrip (H1 : A = B) : cast H1.symm (cast H1 a) = a := by
  cases H1
  rfl

lemma cast_eq_of_heq (H1: A = B) (h : HEq a b) : cast H1 a = b := by
  cases h
  rfl

end cast

section fun_cast

variable {A1 A2 R : Type}
variable (f : A1 → R)

lemma congr_heq_arg {x' : A2} {x : A1} (h : HEq x' x) : (A1 → R) = (A2 → R) := by
  cases h
  rfl

lemma cast_fun_apply_eq_of_heq_arg (x' : A2) (x : A1) (h : HEq x' x) :
    cast (congr_heq_arg h) f x' = f x := by
  cases h
  rfl


--theorem cast_apply (h : A1 = A2) (x' : A2) :
--    cast (congrArg _ h) f x' = f (cast h.symm x') := by
--  rw [cast_fun_apply_eq_of_heq_arg]




variable {B1 B2 : Type}
variable (f2 : A1 → B1 → R)

lemma congr_heq_arg2 {x' : A2} {y' : B2} {x : A1} {y : B1} (h1 : HEq x' x) (h2 : HEq y' y) :
    (A1 → B1 → R) = (A2 → B2 → R) := by
  cases h1
  cases h2
  rfl

lemma cast_fun_apply_eq_of_heq_arg2 (x1 : A2) (x2 : B2) (y1 : A1) (y2 : B1)
    (h1 : HEq x1 y1) (h2 : HEq x2 y2) :
    cast (congr_heq_arg2 h1 h2) f2 x1 x2 = f2 y1 y2 := by
  cases h1
  cases h2
  rfl

--theorem cast_apply2 (ha : A1 = A2) (hb : B1 = B2) (x : A2) (y : B2) :
--    cast (congrArg2 _ ha hb) f2 x y = f2 (cast ha.symm x) (cast hb.symm y) := by
--  rw [cast_fun_apply_eq_of_heq_arg2]

end fun_cast
