import Myyt.matrix
import Myyt.matrix_inner_product
import Myyt.common_lemma
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic--det
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse--inv
import Init.Data.Nat.Div.Lemmas

--import Mathlib.Analysis.Matrix

open scoped BigOperators
open qMatrix
open Matrix

local notation "conj" x  => (starRingEnd ℂ) x

lemma real.lt_of_lt_pow_two {a b : ℝ} (h : a^2 < b^2) (an : 0 ≤ a) (bn : 0 ≤ b) : a < b := by
  rw [← Real.sqrt_mul_self an]
  rw [← Real.sqrt_mul_self bn]
  repeat rw [pow_two] at h
  apply Real.sqrt_lt_sqrt at h
  exact h
  rw [← pow_two]
  exact pow_two_nonneg a

lemma real.add_squares_le_square_add (x y : ℝ) (xn : 0 ≤ x) (yn : 0 ≤ y) : x^2 + y^2 ≤ (x + y)^2 := by
  rw [pow_two, pow_two, pow_two]
  ring_nf
  simp
  exact mul_nonneg xn yn



-- (pure) ℂ lemmas
--@[simp]
--lemma Complex.abs_nonneg' (c : ℂ) : 0 ≤ Complex.abs c := by

@[simp]
lemma Complex.normSq_nonneg' (c : ℂ) : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c

@[simp]
lemma Complex.conj_mul (c : ℂ) : (starRingEnd ℂ) c * c = Complex.normSq c := by
  rw [mul_comm]
  exact Complex.mul_conj c

--@[simp]
--lemma Complex.conj_mul' (c : ℂ) : c * c.conj = Complex.normSq c := Complex.mul_conj c


lemma Complex.re_add_eq_add_re (a b : ℂ) : (a + b).re = a.re + b.re := rfl


-- ℂ + RCLike
lemma Complex.mul_conj_abs_square (c : ℂ) : (starRingEnd ℂ) c * c = |c| ^ 2 := by
  simp
  norm_cast
  exact Complex.normSq_eq_abs _

lemma Complex.abs_of_real' (x : ℝ) : abs x = Complex.abs (x : ℂ) := by
  rfl

lemma Complex.re_conj_eq_re (c : ℂ) : (conj c).re = c.re := by
  rfl

--lackof solve
lemma Complex.conj_sum_dist {n} (f : Fin n → ℂ) : (∑ k, conj (f k)) = conj (∑ k, f k) := by
  simp


@[simp]
lemma Complex.norm_sq_eq_mul_abs (c : ℂ) : |c| * |c| = c.normSq := by
  rw [Complex.normSq_eq_abs, pow_two]
  simp


-- matrix type-cast helpers
section matrix_cast

universe u v
variable {α : Type*} [Semiring α]
variable {m n : Type u} [Fintype m] [Fintype n]
variable {m' n' : Type u} [Fintype m'] [Fintype n']

--Reconsideration

end matrix_cast

section matrix_cast_apply

variable {α : Type*}
variable {m n m' n' : Type}  [Fintype m'] [Fintype n']
variable (A : Matrix m n α) (B : Matrix m' n' α)
variable {a b a' b' : Nat}
variable (C : qMatrix a b) (D : qMatrix a' b')

lemma A_eq (m_eq : m = m') (n_eq : n = n') : Matrix m n α = Matrix m' n' α := by
  subst m_eq
  subst n_eq
  rfl

-- for easier pattern matching with matrix
lemma matrix_cast_apply (m_eq : m = m') (n_eq : n = n') (i' : m') (j' : n') :
    (cast (A_eq m_eq n_eq) A) i' j' = A (cast m_eq.symm i') (cast n_eq.symm j') := by
  subst m_eq
  subst n_eq
  rfl


end matrix_cast_apply


section matrix

variable {m n o : ℕ}
variable {A : qMatrix m n} {B : qMatrix n o}
variable {s : Vector n}

@[simp]
lemma Matrix_zero_neq_one {n : ℕ} : 0 ≠ (I (n+1)) := by
  intro h
  have c3 : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = (I (n+1)) 0 0 := by simp
      _ = (0 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) 0 0 := by rw [h]
      _ = 0 := by simp
  have c4 : (1 : ℝ) = 0 := by exact_mod_cast c3
  linarith

lemma Matrix_nonzero_has_nonzero_val : A ≠ 0 → ∃ i j, A i j ≠ 0 := by
  contrapose!
  intro h
  apply Matrix.ext
  intro i j
  exact h i j

lemma Vector_nonzero_has_nonzero_val : s ≠ 0 → ∃ i, s i 0 ≠ 0 := by
  contrapose!
  intro h
  apply Matrix.ext
  intro i j
  have : j = 0 := by
    cases j with | mk i hi =>
    apply Fin.ext
    simp
    simp at hi
    exact hi
  subst this
  apply h

-- Special case of 1 × 1 matrix.
lemma matrix_mul_cancel_left_square_one {n : ℕ} {x : Matrix (Fin n) (Fin 1) ℂ}
    {y z : Matrix (Fin 1) (Fin 1) ℂ} : x ⬝ y = x ⬝ z → x ≠ 0 → y = z := by
  intros h xn
  apply Matrix.ext
  intro i j
  rw [← Matrix.ext_iff] at h
  obtain ⟨k, kp⟩ := Vector_nonzero_has_nonzero_val xn
  specialize h k j
  iterate 2
    --repeat rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply] at h
    rw [Finset.sum_fin_eq_sum_range] at h
    rw [Finset.sum_range_one] at h
    rw [dif_pos (by simp)] at h
  have i0 : i = 0 := by
    cases j with | mk i hi =>
    apply Fin.ext
    simp
  have j0 : j = 0 := by
    cases i with | mk j hj =>
    apply Fin.ext
    simp
  subst i0
  subst j0
  simp at *
  cases h
  assumption
  exfalso
  apply kp
  assumption

-- Special case of 1 × 1 matrix.
lemma matrix_mul_square_one {x y : Matrix (Fin 1) (Fin 1) ℂ} {i j : Fin 1} :
    (x ⬝ y) i j = x i j * y i j := by

  have i0 : i = 0 := by
    cases j with | mk i hi =>
    apply Fin.ext
    simp
  have j0 : j = 0 := by
    cases i with | mk j hj =>
    apply Fin.ext
    simp
  subst i0
  subst j0
  simp [Matrix.mul_apply, Fin.sum_univ_succ]

-- Special case of 1 × 1 matrix.
lemma matrix_mul_comm_square_one {x y : Matrix (Fin 1) (Fin 1) ℂ} : x ⬝ y = y ⬝ x := by
  apply Matrix.ext
  intro i j
  iterate 2 rw [matrix_mul_square_one]
  ring

-- Special case of 1 × 1 matrix.
@[simp]
lemma id_one_apply {x y : Fin 1} : (I 1) x y = 1 := by
  have xp : x = 0 := by
    cases x with | mk x hx =>
    apply Fin.ext
    simp
    simp at hx
    exact hx
  have yp : y = 0 := by
    cases y with | mk y hy =>
    apply Fin.ext
    simp
    simp at hy
    exact hy
  subst xp
  subst yp
  simp

-- Slightly relaxed version of matrix.smul_apply for easier matching.
-- Note the scalar type is ℝ, not ℂ.
lemma Matrix.real_smul_apply {a : ℝ} {i : Fin m} {j : Fin n} :
    (a • A) i j = a * A i j := rfl

-- Slightly relaxed version of matrix.mul_smul for easier matching.
-- Note the scalar type is ℝ, not ℂ.
lemma Matrix.mul_real_smul {a : ℝ} : A ⬝ (a • B) = a • (A ⬝ B) := by
  simp

end matrix

-- adjoint lemmas


@[simp]
theorem adjoint_zero {m n}:
    (0 : qMatrix m n)† = 0 := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  simp

@[simp]
theorem adjoint_one {n}:
    (1 : qMatrix n n).adjoint = 1 := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  by_cases h : i = j
  rw [h]
  simp
  rw [Matrix.one_apply_ne h]
  have h' : j ≠ i := by cc
  rw [Matrix.one_apply_ne h']
  simp

section adjoint

variable {m n : ℕ}
variable (x y : qMatrix m n)

@[simp]
theorem adjoint_involutive : x†† = x := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  simp

theorem adjoint_inj :(x†) = (y†) → x = y := by
  intro h
  apply Matrix.ext
  intros i j
  rw [← Matrix.ext_iff] at h
  specialize h j i
  unfold qMatrix.adjoint at h
  simp at h
  exact (starRingEnd ℂ).injective h--worthy of study


lemma adjoint_add : ((x + y)†) = (x†) + (y†) := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  simp

lemma adjoint_sub : ((x - y)†) = (x†) - (y†) := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  simp

lemma adjoint_neg (x : qMatrix m n): (-x)† = -(x†) := by
  apply Matrix.ext
  intros i j
  simp
  unfold qMatrix.adjoint
  simp

lemma adjoint_smul (s : ℂ) : (s • x)† = (s†) • (x†) := by
  apply Matrix.ext
  intros i j
  unfold qMatrix.adjoint
  simp

lemma adjoint_apply (x : qMatrix m n) (i : Fin n) (j : Fin m) : (x†) i j = ((x j i)†) := by
  unfold qMatrix.adjoint
  rfl

end adjoint

-- Adjoint + mul lemmas
section adjoint_mul

variable {m n o : ℕ}
variable (A : qMatrix m n)
variable (B : qMatrix n o)


lemma conj_mul_eq_dot_product (i : Fin m) (j : Fin o) :
    ((A ⬝ B) i j)† = dotProduct (fun k => (B k j)†) (fun k => (A i k)†) := by
  unfold dotProduct
  simp [Matrix.mul_apply, star_sum, StarMul.star_mul]


theorem adjoint_mul : (A ⬝ B)† = (B†) ⬝ (A†) := by
  apply Matrix.ext
  intros j i
  simp_rw [adjoint_apply]
  rw [conj_mul_eq_dot_product]
  simp
  rfl

end adjoint_mul

section vector_adjoint

variable {n : ℕ} (s : Vector n)

lemma dot_adjoint_eq_sum_mul_conj :
    dotProduct (fun j => (s†) 0 j) (fun j => s j 0) = ∑ j, (s†) 0 j * s j 0 :=
  rfl


lemma dot_adjoint_eq_sum_square :
    dotProduct (fun j => (s†) 0 j) (fun j => s j 0) = ∑ j, ‖s j 0‖ ^ 2 := by
  rw [dot_adjoint_eq_sum_mul_conj]
  simp [Complex.abs]
  apply Finset.sum_congr rfl
  intro x _
  rw [adjoint_apply]
  rw [RCLike.star_def]
  rw [Complex.conj_mul']
  norm_cast
  rw [Complex.normSq_eq_abs]
  simp


example : (((s†) ⬝ s) 0 0) = ((∑ i, ‖s i 0‖ ^ 2) : ℂ) := by

  rw [Matrix.mul_apply]
  rw [← dotProduct]
  rw [dot_adjoint_eq_sum_square]
  norm_cast


@[simp]
lemma sum_square_one_if_mul_adjoint_one :
    ((s†) ⬝ s) = 1 → (∑ i, |s i 0| ^ 2) = 1 := by
  intro h
  rw [← Matrix.ext_iff] at h
  specialize h 0 0
  rw [Matrix.mul_apply] at h
  rw [← dotProduct] at h
  rw [dot_adjoint_eq_sum_square] at h
  simp at h
  norm_cast at h

lemma mul_adjoint_one_if_sum_square_one :
    (∑ i, |s i 0| ^ 2) = 1 → ((s†) ⬝ s) = 1 := by
  intro h
  apply Matrix.ext
  intros i j
  have i_eq : i = 0 := by
    cases i with | mk i hi =>
    apply Fin.ext
    simp
    simp at hi
    exact hi
  have j_eq : j = 0 := by
    cases j with | mk j hj =>
    apply Fin.ext
    simp
    simp at hj
    exact hj
  cases i_eq
  cases j_eq
  simp
  rw [Matrix.mul_apply]
  rw [← dotProduct]
  rw [dot_adjoint_eq_sum_square]
  norm_cast

end vector_adjoint

-- unit lemmas

lemma unfold_unit {n} {s : Vector n} (h : unit s) : s† ⬝ s = 1 := h

-- 单位向量非零性
lemma unit_nonzero {n : ℕ} {s : Vector n} (h : unit s) : s ≠ 0 := by
  intro h0
  have h1 : s† ⬝ s = (0 : Vector n)† ⬝ (0 : Vector n) := by rw [h0]
  simp only [Matrix.zero_mul, Matrix.mul_zero] at h1
  rw [h] at h1
  norm_num at h1


-- std_basis lemmas
section std_basis

variable {m : Type*} [DecidableEq m]

@[simp]
lemma std_basis_eq_zero {n : m} : ∀ {j i}, j ≠ n → std_basis n j i = 0 := by
  intros j i h
  rw [std_basis]
  exact if_neg h

@[simp]
lemma std_basis_eq_one {n : m} : ∀ {j i}, j = n → std_basis n j i = 1 :=
  by intros j i h; rw [h, std_basis]; simp

variable {n : ℕ} {i j : Fin n}

@[simp]
theorem std_basis_unit : unit (std_basis i) := by
  apply mul_adjoint_one_if_sum_square_one
  rw [Finset.sum_eq_single i]
  simp
  · intros b _ h
    rw [std_basis_eq_zero h]; simp
  · intro h
    exfalso; apply h; simp

@[simp]
lemma std_basis_adjoint_apply {s : Fin n} : ∀ x, ((std_basis s)†) x i = (std_basis s) i x := by
  intros x
  unfold qMatrix.adjoint
  unfold std_basis
  split_ifs
  simp
  simp


@[simp]
lemma std_basis_inner_product : ((std_basis i)†) ⬝ (std_basis i) = 1 := std_basis_unit

lemma std_basis_inner_product_eq_zero : i ≠ j → ((std_basis i)†) ⬝ (std_basis j) = 0 := by
  intro h; apply Matrix.ext
  intros v w

  rw [Matrix.mul_apply]
  --rw [← dotProduct]
  unfold qMatrix.adjoint
  have v0 : v = 0 := by
    cases v with | mk v hv =>
    apply Fin.ext
    simp
    simp at hv
    exact hv
  have w0 : w = 0 := by
    cases w with | mk w hw =>
    apply Fin.ext
    simp
    simp at hw
    exact hw
  rw [v0, w0]
  simp
  rw [Finset.sum_eq_single i]
  simp [std_basis_eq_zero h]
  simp
  intros b _
  unfold std_basis
  split_ifs
  left
  rfl
  simp
  rw [std_basis_eq_zero h]
  rw [mul_zero]
  simp


@[simp]
lemma inner_product_std_basis_cancel_left {s : Vector n} : ((std_basis i)† ⬝ s) 0 0 = s i 0 := by

  rw [Matrix.mul_apply]

  unfold adjoint std_basis
  rw [Finset.sum_eq_single i]
  simp;
  intros b _ h
  simp [std_basis]
  intro
  tauto
  intro h
  exfalso
  simp at i h

@[simp]
lemma adjoint_inner_product_std_basis_cancel_left {s : Vector n} :
    qMatrix.adjoint ((std_basis i)† ⬝ s) 0 0 = (s i 0)† := by--fail to use double†
  unfold adjoint std_basis
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  simp
  intros b _ h
  simp [std_basis]
  intro
  tauto
  intro h
  exfalso
  simp at i h

end std_basis


section matrix_std_basis

variable {m n : Type*}
variable [DecidableEq m] [DecidableEq n]
variable {α : Type*} [Semiring α]

@[simp]
lemma std_basis_matrix_eq_given {i' : m} {j' : n} {v : α} :
    ∀ {i j}, i = i' ∧ j = j' → Matrix.stdBasisMatrix i' j' v i j = v := by
  intro i j h
  cases h with
  | intro h1 h2 =>
    rw [h1, h2]
    unfold Matrix.stdBasisMatrix
    simp

lemma std_basis_matrix_eq_zero {i' : m} {j' : n} {v : α} :
    ∀ {i j}, ¬(i = i') ∨ ¬(j = j') → Matrix.stdBasisMatrix i' j' v i j = 0 := by
  intro i j h
  unfold Matrix.stdBasisMatrix
  simp only [Matrix.of_apply]
  split_ifs with h'
  exfalso
  cases h with
  | inl h =>
    cases h' with | intro h_eq_i h_eq_j =>
    symm at h_eq_i
    exact h h_eq_i
  | inr h =>
    cases h' with | intro h_eq_i h_eq_j =>
    symm at h_eq_j
    exact h h_eq_j
  rfl



lemma std_basis_eq_std_basis_matrix {n : m} :
    std_basis n = Matrix.stdBasisMatrix n 0 1 := by
  apply Matrix.ext
  intro i j
  have jp : j = 0 := by
    cases j with
    | mk j_val jp =>
    apply Fin.ext
    simp
    simp at jp
    exact jp
  cases jp
  by_cases h : i = n
  · rw [h]
    simp
  rw [std_basis_eq_zero h]
  rw [std_basis_matrix_eq_zero]
  simp
  exact h


end matrix_std_basis


-- state vector decomposition into standard basis vectors
theorem Vector_decomposition {n} (s : Vector n) :
    s = ∑ k, s k 0 • std_basis k := by
  apply Matrix.ext
  intro i j
  cases j with
  | mk j_val jp =>
    have jeq : j_val = 0 := by
      simp at jp
      exact jp
    cases jeq
    simp
    --unfold std_basis
    have hh : (∑ k : Fin n, s k 0 • std_basis k) i 0 = ∑ k : Fin n,((s k 0 • std_basis k) i 0) := by
      rw [Matrix.sum_apply]
    rw[hh]--if dont use sum_apply,target will turn to ⊢ s b 0 • std_basis b = 0
    simp
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ h
      simp
      right
      symm at h
      exact std_basis_eq_zero h
    · intro c
      exfalso
      apply c
      simp


-- kron_loc lemmas, terrible
section kron_loc

variable {n m : ℕ}

@[simp]
lemma kron_loc_composition (x : Fin (n * m)) : kronLoc (kronDiv x) (kronMod x) = x := by
  unfold kronDiv kronMod kronLoc
  cases x with
  | mk x xp =>
    simp
    have f1 : 0 < m := by
      cases m with
      | zero =>
        exfalso
        simp at xp
      | succ _ => simp
    rw[Nat.div_add_mod]

@[simp]
lemma kron_div_kron_loc {k : Fin n} {j : Fin m} : kronDiv (kronLoc k j) = k := by
  unfold kronDiv kronLoc
  simp
  cases k with
  | mk k kp =>
    cases j with
    | mk j jp =>
      simp
      have hh : m * k + j= j + m * k := by ring
      rw [hh]
      rw [Nat.add_mul_div_left j k]
      rw [Nat.div_eq_of_lt]
      simp
      exact jp
      exact Nat.lt_of_le_of_lt (Nat.zero_le j) jp

@[simp]
lemma kron_mod_kron_loc {k : Fin n} {j : Fin m} :
  kronMod (kronLoc k j) = j := by
  unfold kronMod kronLoc
  simp
  cases k with
  | mk k kp =>
    cases j with
    | mk j jp =>
      simp
      exact Nat.mod_eq_of_lt jp

lemma kron_loc_inj (a b : Fin n) (c d : Fin m) : kronLoc a c = kronLoc b d → a = b ∧ c = d := by
  intro h
  cases a with
  | mk a ap =>
    cases b with
    | mk b bp =>
      cases c with
      | mk c cp =>
        cases d with
        | mk d dp =>
          simp
          unfold kronLoc at h
          simp at h
          apply add_mul_congr
          repeat assumption

lemma kron_loc_inj_iff (a b : Fin n) (c d : Fin m) : kronLoc a c = kronLoc b d ↔ a = b ∧ c = d := by
  constructor
  · apply kron_loc_inj
  · intro h
    rcases h with ⟨h1, h2⟩
    cases h1
    cases h2
    rfl

end kron_loc


section kron

variable {m n p q : ℕ}
variable (A : qMatrix m n) (B : qMatrix p q)

theorem adjoint_kron :
  (A ⊗ B)† = (A†) ⊗ (B†):= by
  unfold adjoint kron
  simp


theorem mul_to_kron (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q)  :
   A r s * B v w = (A ⊗ B) (kronLoc r v) (kronLoc s w) := by
  unfold kron
  simp

theorem kron_ext_mul (M : qMatrix (m*p) (n*q)) :
    (∀ (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q)
           , A r s * B v w = M (kronLoc r v) (kronLoc s w))
          → (A ⊗ B) = M := by
  intro h
  ext i j
  unfold kron
  rw [h]
  unfold kronLoc kronDiv kronMod
  simp
  congr
  · cases i with | mk i hi =>
    simp
    rw [add_comm, Nat.mod_add_div]
  · cases j with | mk j hj =>
    simp
    rw [add_comm, Nat.mod_add_div]


theorem kron_ext_mul_iff {M : qMatrix (m*p) (n*q)} :
    (A ⊗ B)  = M ↔
      ∀ (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q),
        A r s * B v w = M (kronLoc r v) (kronLoc s w) := by
  constructor
  · intro h r s v w
    rw [← h]
    apply mul_to_kron
  · apply kron_ext_mul

@[simp]
lemma kron_zero_left {p q m n} {x : qMatrix m n} : ((0 : qMatrix p q) ⊗ x) = 0 := by
  rw [kron_ext_mul]
  simp
  --kron_ext_mul _ _ (by simp)

@[simp]
lemma kron_zero_right {p q m n} {x : qMatrix m n} : (x ⊗ (0 : qMatrix p q)) = 0 := by
  rw [kron_ext_mul]
  simp

theorem kron_id : (I m) ⊗ (I n)= I (m * n) := by
  apply kron_ext_mul
  intro r s v w
  by_cases h1 : r = s
  · rw [h1]
    by_cases h2 : v = w
    · rw [h2]
      simp
    · have f1 : (I n) v w = 0 := if_neg h2
      rw [f1]
      simp
      have f2 : (kronLoc r v) ≠ (kronLoc r w) := by
        simp
        intro h
        apply h2
        exact Fin.eq_of_val_eq h
      rw[← h1]
      simp[f2]
  · have f1 : (I m) r s = 0 := if_neg h1
    rw [f1]
    simp
    have f2 : (kronLoc r v) ≠ (kronLoc s w) := by
      unfold kronLoc
      intro h
      apply h1
      simp at h
      cases v with |mk v hv=>
      cases w with |mk w hw=>
      simp at h
      cases add_mul_congr h hv hw with |intro h1 h2=>
      rw[Fin.val_eq_val]at h1
      exact h1
      /-have hh :  n * r = n * s + w - v:= by
        rw [← h]
        simp
      have hh2 : n * r - n * s= w - v:= by
        rw[hh]
        set t := n * s
        rw[tsub_tsub]
        rw[add_comm]
        nth_rewrite 2[add_comm]
        rw[← tsub_tsub]
        simp
      have hh3 : n * (r-s) = w - v :=by
        rw[mul_tsub]
        exact hh2
      have h_rs_ne_zero_z : (r:ℤ) - s ≠ 0 := by
        intro h_eq
        apply h1
        rw[sub_eq_zero] at h_eq
        norm_cast at h_eq
        rw[Fin.val_eq_val]at h_eq
        exact h_eq
      rw[sub_ne_zero] at h_rs_ne_zero_z
      norm_cast at h_rs_ne_zero_z
      rw[← ne_eq] at h_rs_ne_zero_z
      --rw[Nat.neeq]
      have h_n_times_nonzero : n * (r - s) ≠ 0 := by
        apply Nat.mul_ne_zero
        · exact hn.ne'
        · intro h_eq
          apply h_rs_ne_zero_z
          rw [sub_eq_zero] at h_eq-/
--terrible and useless
--nat sub won't less than 0, so n * (r-s) = w - v will become n * 0 if r le s and seems fail to continue prove
    simp[f2]

theorem kron_dist_over_add_right (C : qMatrix p q): (A ⊗ (B + C))  = (A ⊗ B) + (A ⊗ C)  := by
  ext i j
  simp [kron]
  ring

theorem kron_dist_over_add_left (C : qMatrix p q): (B + C) ⊗ A  = (B ⊗ A) + (C ⊗ A)  := by
  ext i j
  simp [kron]
  ring

lemma kron_dist_over_sub_right (C : qMatrix p q): A ⊗ (B - C) = (A ⊗ B) - (A ⊗ C) := by
  ext i j
  simp [kron]
  ring

lemma kron_dist_over_sub_left (C : qMatrix p q): (B - C) ⊗ A = (B ⊗ A) - (C ⊗ A) := by
  ext i j
  simp [kron]
  ring

@[simp]
lemma kron_smul_right {s : ℂ}: A ⊗ (s • B) = s • (A ⊗ B) := by
  ext i j
  simp [kron]
  ring

@[simp]
lemma kron_smul_left  {s : ℂ}: (s • A) ⊗ B = s • (A ⊗ B) := by
  ext i j
  simp [kron]
  ring

--set_option pp.proofs true

-- lemma eq_Fin_m : Fin m = Fin (1 * m) :=by
--   simp

-- lemma eq_Fin_n (n: ℕ) : Fin (1 * n) = Fin n :=by
--   simp

-- lemma eq_qMatrix_n_m (n: ℕ)(m: ℕ) : qMatrix m n = qMatrix (1 * m) (1 * n) :=by
--   simp

-- example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
--   have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
--     Nat.mul_add (x + y) x y
--   have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
--     (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
--   h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- lemma eq:m=1*m:=by
--   simp

-- lemma eq2:n=1*n:=by
--   simp


@[simp] lemma kron_id_left :
    (I 1) ⊗ A = cast (by simp) A := by
    funext i j
    unfold kron kronDiv kronMod
    cases i  with | mk i ip=>
    cases j  with | mk j jp=>
      simp
      rw[matrix_cast_apply]
      case h.h.mk.mk.m_eq=>
        simp
      case h.h.mk.mk.n_eq=>
        simp
      rw[Fin.cast_eq_cast']--finally!
      rw[Fin.cast_eq_cast']
      congr
      have ip': i < m :=by
        rw[one_mul]at ip
        exact ip
      rw[Nat.mod_eq_of_lt ip']
      have jp': j < n :=by
        rw[one_mul]at jp
        exact jp
      rw[Nat.mod_eq_of_lt jp']



@[simp] lemma kron_id_right :
    A ⊗ (I 1) = cast (by simp) A := by
  funext i j
  simp [kron, kronDiv, kronMod]
  cases i with|mk i ip=>
  cases j with|mk j jp=>
    simp
    rw [matrix_cast_apply]
    case h.h.mk.mk.m_eq=>
      simp
    case h.h.mk.mk.n_eq=>
      simp
    rw[Fin.cast_eq_cast']
    rw[Fin.cast_eq_cast']
    congr

@[simp] lemma kron_one_one : (I 1) ⊗ (I 1) = I 1 := by
  rw [kron_id_right]
  rfl

@[simp] lemma kron_id_left_square_one (M : Square 1) : (I 1) ⊗ M = M := by
  ext i j
  simp [kron, kronDiv, kronMod]
  have i0 : i = 0 := by
    apply Fin.eq_of_val_eq
    simp
  have j0 : j = 0 := by
    apply Fin.eq_of_val_eq
    simp
  rw[i0,j0]

@[simp] lemma kron_id_right_square_one (M : Square 1) : M ⊗ (I 1) = M := by
  ext i j
  simp [kron, kronDiv, kronMod]
  have i0 : i = 0 := by
    apply Fin.eq_of_val_eq
    simp
  have j0 : j = 0 := by
    apply Fin.eq_of_val_eq
    simp
  rw[i0,j0]

lemma kron_square_one_eq_mul {x y : Square 1} : x ⊗ y = x ⬝ y := by
  ext i j
  have i0 : i = 0 := by
    cases i with | mk i ip=>
    apply Fin.eq_of_val_eq
    simp
    simp at ip
    exact ip
  have j0 : j = 0 := by
    cases j with | mk j jp=>
    apply Fin.eq_of_val_eq
    simp
    simp at jp
    exact jp
  subst i0 j0
  simp [kron, kronDiv, kronMod]
  rw [Matrix.mul_apply]
  simp

set_option pp.proofs true




lemma kron_cancel_left {m n : ℕ} {x : qMatrix m n} {y z : Square 1} :
    x ⊗ y = x ⊗ z → x ≠ 0 → y = z := by
  intros h xn
  ext i j
  rw [← Matrix.ext_iff] at h
  obtain ⟨r, s, h1⟩ := Matrix_nonzero_has_nonzero_val xn
  have hh : r < m * 1:=by
    rw[mul_one]
    apply Fin.is_lt
  have hh2 : s < n * 1:=by
    rw[mul_one]
    apply Fin.is_lt
  specialize h ⟨r, hh⟩ ⟨s, hh2⟩
  --apply Fin.cast (1*m = m) Fin(m)
  --unfold Fin.mk at h

  simp [kron] at h
  cases h with
  | inl h =>

  · have i0 : i = 0 := by
      cases i with | mk i ip=>
      apply Fin.eq_of_val_eq
      simp
      simp at ip
      exact ip
    have j0 : j = 0 := by
      cases j with | mk j jp=>
      apply Fin.eq_of_val_eq
      simp
      simp at jp
      exact jp
    subst i0 j0
    have hp : kronMod ⟨↑r, hh⟩ =0:=by
      unfold kronMod
      simp
      have h1 : (r :ℕ ) % 1 = 0 := by
        rw[Nat.mod_one]
      congr

    have hs : kronMod ⟨↑s, hh2⟩ =0:= by
      unfold kronMod
      simp
      have h2 : (s :ℕ ) % 1 = 0 := by
        rw[Nat.mod_one]
      congr
    rw[hp,hs] at h
    assumption
  | inr h =>
  · exfalso
    have hm1 : kronDiv ⟨↑r, hh⟩ = r := by
      unfold kronDiv
      simp
    have hm2 : kronDiv ⟨↑s, hh2⟩ = s := by
      unfold kronDiv
      simp
    rw[hm1,hm2] at h
    exact h1 h

lemma kron_diagonal {n m : ℕ} {A : Fin n → ℂ} {B : Fin m → ℂ} :
    (diagonal A) ⊗ (diagonal B) =
    diagonal (fun i => A (kronDiv i) * B (kronMod i)) :=by
  apply kron_ext_mul
  intros r s v w
  by_cases h1 : r = s
  · subst h1
    by_cases h2 : v = w
    · subst h2
      simp
    · have : (kronLoc r v) ≠ (kronLoc r w) := by
          intro c
          rw [kron_loc_inj_iff] at c
          cc
      nth_rw 2[diagonal_apply_ne]
      rw[mul_zero]
      simp only [diagonal, dite_eq_ite, ite_eq_left_iff]
      simp only [Matrix.of_apply]
      rw [if_neg]
      simp[this]
      rw[ne_eq]
      exact h2
  · have : (kronLoc r v) ≠ (kronLoc s w) := by
        intro c
        rw [kron_loc_inj_iff] at c
        cc
    nth_rw 1[diagonal_apply_ne]
    rw[zero_mul]
    simp only [diagonal, dite_eq_ite, ite_eq_left_iff]
    simp only [Matrix.of_apply]
    rw [if_neg]
    simp[this]
    rw[ne_eq]
    exact h1

end kron


-- theorem kron_std_basis

-- Kronecker product of two standard basis vector is another standard basis vector.

theorem kron_std_basis {n m : ℕ} (i : Fin n) (j : Fin m) :
    kron (std_basis i) (std_basis j) =
    std_basis ⟨m * (i : ℕ) + (j : ℕ), fin_add_mul_lt i j⟩ := by
  apply kron_ext_mul
  intros r s v w
  unfold kronLoc
  by_cases h1 : r = i
  · rw [h1]
    simp
    by_cases h2 : v = j
    · rw [h2]
      simp
    · rw [std_basis_eq_zero h2, std_basis_eq_zero]
      simp
      intro c
      apply h2
      rw[Fin.val_eq_val] at c
      exact c
  · rw [std_basis_eq_zero h1]
    simp
    rw [std_basis_eq_zero]
    simp
    intro c
    obtain ⟨f1, f2⟩ := add_mul_congr c v.prop j.prop
    apply h1
    rw[Fin.val_eq_val] at f1
    exact f1



-- kron assoc
section KronAssoc

variable {m n p q r s: ℕ} (a : qMatrix m n) (b : qMatrix p q) (c : qMatrix r s)

lemma kron_assoc_cast : qMatrix ((m * p) * r) ((n * q) * s) = qMatrix (m * (p * r)) (n * (q * s)) := by
  ring_nf

theorem kron_assoc : a ⊗ (b ⊗ c) = cast kron_assoc_cast ((a ⊗ b) ⊗ c) := by
  apply Matrix.ext
  intros i j
  unfold kron
  cases i with | mk i ip =>
  cases j with | mk j jp =>
  unfold kronDiv kronMod
  --simp
  rw [matrix_cast_apply]
  case a.mk.mk.m_eq =>
    rw[mul_assoc]
  case a.mk.mk.n_eq =>
    rw[mul_assoc]
  rw[← mul_assoc]
  rw[Fin.cast_eq_cast']
  rw[Fin.cast_eq_cast']
  simp
  left
  congr 3
  rw[Nat.div_div_eq_div_mul]
  ring_nf
  rw[Nat.div_div_eq_div_mul]
  ring_nf
  rw[Nat.mod_mul_left_div_self]
  rw[Nat.mod_mul_left_div_self]



lemma kron_assoc_l2r : (a ⊗ b) ⊗ c = cast kron_assoc_cast.symm (a ⊗ (b ⊗ c)) := by
  rw [kron_assoc, cast_cast]
  simp

end KronAssoc

-- kron_mixed_prod
section KronSumMulMul

variable {α : Type} [CommSemiring α]
variable {n m : ℕ}
variable (f : Fin n → α)
variable (g : Fin m → α)

def kron_to_prod (i : Fin (n * m)) : Fin n × Fin m := ⟨kronDiv i, kronMod i⟩

lemma kron_to_prod_inj (i j : Fin (n * m)) : kron_to_prod i = kron_to_prod j → i = j := by
  have hm : 0 < m := by
    apply Nat.pos_of_mul_pos_left
    exact Fin.pos i
  cases i with |mk i hi=>
  cases j with |mk j hj=>
  simp only [kron_to_prod, kronDiv, kronMod]
  intro h1
  simp at h1
  congr
  obtain ⟨hdiv, hmod⟩ := h1
  rw [← Nat.mod_add_div i m]
  rw [← Nat.mod_add_div j m]
  rw [hdiv, hmod]


lemma kron_sum_mul_mul : (∑ x, f x) * (∑ x, g x) = ∑ (x : Fin (n * m)), f (kronDiv x) * g (kronMod x) := by
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']--important
  rw[← Finset.sum_preimage (λ x : Fin (n*m)=> (⟨kronDiv x, kronMod x⟩ : Fin n × Fin m))]
  congr
  ext
  simp
  simp
  unfold Set.InjOn
  simp
  intro x y
  intro h1 h2
  apply Fin.ext
  have hh : x=x/m*m+x%m:=by
    rw[Nat.div_add_mod']
  have hh2: y=y/m*m+y%m:=by
    rw[Nat.div_add_mod']
  rw[hh,hh2,h1,h2]
  simp
  intro x y z
  exfalso

  let i : Fin (n * m) := ⟨x.val * m + y.val, by
    have hx := x.isLt
    have hy := y.isLt

    have h3:x*m≤(n-1)*m:=by
      have h4:x≤(n-1):=by
        exact Nat.le_pred_of_lt hx
      rw[mul_le_mul_right]
      exact h4
      exact Fin.pos y
    have h5 : ↑x * m + ↑y < ↑x * m + m := Nat.add_lt_add_left hy (↑x * m)
    have h6 : ↑x * m + m ≤ (n - 1) * m + m := Nat.add_le_add_right h3 m
    have h7 : (n - 1) * m + m = n * m := by
      rw[Nat.sub_mul]
      rw[one_mul]
      rw[Nat.sub_add_cancel]
      nth_rw 1[← one_mul m]
      apply Nat.mul_le_mul_right m
      exact Fin.pos x
    exact Nat.lt_of_lt_of_le h5 (h7 ▸ h6)
  ⟩
  apply z i
  apply Fin.ext
  simp [kronDiv]
  rw[Fin.val_mk]
  rw[Nat.add_div]
  simp
  have hm : 0 < m := Fin.pos y
  have h1 : ↑x * m / m = ↑x := by
    apply Nat.mul_div_cancel
    exact hm
  have h2 : ↑y / m = 0 := by
    rw[Nat.div_eq_zero_iff]
    right
    apply Fin.is_lt
  have h3:(if m ≤ ↑y % m then (1 : Nat) else 0)=0:=by
    simp
    rw[Nat.mod_eq]
    simp
    have h4:¬ m ≤ ↑y:=by
      simp
    simp[h4]
  rw[h1,h2,h3]
  ring_nf
  exact Fin.pos y
  apply Fin.ext
  simp [kronDiv]
  rw[Fin.val_mk]
  rw[Nat.add_mod]
  simp
  rw[Nat.mod_eq]
  simp

  --have bij : Fin (n * m) ≃ Fin n × Fin m := by no need anymore

--(λ x : fin (n*m)=> (⟨kron_div x, kron_mod x⟩ : fin n × fin m))
end KronSumMulMul

section kron_mixed_prod


variable {n m o : ℕ} (a : qMatrix m n) (c : qMatrix n o)
variable {q r s : ℕ} (b : qMatrix q r) (d : qMatrix r s)

theorem kron_mixed_prod : (a ⊗ b) ⬝ (c ⊗ d) = (a ⬝ c) ⊗ (b ⬝ d) := by
  ext i j
  unfold  kron
  simp[Matrix.mul_apply]
  rw [kron_sum_mul_mul]
  congr
  funext x
  ring

lemma kron_mixed_prod_I_left : ((I q) ⊗ a) ⬝ (b ⊗ c) = b ⊗ (a ⬝ c) := by
  have : b ⊗ (a ⬝ c) = ((I q) ⬝ b) ⊗ (a ⬝ c) := by simp
  rw [this]
  rw [kron_mixed_prod]

lemma kron_mixed_prod_I_right : (b ⊗ a) ⬝ ((I r) ⊗ c) = b ⊗ (a ⬝ c) := by
  have : b ⊗ (a ⬝ c) = (b ⬝ (I r)) ⊗ (a ⬝ c) := by simp
  rw [this]
  rw [kron_mixed_prod]

end kron_mixed_prod

-- kron + unit lemmas

section unit_kron


variable {n : ℕ} {s : Vector n}
variable {m : ℕ} {t : Vector m}

lemma unit_kron_of_unit : unit s → unit t → unit (s ⊗ t) := by
  unfold unit
  intro su tu
  rw [adjoint_kron, kron_mixed_prod, su, tu]
  simp

lemma unit_kron_right : unit (s ⊗ t) → unit s → unit t := by
  unfold unit
  intro h su
  rw [adjoint_kron, kron_mixed_prod, su, kron_id_left] at h
  exact h

lemma unit_kron_left : unit (s ⊗ t) → unit t → unit s := by
  unfold unit
  intro h tu
  rw [adjoint_kron, kron_mixed_prod, tu, kron_id_right] at h
  exact h

end unit_kron



-- Unitary lemmas

section unitary

open Matrix

variable {n : ℕ} (U : qMatrix n n)

lemma unfold_unitary {U : qMatrix n n} : U.unitary → U.adjoint ⬝ U = 1 := by tauto

-- Compatibility with `isUnit U.det`.
lemma unitary_is_unit_det : U.unitary → IsUnit U.det := by
  --unfold adjoint
  intro h1
  apply unfold_unitary at h1
  set sh :  Matrix (Fin n) (Fin n) ℂ :=U.adjoint
  apply Matrix.isUnit_det_of_left_inverse
  case B=>
    use sh
  exact h1

-- Compatibility with `IsUnit U`.
lemma unitary_is_unit : U.unitary → IsUnit U := by
  intro h
  rw [Matrix.isUnit_iff_isUnit_det]
  apply unitary_is_unit_det
  assumption

-- Unitary matrix has a right inverse.
lemma unitary_mul_inv_right : U.unitary → U ⬝ U⁻¹ = 1 := by
  intro h
  apply unitary_is_unit_det at h
  rw [Matrix.mul_nonsing_inv]
  exact h

-- Unitary matrix has a left inverse.
lemma unitary_mul_inv_left : U.unitary → U⁻¹ ⬝ U = 1 := by
  intro h
  rw [Matrix.nonsing_inv_mul]
  apply unitary_is_unit_det
  assumption

-- U† is the inverse.
lemma unitary_inv_eq_adjoint : U.unitary → U⁻¹ = U.adjoint := by
  intro h
  have f1 : U.adjoint ⬝ U ⬝ (U⁻¹) = (U⁻¹) := by
    unfold qMatrix.unitary at h
    rw [h]
    simp
  rw [← f1]
  rw [Matrix.mul_assoc]
  have h1 : U * U⁻¹=1:=by
    apply unitary_mul_inv_right at h
    exact h
  rw [h1]
  rw[mul_one]

-- Unitary property `U† ⬝ U = 1` can be stated the other way around.
theorem unitary_comm : U.unitary ↔ U ⬝ U.adjoint = 1 := by
  constructor
  · intro h
    have h2: qMatrix.unitary U:=h
    apply unitary_inv_eq_adjoint at h
    rw [← h]
    apply unitary_mul_inv_right
    assumption
  · intro h
    unfold qMatrix.unitary
    simp [Matrix.mul_apply] at h ⊢
    rw[Matrix.mul_eq_one_comm]
    exact h

-- Unitary matrix is also normal.
-- (But, not all normal matrices are unitary.)
theorem unitary_normal : U.unitary → U.normal := by
  unfold qMatrix.normal
  unfold qMatrix.unitary
  intro h
  rw [h]
  symm
  rw [← unitary_comm]
  assumption

end unitary


section unitary_and_vector

variable {n : ℕ} (U : qMatrix n n)
variable (v : Vector n) (w : Vector n)

-- Unitary operator is norm-preserving.
-- The angle between two quantum states preserves under any unitary operations
theorem unitary_preserve_norm : U.adjoint ⬝ U = 1 → ((U ⬝ v)†) ⬝ (U ⬝ w) = (v†) ⬝ w := by
    intro up
    rw [adjoint_mul]
    rw [← Matrix.mul_assoc]
    nth_rw 2[Matrix.mul_assoc]
    rw [up]
    rw[Matrix.mul_one]


-- Unitary matrix presevese the validity of quantum state.
example : U.adjoint ⬝ U = 1 → (v†) ⬝ v = 1 → ((U ⬝ v)†) ⬝ (U ⬝ v) = 1:= by
    intro up pp
    rw [unitary_preserve_norm]
    assumption
    assumption

example : U.unitary → ((U ⬝ v)†) ⬝ (U ⬝ w) = (v†) ⬝ w:= by
    intro h
    apply unitary_preserve_norm
    assumption

example : U.unitary → (w†) ⬝ w = 1 → ((U ⬝ w)†) ⬝ (U ⬝ w) = 1:= by
    intros h wu
    rw [unitary_preserve_norm]
    assumption
    unfold qMatrix.unitary at h
    exact h

end unitary_and_vector


-- Matrix.inner_product & Matrix.norm & Matrix.dist

namespace qMatrix

variable {n : ℕ}

noncomputable
def inner_product (x y : Vector n) : ℂ :=
  (x† ⬝ y) 0 0

noncomputable
instance {n : ℕ} : Inner ℂ (Vector n) := ⟨inner_product⟩

noncomputable
def norm (x : Vector  n) : ℝ :=
  Real.sqrt (RCLike.re (inner_product x x))

noncomputable
instance {n : ℕ} : Norm (Vector n) := ⟨norm⟩

/-- Distance between two vectors -/
noncomputable
def dist (x y : Vector n) : ℝ :=
  norm (x - y)

noncomputable
instance {n : ℕ} : Dist (Vector n) := ⟨qMatrix.dist⟩

end qMatrix

notation "⟪" X "," Y "⟫" =>  @Inner.inner ℂ _ _ X Y

-- Matrix inner product operator is compatible with matrix.inner_product.
-- So are norm and dist.

section inner_product_compat

variable {n : ℕ} (s t : Vector n)

lemma norm_eq_norm : s.norm = ‖s‖ :=by
  unfold qMatrix.norm Norm.norm
  norm_cast


lemma qMatrix_inner_eq_Matrix_inner : ⟪s,t⟫ = ⟪ fun i=> s i 0, fun i=> t i 0 ⟫:= by
    unfold inner instInnerComplexOfNatNat instInnerForall_myyt
    simp
    unfold qMatrix.inner_product Matrix.inner_product «conj» adjoint
    simp[dotProduct]
    congr



lemma Matrix_norm_eq_matrix_norm : ‖s‖ = ‖ (fun i=> s i 0)‖:= by
    unfold Norm.norm instNormOfNatNat instNormForall_myyt
    simp
    unfold qMatrix.norm
    congr


lemma Matrix_dist_eq_matrix_dist : qMatrix.dist s t = Matrix.dist (fun i=> s i 0) (fun i=> t i 0) := by
    unfold Matrix.dist qMatrix.dist
    rw[norm_eq_norm]
    rw[Matrix_norm_eq_matrix_norm]
    norm_cast

end inner_product_compat


-- Vector normed_group

section NormedGroup

variable {m : ℕ}

noncomputable
instance : MetricSpace (Vector m) := {
dist               := qMatrix.dist
dist_self          := by

        intros x
        unfold Dist.dist
        simp
        rw [Matrix_dist_eq_matrix_dist]
        unfold Matrix.dist
        simp

eq_of_dist_eq_zero := by
        intros x y
        unfold Dist.dist
        simp
        rw [Matrix_dist_eq_matrix_dist]
        intros h
        have : (λ (i : Fin m)=> x i 0) = (λ (i : Fin m)=> y i 0):= by
          apply eq_of_dist_eq_zero h
        apply Matrix.ext
        intros i j
        have j0 : j = 0 := by
          cases j with | mk j jp=>
          apply Fin.eq_of_val_eq
          simp
          simp at jp
          exact jp
        cases j0
        change (λ (i : Fin m)=> x i 0) i = (λ (i : Fin m)=> y i 0) i
        cc

dist_comm          := by
        intros x y
        unfold Dist.dist
        simp
        rw [Matrix_dist_eq_matrix_dist]
        rw [Matrix_dist_eq_matrix_dist]
        rw [Matrix.dist_comm]


dist_triangle      := by
        intros x y z
        unfold Dist.dist
        simp
        repeat rw [Matrix_dist_eq_matrix_dist]
        apply Matrix.dist_triangle

}

lemma qMatrix.dist_eq (x y : Vector m) : dist x y = ‖x - y‖ := by rfl

noncomputable
instance : SeminormedAddCommGroup (Vector m) := ⟨ qMatrix.dist_eq ⟩--not completely norm

end NormedGroup

-- Vector inner_product_space

section inner_product_space

variable {m : ℕ}

lemma qMatrix_smul_apply (a : ℂ) (s : Vector m)
        : (λ i=> (a • s) i 0) = a • (λ i=> s i 0):= by
    apply funext
    intros i
    apply smul_apply


noncomputable
instance : NormedSpace ℂ (Vector m) := {
norm_smul_le :=by
        intros a1 b1
        have h1: ‖a1 • b1‖ = ‖a1 • fun i => b1 i 0‖:=by
          rw[Matrix_norm_eq_matrix_norm]
          rw [qMatrix_smul_apply]
        rw[h1]
        rw[Matrix_norm_eq_matrix_norm]
        unfold Norm.norm
        unfold instNormForall_myyt
        unfold NormedField.toNorm
        simp
        unfold Complex.instNormedField
        simp
        unfold Complex.instNorm
        simp
        rw[Matrix.norm_smul]
        have h2: ‖a1‖ = Complex.abs a1:=by
          simp
        rw[h2]
}

noncomputable
instance : InnerProductSpace ℂ (Vector m) := {
norm_sq_eq_inner :=by
        intros x
        rw [qMatrix_inner_eq_Matrix_inner]
        rw [Matrix_norm_eq_matrix_norm]
        apply has_norm_sq_eq_re_inner_product_self

conj_symm :=by
        intros x y
        repeat rw [qMatrix_inner_eq_Matrix_inner]
        unfold inner instInnerForall_myyt
        simp
        rw[← conj_inner_product]
        rw[RCLike.star_def]
        simp

add_left :=by
        intros x y z
        repeat rw [qMatrix_inner_eq_Matrix_inner]
        unfold inner
        apply inner_product_add_left

smul_left :=by
        intros x y r
        repeat rw [qMatrix_inner_eq_Matrix_inner]
        unfold inner
        apply inner_product_smul_l

}

end inner_product_space

-- Matrix inner product lemmas

section inner_product_lemmas

variable {n : ℕ}
variable {x y z : Vector n}

lemma norm_eq_one_of_unit : unit x → x.norm = 1 := by
  unfold unit
  intro h
  unfold qMatrix.norm
  simp
  unfold qMatrix.inner_product
  have hh :  x† * x = (x† ⬝ x):=by
    simp
  rw[← hh]
  rw [h]
  simp


lemma inner_product_bound_of_unit (xu : unit x) (yu : unit y) : |⟪x, y⟫| ≤ 1 := by
  have f1 : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := by
    rw [qMatrix_inner_eq_Matrix_inner]
    repeat rw [Matrix_norm_eq_matrix_norm]
    apply cauchy_schwarz_inequality_alt
  apply norm_eq_one_of_unit at xu
  apply norm_eq_one_of_unit at yu
  have f2 : ‖x‖ * ‖y‖ = x.norm * y.norm:=by
    simp[norm_eq_norm]
  rw[xu,yu] at f2
  rw[f2] at f1
  rw[one_mul] at f1
  exact f1


lemma inner_product_zero_iff : x† ⬝ y = 0 ↔ ⟪x, y⟫ = 0 := by
  unfold  inner instInnerComplexOfNatNat qMatrix.inner_product
  simp
  constructor
  · intro h; rw [h]; simp
  · intro h; apply Matrix.ext; intro i j
    have i0 : i = 0 := by
      cases i with | mk i ip=>
      apply Fin.eq_of_val_eq
      simp
      simp at ip
      exact ip
    have j0 : j = 0 := by
      cases j with | mk j jp=>
      apply Fin.eq_of_val_eq
      simp
      simp at jp
      exact jp
    simp at *
    rw[i0,j0]
    exact h

lemma Matrix_inner_self_eq_norm_sq : (⟪x, x⟫).re = ‖x‖ ^ 2 := by
  rw [qMatrix_inner_eq_Matrix_inner]
  rw [Matrix_norm_eq_matrix_norm]
  unfold inner instInnerForall_myyt
  simp
  rw [has_norm_sq_eq_re_inner_product_self]
  norm_cast

lemma Matrix_inner_self_im_zero : (⟪x, x⟫).im = 0 := by
  rw [qMatrix_inner_eq_Matrix_inner]
  unfold inner instInnerForall_myyt
  simp
  have h2 :(Matrix.inner_product (fun i => x i 0) fun i => x i 0).im = RCLike.im (Matrix.inner_product (fun i => x i 0) fun i => x i 0):=by
    norm_cast
  rw[h2]
  rw[inner_product_self_im_zero]

lemma complex_re_eq_self_of_im_zero (x : ℂ) (h : x.im = 0) : (x.re : ℂ) = x := by
  cases x
  simp
  simp at h
  rw [h]
  rfl

lemma Matrix_inner_self_real : (⟪x, x⟫).re = ⟪x, x⟫ := by
  apply complex_re_eq_self_of_im_zero
  apply Matrix_inner_self_im_zero

lemma norm_eq_one_iff_unit : unit x ↔ ‖x‖ = 1 := by
  constructor
  · intro h; apply norm_eq_one_of_unit; assumption
  · intro h
    unfold unit
    apply Matrix.ext; intro i j
    have i0 : i = 0 := by
      cases i with | mk i ip=>
      apply Fin.eq_of_val_eq
      simp
      simp at ip
      exact ip
    have j0 : j = 0 := by
      cases j with | mk j jp=>
      apply Fin.eq_of_val_eq
      simp
      simp at jp
      exact jp
    rw[i0,j0]
    change ⟪x, x⟫ = 1
    have h2 : ‖x‖ ^ 2 = 1 := by rw [h]; simp
    rw [← Matrix_inner_self_real, Matrix_inner_self_eq_norm_sq]
    norm_cast

lemma norm_smul_norm_inv_eq_one {s : Vector n} : ‖s‖ ≠ 0 → ‖(‖s‖⁻¹ • s)‖ = 1 := by
  intro h
  rw [_root_.norm_smul]
  simp
  ring_nf
  apply mul_inv_cancel₀ h

end inner_product_lemmas
