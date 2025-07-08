import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Reflection
import Mathlib.Algebra.BigOperators.Group.Finset.Defs


open scoped BigOperators
--open Matrix

-- ℝ lemmas
lemma real.le_of_le_pow_two {a b : ℝ} (h : a^2 ≤ b^2) (an : 0 ≤ a) (bn : 0 ≤ b) : a ≤ b := by
  rw [← Real.sqrt_mul_self an]
  rw[← Real.sqrt_mul_self bn]
  repeat rw [pow_two] at h
  apply Real.sqrt_le_sqrt h

namespace Matrix


local notation  x "†" => star x

section conjugate
-- Conjugate of a vector.
def conj {𝕜 : Type _} [RCLike 𝕜] {m : Type _} (v : m → 𝕜) : m → 𝕜 :=
  fun i =>  (v i)†


end conjugate

section conj_lemmas

@[simp]
lemma conj_zero {𝕜 : Type _} [RCLike 𝕜] {m : Type _} : conj (0 : m → 𝕜) = 0 := by
  ext i; simp[conj]

lemma conj_smul {𝕜 : Type _} [RCLike 𝕜] {m : Type _} {x : m → 𝕜} {s : 𝕜} : conj (s • x) = s† • conj x := by
  ext i; simp[conj]

lemma conj_add {𝕜 : Type _} [RCLike 𝕜] {m : Type _} {x y : m → 𝕜} : conj (x + y) = conj x + conj y := by
  ext i; simp[conj]

lemma conj_neg {𝕜 : Type _} [RCLike 𝕜] {m : Type _} {x : m → 𝕜} : conj (-x) = -conj x := by
  ext i; simp[conj]

end conj_lemmas


section inner_product

variable {𝕜 : Type _} [RCLike 𝕜]
variable {m : Type _} [Fintype m]

/-- Inner product of two vectors, following the convention that it is conjugate linear in the first argument. -/
def inner_product  (x y : m → 𝕜) : 𝕜 :=
  dotProduct (conj x) y

instance : Inner 𝕜 ((m → 𝕜)) := ⟨inner_product⟩


end inner_product

local notation "⟪" X "," Y "⟫" => inner_product X Y

section inner_product_lemmas

variable {𝕜 : Type _} [RCLike 𝕜] {m : Type _} [Fintype m]
variable {x y z : m → 𝕜} {s : 𝕜}

lemma inner_product_self_eq_sum_conj_mul : ⟪x, x⟫ = ∑ i,  ((x i)†) * x i := rfl

lemma inner_product_self_re_eq_sum_norm_sq : RCLike.re ⟪x, x⟫ = ∑ i, RCLike.normSq (x i) := by
  rw [inner_product_self_eq_sum_conj_mul]
  rw [map_sum]  -- 交换 RCLike.re 和求和顺序
  apply Finset.sum_congr rfl
  intro i _
  rw[RCLike.star_def]
  rw[RCLike.normSq_eq_def']
  rw[RCLike.conj_mul]
  rw[pow_two]
  simp
  rw[pow_two]

@[simp]
lemma inner_product_self_im_zero : RCLike.im ⟪x, x⟫ = 0 := by
  rw [inner_product_self_eq_sum_conj_mul]  -- 展开内积定义
  rw [map_sum]  -- 交换 RCLike.im 和求和
  apply Finset.sum_eq_zero  -- 证明每一项的虚部都是 0
  intro i _
  rw [RCLike.star_def, RCLike.conj_mul]  -- 展开共轭乘法
  rw[pow_two]
  simp  --

@[simp]
lemma inner_product_self_re_eq_self : (RCLike.re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by

  have h : (RCLike.re ⟪x, x⟫ : 𝕜) + (RCLike.im ⟪x, x⟫ ) * (RCLike.I) = ⟪x, x⟫ :=
    RCLike.re_add_im ⟪x, x⟫
  rw[inner_product_self_im_zero] at h
  rw[RCLike.ofReal_zero] at h
  simp at h
  exact h

lemma inner_product_self_eq_sum_norm_sq : ⟪x, x⟫ = ∑ i, RCLike.normSq (x i) := by
  rw[← inner_product_self_re_eq_self]
  rw[inner_product_self_re_eq_sum_norm_sq]

@[simp]
lemma inner_product_self_re_nonneg (x : m → 𝕜) : 0 ≤ RCLike.re ⟪x, x⟫ := by
  rw [inner_product_self_re_eq_sum_norm_sq]
  apply Finset.sum_nonneg
  intro i _
  apply RCLike.normSq_nonneg

lemma inner_product_self_zero : ⟪x, x⟫ = 0 → x = 0 := by
  rw [inner_product_self_eq_sum_norm_sq]
  intro h
  norm_cast at h
  have normSq_nonneg : ∀ i, 0 ≤ RCLike.normSq (x i) :=by
    intros i
    apply RCLike.normSq_nonneg

  have h_nonneg : ∀ i ∈ Finset.univ, 0 ≤ RCLike.normSq (x i) := by
    intros i _
    exact RCLike.normSq_nonneg (x i)
  have f1 := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h
  ext i
  exact RCLike.normSq_eq_zero.mp (f1 i (Finset.mem_univ i))


lemma inner_product_self_add : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  unfold inner_product
  rw [conj_add]
  rw [add_dotProduct]
  rw [dotProduct_add]
  rw [dotProduct_add]
  ring

@[simp]
lemma inner_product_self_neg : ⟪-x, -x⟫ = ⟪x, x⟫ := by
  unfold inner_product
  rw [conj_neg]
  simp

lemma inner_product_smul_l : ⟪s • x, y⟫ = (s†) * ⟪x, y⟫ := by
  unfold inner_product
  rw [conj_smul, smul_dotProduct]
  simp

lemma inner_product_smul_r : ⟪x, s • y⟫ = s * ⟪x, y⟫ := by
  unfold inner_product
  rw [dotProduct_smul]
  simp

lemma inner_product_add_left : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  unfold inner_product
  rw [conj_add, add_dotProduct]

lemma inner_product_add_right : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  unfold inner_product
  rw [dotProduct_add]

@[simp]
lemma inner_product_zero_r : ⟪x, (0 : m → 𝕜)⟫ = 0 := by
  unfold inner_product; simp

@[simp]
lemma inner_product_zero_l : ⟪(0 : m → 𝕜), x⟫ = 0 := by
  unfold inner_product; simp

@[simp]
lemma conj_inner_product :  ⟪y, x⟫† = ⟪x, y⟫ := by
  unfold inner_product
  unfold dotProduct
  simp
  congr; funext i
  unfold conj
  simp; ring

lemma inner_product_mul_eq_normSq : ⟪x, y⟫ * ⟪y, x⟫ = RCLike.normSq ⟪y, x⟫ := by
  rw [← conj_inner_product]
  rw [RCLike.normSq_eq_def']
  rw [RCLike.star_def, RCLike.conj_mul]
  simp


lemma abs_inner_product_comm : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by
  rw [← conj_inner_product]
  rw [RCLike.star_def, RCLike.norm_conj]

lemma re_inner_product_comm : RCLike.re ⟪x, y⟫ = RCLike.re ⟪y, x⟫ := by
  rw [← conj_inner_product]
  apply RCLike.conj_re

end inner_product_lemmas

section norm

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]

/--
Norm of a vector
-/
noncomputable
def norm (x : m → 𝕜) : ℝ := (RCLike.re ⟪x, x⟫).sqrt

noncomputable
instance : Norm (m → 𝕜) := ⟨norm⟩

end norm

------------------------------------------------------------------------------
-- matrix.norm lemmas

section norm_lemmas

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]
variable {x : m → 𝕜}

lemma norm_smul (s : 𝕜) : norm (s • x) = ‖s‖ * norm x := by
  unfold norm
  have f1 : ‖s‖ = Real.sqrt (RCLike.normSq s) := by
    rw [RCLike.normSq_eq_def']
    simp

  rw [inner_product_smul_l]
  rw [inner_product_smul_r]
  rw [← mul_assoc]
  rw [RCLike.star_def]
  rw [RCLike.conj_mul]
  rw[pow_two]
  simp

@[simp]
lemma norm_zero : norm (0 : m → 𝕜) = 0 := by
  simp [norm, inner_product_self_eq_sum_norm_sq]

@[simp]
lemma norm_nonneg : 0 ≤ norm x := by
  exact Real.sqrt_nonneg _

@[simp]
lemma norm_neg : norm (-x) = norm x := by
  simp [norm]

end norm_lemmas

-- has_norm.norm lemmas for proof automation
section has_norm_lemmas

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]
variable {x : m → 𝕜}

lemma has_norm_sq_eq_re_inner_product_self : ‖x‖^2 = RCLike.re ⟪x, x⟫ := by
  have h : ‖x‖ = (RCLike.re ⟪x, x⟫).sqrt := rfl
  rw[h]
  simp

@[simp]
lemma has_norm_zero : ‖(0 : m → 𝕜)‖ = 0 := by
  have h_inner : ⟪(0 : m → 𝕜), (0 : m → 𝕜)⟫ = 0 := by
    unfold inner_product
    simp
  have h : ‖(0 : m → 𝕜)‖ = (RCLike.re ⟪0, 0⟫).sqrt := rfl
  rw [h]
  simp

@[simp]
lemma has_norm_nonneg : 0 ≤ ‖x‖ := by
  exact Real.sqrt_nonneg _

end has_norm_lemmas

section cauchy_schwarz_inequality

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]
variable {u v : m → 𝕜}

lemma cauchy_schwarz_inequality_step1 : ‖u + v‖^2 = (‖u‖^2 + RCLike.re ⟪u, v⟫) + (RCLike.re ⟪u, v⟫ + ‖v‖^2) := by
  iterate 3 rw [has_norm_sq_eq_re_inner_product_self]
  unfold inner_product
  rw[conj_add]
  rw [dotProduct_add]
  simp
  have h1 : RCLike.re (⟪v, u⟫) = RCLike.re (⟪u, v⟫) := by
    apply re_inner_product_comm
  unfold inner_product at h1
  exact h1



lemma cauchy_schwarz_inequality_step2_1 : ⟪u, (-(⟪v , u⟫/⟪v , v⟫)) • v⟫ = -‖⟪u , v⟫‖^2 /⟪v , v⟫ := by
  rw [inner_product_smul_r]
  simp
  ring_nf
  rw [mul_assoc, mul_comm, mul_assoc]
  simp
  rw[inner_product_mul_eq_normSq]
  rw[RCLike.normSq_eq_def']
  simp[abs_inner_product_comm]



lemma cauchy_schwarz_inequality_step2_2 : ⟪(-(⟪v , u⟫/⟪v , v⟫)) • v, u⟫ = -‖⟪u , v⟫‖^2/⟪v , v⟫ := by
  rw [inner_product_smul_l]
  simp
  rw [mul_comm]
  rw[← mul_div_assoc]
  rw[inner_product_mul_eq_normSq]
  rw[RCLike.normSq_eq_def']
  rw[neg_div']
  simp


lemma cauchy_schwarz_inequality_step2_3 (h : v ≠ 0) : ‖-(⟪v, u⟫/⟪v, v⟫) • v‖ ^ 2 = ‖⟪u, v⟫‖^2 / (RCLike.re ⟪v, v⟫) := by
  rw [has_norm_sq_eq_re_inner_product_self]
  rw [inner_product_smul_l]
  rw [inner_product_smul_r]
  --rw [mul_assoc]
  have f1 : (-(⟪v, u⟫ / ⟪v, v⟫))† * (-(⟪v, u⟫ / ⟪v, v⟫))
    = RCLike.normSq (⟪v, u⟫ / ⟪v, v⟫) := by
    rw[RCLike.normSq_eq_def']
    rw[RCLike.star_def, RCLike.conj_mul]
    simp
  have f2 : (-(⟪v,u⟫ / ⟪v,v⟫))† * (-(⟪v,u⟫ / ⟪v,v⟫) * ⟪v,v⟫)= (-(⟪v,u⟫ / ⟪v,v⟫))† * (-(⟪v,u⟫ / ⟪v,v⟫) )* ⟪v,v⟫:=by
    rw[mul_assoc ]
  rw [f2]
  rw [f1]
  rw [RCLike.normSq_div]
  simp
  norm_cast
  rw [RCLike.normSq_eq_def']
  have f2 : RCLike.normSq ⟪v, v⟫ = RCLike.re ⟪v, v⟫ * RCLike.re ⟪v, v⟫ := by
    unfold RCLike.normSq
    simp
  rw [f2]
  ring_nf
  nth_rw 3[mul_comm ]
  rw[mul_assoc ]
  congr 1
  simp
  apply abs_inner_product_comm
  rw [pow_two]
  rw [← mul_assoc]
  have h1 : ⟪v, v⟫ ≠ 0 := by
    contrapose! h
    exact inner_product_self_zero h
  have h2 : RCLike.re ⟪v,v⟫ ≠ 0 := by
    contrapose! h1
    apply RCLike.ext
    rw[h1]
    symm
    apply RCLike.zero_re'
    rw[inner_product_self_im_zero]
    simp
  have h3 : RCLike.re ⟪v,v⟫ * (RCLike.re ⟪v,v⟫)⁻¹ =1 :=by
    field_simp
  rw[h3]
  rw [one_mul]


lemma cauchy_schwarz_inequality_part1 (h : v ≠ 0) :
    ‖u - (⟪v, u⟫/⟪v, v⟫) • v‖ ^ 2 = ‖u‖^2 - RCLike.re (‖⟪u, v⟫‖^2 / ⟪v, v⟫ : 𝕜) := by
  have f1 : u - (⟪v, u⟫/⟪v, v⟫) • v = u + (-(⟪v, u⟫/⟪v, v⟫)) • v := by simp; ring
  rw [f1]
  rw [cauchy_schwarz_inequality_step1]
  have f2 : ‖u‖^2 - RCLike.re (‖⟪u, v⟫‖^2 / ⟪v, v⟫ : 𝕜) = (‖u‖^2 + RCLike.re (-‖⟪u, v⟫‖^2 / ⟪v, v⟫ : 𝕜)) + 0 := by
    rw [neg_div]
    simp
    ring
  rw [f2]
  congr 1
  congr 1
  rw [cauchy_schwarz_inequality_step2_1]
  rw [cauchy_schwarz_inequality_step2_1]
  rw [cauchy_schwarz_inequality_step2_3 h]
  have f4 : ∀ {r s : ℝ}, r = -s → r + s = 0 := by intros r s h; rw [h]; simp
  apply f4
  have f5 : ∀ {r s : ℝ}, -(r/s) = RCLike.re (-r / s : 𝕜) := by intros; norm_cast; ring
  rw [f5]
  simp

theorem cauchy_schwarz_inequality : ‖⟪u, v⟫‖^2 ≤ ‖u‖^2 * ‖v‖^2 := by
  by_cases h : v = 0
  rw [h]
  repeat  rw [pow_two]
  simp
  have f1 : 0 ≤ ‖u‖^2 - RCLike.re (‖⟪u, v⟫‖^2 / ⟪v, v⟫ : 𝕜) := by
    rw [← cauchy_schwarz_inequality_part1 h]
    rw [has_norm_sq_eq_re_inner_product_self]
    simp
  have f2 : RCLike.re (‖⟪u, v⟫‖^2 / ⟪v, v⟫ : 𝕜) ≤ ‖u‖^2 := by
    have g1 : ∀ (r s : ℝ), 0 ≤ r - s → s ≤ r := by simp
    apply g1
    apply f1
  have f3 : ‖⟪u, v⟫‖^2 / ‖v‖^2 ≤ ‖u‖^2 := by
    rw [has_norm_sq_eq_re_inner_product_self]
    have f3' : ∀ {r s : ℝ}, r/s = RCLike.re (r / s : 𝕜) := by intros; norm_cast
    rw [f3']
    rw [inner_product_self_re_eq_self]
    apply_mod_cast f2
  apply (div_le_iff₀ _).mp
  assumption
  rw [has_norm_sq_eq_re_inner_product_self]
  let f4 := inner_product_self_re_nonneg v
  have h1 : ⟪v, v⟫ ≠ 0 := by
    contrapose! h
    exact inner_product_self_zero h
  have f5 : RCLike.re ⟪v,v⟫ ≠ 0 := by
    contrapose! h1
    apply RCLike.ext
    rw[h1]
    symm
    apply RCLike.zero_re'
    rw[inner_product_self_im_zero]
    simp
  by_contra c
  push_neg at c
  apply f5
  linarith

lemma cauchy_schwarz_inequality_alt : ‖⟪u,v⟫‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖⟪u, v⟫‖^2 ≤ ‖u‖^2 * ‖v‖^2 :=by
    exact cauchy_schwarz_inequality
  apply Real.sqrt_le_sqrt at h
  simp at h
  exact h

end cauchy_schwarz_inequality



section triangle_inequality

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]
variable {x y : m → 𝕜}

lemma norm_sq_add_le_add_norm_sq : ‖x + y‖^2 ≤ (‖x‖ + ‖y‖)^2 := by
  rw [has_norm_sq_eq_re_inner_product_self]
  rw [inner_product_self_add]
  simp
  repeat rw [sq]
  repeat rw [add_mul]
  repeat rw [mul_add]
  repeat rw [← sq]
  repeat rw [has_norm_sq_eq_re_inner_product_self]
  have f0 : RCLike.re ⟪y,x⟫ = RCLike.re ⟪x,y⟫ := by rw [re_inner_product_comm]
  rw [f0]
  have f1 : RCLike.re ⟪x,x⟫ + RCLike.re ⟪x,y⟫ + RCLike.re ⟪x,y⟫ + RCLike.re ⟪y,y⟫ = (RCLike.re ⟪x,x⟫ + RCLike.re ⟪y,y⟫) + (2 * RCLike.re ⟪x,y⟫) := by ring
  rw [f1]
  have f2 : RCLike.re ⟪x,x⟫ + ‖x‖ * ‖y‖ + (‖y‖ * ‖x‖ + RCLike.re ⟪y,y⟫) = (RCLike.re ⟪x,x⟫ + RCLike.re ⟪y,y⟫) + 2 * ‖x‖ * ‖y‖ := by ring
  rw [f2]
  simp
  rw [mul_assoc]
  have f3 : RCLike.re ⟪x,y⟫ ≤ (‖x‖ * ‖y‖) → 2 * RCLike.re ⟪x,y⟫ ≤ 2 * (‖x‖ * ‖y‖) := by intro h; linarith
  apply f3
  have f1 : RCLike.re ⟪x,y⟫ ≤ ‖RCLike.re ⟪x,y⟫‖ := by
    apply le_abs_self
  have f2 : ‖RCLike.re ⟪x,y⟫‖ ≤ ‖⟪x,y⟫‖ := by
    apply RCLike.norm_re_le_norm
  have f3 : ‖⟪x,y⟫‖ ≤ ‖x‖ * ‖y‖ := by
    exact cauchy_schwarz_inequality_alt
  exact f1.trans (f2.trans f3)


lemma triangle_inequality : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖^2 ≤ (‖x‖ + ‖y‖)^2 := by
    exact norm_sq_add_le_add_norm_sq
  apply Real.sqrt_le_sqrt at h
  simp at h
  have h2 :√((‖x‖ + ‖y‖) ^ 2)=‖x‖ + ‖y‖ := by
    rw[Real.sqrt_sq]
    apply add_nonneg
    apply norm_nonneg
    apply norm_nonneg
  rw [h2] at h
  exact h

end triangle_inequality


section dist

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]

/--
Distance between two vectors
-/
noncomputable def dist (x y : m → 𝕜) := norm (x-y)

noncomputable instance : Dist (m → 𝕜) := ⟨dist⟩

end dist

------------------------------------------------------------------------------
-- dist lemmas

section dist_lemmas

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m : Type*} [Fintype m]
variable {x y z : m → 𝕜}

lemma dist_self : dist x x = 0 := by
  unfold dist; simp

lemma eq_of_dist_eq_zero : dist x y = 0 → x = y := by
  intro h
  have h' : (dist x y) ^ 2 = 0 := by rw [h]; simp
  have f1 : ⟪x - y,x - y⟫ = (0 : 𝕜) := by
    unfold dist norm at h'
    rw [sq, Real.mul_self_sqrt] at h'
    · rw [← inner_product_self_re_eq_self]
      exact_mod_cast h'
    · simp
  have f2 : x - y = 0 := inner_product_self_zero f1
  rw [sub_eq_zero] at f2
  exact f2


lemma dist_comm : dist x y = dist y x := by
  unfold dist
  have f1 : y - x = -(x - y) := by simp
  rw [f1, norm_neg]

lemma dist_triangle : dist x z ≤ dist x y + dist y z := by
  unfold dist
  have f1 : x - z = (x - y) + (y - z) := by abel
  rw [f1]
  exact triangle_inequality

end dist_lemmas
