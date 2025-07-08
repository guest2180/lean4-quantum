import Myyt.quantum_lemma

open qMatrix

noncomputable def expectation (ψ : Vector n) (A : qMatrix n n) : ℂ :=
  (ψ† ⬝ A ⬝ ψ) 0 0


noncomputable def variance (ψ : Vector n) (A : qMatrix n n) : ℝ :=
  let μ := expectation ψ A
  let A' := A - μ • I(n)
  ‖((ψ† ⬝ A' ⬝ A' ⬝ ψ) 0 0).re‖

noncomputable def stddev (ψ : Vector n) (A : qMatrix n n) : ℝ :=
  Real.sqrt (variance ψ A)


noncomputable def commutator (A B : qMatrix n n) : qMatrix n n :=
  A ⬝ B - B ⬝ A


theorem heisenberg_uncertainty
  {n : ℕ} (ψ : Vector n) (A B : qMatrix n n)
  (hA : A.adjoint = A) -- A 是自伴算符
  (hB : B.adjoint = B) -- B 是自伴算符
  :
  stddev ψ A * stddev ψ B ≥ Complex.abs (expectation ψ (commutator A B)) / 2
:= by
  unfold expectation commutator stddev variance
  simp
  set ΔA:=A - expectation ψ A • 1
  set ΔB:=B - expectation ψ B • 1
  have inner1:(ψ† ⬝ ΔB ⬝ ΔA ⬝ ψ) 0 0=inner ((ψ† ⬝ ΔB)†) (ΔA ⬝ ψ):=by
        unfold inner instInnerComplexOfNatNat inner_product
        simp
        rw[Matrix.mul_assoc]
  have inner2:(ψ† ⬝ ΔA ⬝ ΔB ⬝ ψ) 0 0=inner ((ψ† ⬝ ΔA)†) (ΔB ⬝ ψ):=by
        unfold inner instInnerComplexOfNatNat inner_product
        simp
        rw[Matrix.mul_assoc]
  have hΔA' : ΔA.adjoint = ΔA := by
        unfold ΔA;
        simp [hA, adjoint_sub]
        rw[adjoint_smul]
        unfold expectation
        nth_rw 1[← hA]
        rw[← adjoint_mul]
        rw[Matrix.mul_assoc]
        set aj:=A ⬝ ψ
        have h:(ψ† ⬝ aj) 0 0=inner ψ aj:=by
          unfold inner instInnerComplexOfNatNat inner_product
          simp
        rw[h]
        have h2: (aj† ⬝ ψ) 0 0=inner aj ψ:=by
          unfold inner instInnerComplexOfNatNat inner_product
          simp
        rw[h2]
        rw[← InnerProductSpace.conj_symm]
        simp
  have hΔB' : ΔB.adjoint = ΔB := by
        unfold ΔB;
        simp [hB, adjoint_sub]
        rw[adjoint_smul]
        unfold expectation
        nth_rw 1[← hB]
        rw[← adjoint_mul]
        rw[Matrix.mul_assoc]
        set bj:=B ⬝ ψ
        have h:(ψ† ⬝ bj) 0 0=inner ψ bj:=by
          unfold inner instInnerComplexOfNatNat inner_product
          simp
        rw[h]
        have h2: (bj† ⬝ ψ) 0 0=inner bj ψ:=by
          unfold inner instInnerComplexOfNatNat inner_product
          simp
        rw[h2]
        rw[← InnerProductSpace.conj_symm]
        simp
  have h_comm :
  (ψ† ⬝ (A ⬝ B - B ⬝ A) ⬝ ψ) 0 0
  = 2 * Complex.I * Complex.im ((ψ† ⬝ (ΔA ⬝ ΔB) ⬝ ψ) 0 0):=by
    set α := expectation ψ A with hα
    set β := expectation ψ B with hβ
    have h1 : ΔA ⬝ ΔB = A ⬝ B - α • B - β • A + (α * β) • I(n) := by
      unfold ΔA ΔB
      rw[← hα,← hβ]
      simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_smul_comm, ← sub_add, ← add_assoc]
      simp
    have h2 : ΔB ⬝ ΔA = B ⬝ A - β • A - α • B + (α * β) • I(n) := by
      unfold ΔA ΔB
      rw[← hα,← hβ]
      simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_smul_comm, ← sub_add, ← add_assoc]
      simp[mul_comm]
    have comm_expand : ΔA ⬝ ΔB - ΔB ⬝ ΔA = A ⬝ B - B ⬝ A := by
      rw [h1, h2]
      abel
    rw [← comm_expand]
    rw [Matrix.mul_assoc]
    set z := (ψ† ⬝ ΔA ⬝ ΔB ⬝ ψ) 0 0 with hz
    nth_rw 2[← Matrix.mul_assoc]
    have h_im : z -  z† = 2 * Complex.I * Complex.im z := by
      rw[RCLike.star_def]
      rw[Complex.sub_conj]
      simp
      ring
    have h_conj :  z† = (ψ† ⬝ ΔB ⬝ ΔA ⬝ ψ) 0 0 := by
      rw[inner1]


      rw[inner2]
      rw[← InnerProductSpace.conj_symm]
      simp
      rw[adjoint_mul]
      rw[adjoint_mul]
      simp
      rw[hΔA', hΔB']
    rw[← hz]
    rw[← h_im]
    rw[h_conj ]
    rw[hz]
    rw [Matrix.sub_mul]
    rw[Matrix.mul_sub]
    repeat rw[← Matrix.mul_assoc]
    rw[Matrix.sub_apply]
  rw[h_comm]
  simp
  rw[← Matrix.mul_assoc]
  rw[inner2]
  rw[adjoint_mul]
  rw[hΔA']
  simp
  nth_rw 2[← hΔA']
  nth_rw 2[← hΔB']
  have h1: (ψ† ⬝ ΔA.adjoint ⬝ ΔA ⬝ ψ) 0 0=inner (ΔA ⬝ ψ) (ΔA ⬝ ψ):=by
    unfold inner instInnerComplexOfNatNat inner_product
    simp
    rw [← Matrix.mul_assoc]
    rw [adjoint_mul]
  have h2: (ψ† ⬝ ΔB.adjoint ⬝ ΔB ⬝ ψ) 0 0=inner (ΔB ⬝ ψ) (ΔB ⬝ ψ):=by
    unfold inner instInnerComplexOfNatNat inner_product
    simp
    rw [← Matrix.mul_assoc]
    rw [adjoint_mul]
  rw[h1,h2]
  have final1: ‖ (inner (ΔA ⬝ ψ) (ΔB ⬝ ψ) : ℂ)‖ ≤ ‖ (ΔA ⬝ ψ)‖ *‖ (ΔB ⬝ ψ)‖:=by
    rw [qMatrix_inner_eq_Matrix_inner]
    repeat rw [Matrix_norm_eq_matrix_norm]
    apply Matrix.cauchy_schwarz_inequality_alt
  have final2: √ (abs (inner (ΔA ⬝ ψ) (ΔA ⬝ ψ): ℂ).re)=‖ (ΔA ⬝ ψ)‖:=by
    have lt:0≤‖ (ΔA ⬝ ψ)‖^2:=by
      have lt2:0≤‖ (ΔA ⬝ ψ)‖:=by
        apply norm_nonneg
      exact pow_nonneg lt2 2
    unfold Norm.norm instNormOfNatNat qMatrix.norm
    unfold inner instInnerComplexOfNatNat
    simp
    rw[← Real.sqrt_sq_eq_abs]
    rw[pow_two]
    rw[Real.sqrt_mul_self]
    have hh: inner_product (ΔA ⬝ ψ) (ΔA ⬝ ψ)=inner (ΔA ⬝ ψ) (ΔA ⬝ ψ):=by
      unfold inner instInnerComplexOfNatNat
      simp
    rw[hh]
    rw[Matrix_inner_self_eq_norm_sq]
    exact lt
  have final3: √ (abs (inner (ΔB ⬝ ψ) (ΔB ⬝ ψ): ℂ).re)=‖ (ΔB ⬝ ψ)‖:=by
    have lt:0≤‖ (ΔB ⬝ ψ)‖^2:=by
      have lt2:0≤‖ (ΔB ⬝ ψ)‖:=by
        apply norm_nonneg
      exact pow_nonneg lt2 2
    unfold Norm.norm instNormOfNatNat qMatrix.norm
    unfold inner instInnerComplexOfNatNat
    simp
    rw[← Real.sqrt_sq_eq_abs]
    rw[pow_two]
    rw[Real.sqrt_mul_self]
    have hh: inner_product (ΔB ⬝ ψ) (ΔB ⬝ ψ)=inner (ΔB ⬝ ψ) (ΔB ⬝ ψ):=by
      unfold inner instInnerComplexOfNatNat
      simp
    rw[hh]
    rw[Matrix_inner_self_eq_norm_sq]
    exact lt
  rw[final2,final3]
  have final :abs ((inner (ΔA ⬝ ψ) (ΔB ⬝ ψ)):ℂ ).im≤  ‖ (inner (ΔA ⬝ ψ) (ΔB ⬝ ψ) : ℂ)‖:=by
    simp
    apply Complex.abs_im_le_abs
  exact le_trans final final1
