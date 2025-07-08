import Myyt.quantum
import Myyt.matrix_lemma


open scoped BigOperators
open Matrix
open qMatrix
open Quantum

section measurement

variable {n : ℕ} {s : Vector n}

lemma measure_eq_mul_conj {m : Fin n}
        : (measure s m : ℂ) = ((s m 0)†) * (s m 0):= by
    unfold Quantum.measure
    simp



lemma measure_eq_proj {m : Fin n} : (measure s m : ℂ) = proj s m m:= by
    unfold Quantum.measure proj
    simp[Matrix.mul_apply]
    unfold adjoint
    rw[RCLike.star_def]
    rw[Complex.mul_conj]

lemma measure_eq_of_proj_eq {a b : Vector n} :
                   proj a = proj b
    → measure a = measure b:= by
    intros h
    rw [← Matrix.ext_iff]  at h
    apply funext
    intros i
    have g: (measure a i : ℂ) = measure b i:=by
        repeat rw [measure_eq_proj]
        apply h
    apply_mod_cast g


lemma nonzero_vector_has_nonzero_measure
        : s ≠ 0 → (∃ i, measure s i ≠ 0):= by
    contrapose!
    intros h
    apply Matrix.ext
    intros i j
    have j0: j = 0:= by
      cases j with | mk j hj =>
        apply Fin.ext
        simp
        simp at hj
        exact hj
    rw [j0]
    simp
    rw[← Complex.normSq_eq_zero]
    apply h


end measurement


-- proj lemmas

section proj

variable {n : ℕ} {s t : Vector n}

-- `proj s` is self-adjoint (aka "Hermitian").
@[simp]
lemma proj_self_adjoint (s : Vector n) : ((proj s).adjoint) = proj s:= by
    unfold proj
    rw [adjoint_mul]
    simp

lemma proj_mul_adjoint_eq_self {n} {u : Vector n} : unit u → (proj u).adjoint ⬝ (proj u) = proj u:= by
    unfold proj
    intros h
    rw [adjoint_mul]
    simp
    rw [Matrix.mul_assoc]
    congr 1
    rw [←  Matrix.mul_assoc]
    have h: u† ⬝ u=1:=by
      rw[unfold_unit h]
    simp[Matrix.mul_apply] at h
    rw[h]
    simp

lemma outer_product_diagnonal_apply {i : Fin n}
        : (s ⬝ t†) i i = (s i 0) * (t i 0)†:= by
    simp[Matrix.mul_apply]
    unfold  adjoint
    left
    simp

lemma outer_product_self_diagnonal_apply_eq_norm_sq {i : Fin n}
        : (s ⬝ s†) i i = (s i 0).normSq:= by
    rw [outer_product_diagnonal_apply]
    simp
    --rw[RCLike.star_def]
    rw[Complex.mul_conj]

lemma proj_diagnonal_eq_mul_conj {i : Fin n} : s.proj i i = (s i 0)† * s i 0:= by
    unfold proj
    rw [outer_product_diagnonal_apply]
    ring

lemma proj_diagnonal_eq_norm_sq {i : Fin n} : s.proj i i = (s i 0).normSq:= by
    rw [proj_diagnonal_eq_mul_conj]
    simp

end proj


section proj_kron

variable {n : ℕ} {s : Vector n}
variable {m : ℕ} {t : Vector m}

lemma proj_kron : proj (s ⊗ t) = proj s ⊗ proj t:= by
    unfold proj
    rw [adjoint_kron]
    rw [kron_mixed_prod]

lemma proj_kron_apply {i : Fin n} {j : Fin m}
    : proj (s ⊗ t) (kronLoc i j) (kronLoc i j)
      = proj s i i * proj t j j:= by
    rw [proj_kron]
    cases i with |mk i ip=>
    cases j with |mk j jp=>
    unfold kron kronDiv kronMod
    simp
    have f1: (m * i + j) / m = i:=by
        rw [add_comm]
        rw [Nat.add_mul_div_left]
        simp[jp]
        linarith

    have f2: (m * i + j) % m = j:=by
        rw [add_comm]
        rw [Nat.add_mul_mod_self_left]
        rw [Nat.mod_eq_of_lt jp]

    congr 1
    congr;
    congr;
    rw[Nat.mod_eq]
    simp[jp]
    rw[Nat.mod_eq]
    simp[jp]

end proj_kron

-- proj + std_basis lemmas

section proj_std_basis

variable {n : ℕ} {m : Fin n}

lemma proj_std_basis_eq_diagonal
        : proj (std_basis m) = Matrix.diagonal (λ i=> if i = m then 1 else 0):= by
    unfold proj
    unfold HMul.hMul
    unfold instHMulOfFintypeOfMulOfAddCommMonoid
    unfold qMatrix.adjoint std_basis
    apply Matrix.ext
    intros i j
    simp
    unfold dotProduct
    by_cases h: i = j
    {
        rw[h]
        cases h
        simp
        by_cases h2: i = m
        {
            cases h2
            simp
        }
        {
            rw [if_neg]
            intro h
            rfl
            exact h2
        }
    }
    {
        unfold Matrix.diagonal
        simp
        rw [if_neg h]
        by_cases h2: i = m
        {
            have f1: ¬ j = m:= by cc
            simp[f1]
        }
        {
            have f1: ¬ i = m:= by cc
            simp[f1]
        }
    }

@[simp]
lemma proj_std_basis_eq_one : proj (std_basis m) m m = 1:= by
    rw [proj_std_basis_eq_diagonal]
    unfold Matrix.diagonal
    simp

lemma proj_std_basis_eq_zero1 {i j : Fin n} : ¬ i = m → proj (std_basis m) i j = 0:= by
    rw [proj_std_basis_eq_diagonal]
    unfold Matrix.diagonal
    intro e
    simp
    intro h
    exact e

lemma proj_std_basis_eq_zero2 {i j : Fin n} : ¬ j = m → proj (std_basis m) i j = 0:= by
    rw [proj_std_basis_eq_diagonal]
    unfold Matrix.diagonal
    intro e
    simp
    by_cases h : i = j
    {

        intro
        rw [← h] at e
        exact e
    }
    {
        intro
        tauto
    }

lemma mul_proj_std_basis_left {n} {m : Fin n} {U : Square n}
    : proj (std_basis m) ⬝ U = λ i j=> ite (i = m) (U i j) 0:= by
    apply Matrix.ext
    intro i j
    rw [proj_std_basis_eq_diagonal]
    simp

lemma mul_proj_std_basis_right {n} {m : Fin n} {U : Square n}
    : U ⬝ proj (std_basis m) = λ i j=> ite (j = m) (U i j) 0:= by
    apply Matrix.ext
    intro i j
    rw [proj_std_basis_eq_diagonal]
    simp

lemma kron_proj_std_basis {m : Fin 2} {U : Square 2}
    : proj (std_basis m) ⊗ U = λ i j=> ite (kronDiv i = m ∧ kronDiv j = m) (U (kronMod i) (kronMod j)) 0:= by
    apply kron_ext_mul
    intro r s v w
    simp
    by_cases h1: r = m
    {
        rw [h1]

        by_cases h2: s = m
        {
            rw[h2]
            simp
        }
        {
            rw [proj_std_basis_eq_zero2 h2]
            simp
            rw [if_neg h2]
        }
    }
    {
        rw [proj_std_basis_eq_zero1 h1]
        have : ¬ (r = m ∧ s = m):= by cc
        rw [if_neg this]
        simp
    }

end proj_std_basis


-- trace lemmas

section trace

variable {n : ℕ} (v w : Square n)

theorem trace_smul (s : ℂ) : Tr(s • v) = s * Tr(v)
:= by
    unfold qMatrix.trace
    simp
    rw [Finset.mul_sum]


lemma trace_adjoint : Tr((v.adjoint)) = Tr(v)†
:= by
    unfold qMatrix.trace
    unfold adjoint
    rw [RCLike.star_def]
    rw [Complex.conj_sum_dist]


lemma abs_trace_adjoint : |Tr(v.adjoint)| = |Tr(v)|
:= by
    unfold qMatrix.trace
    unfold adjoint
    rw [RCLike.star_def]
    rw [Complex.conj_sum_dist]
    rw [RCLike.norm_conj]


lemma trace_mul_comm : Tr(v ⬝ w) = Tr(w ⬝ v)
:= by
    unfold qMatrix.trace
    unfold HMul.hMul instHMulOfFintypeOfMulOfAddCommMonoid
    simp
    unfold dotProduct
    rw [Finset.sum_comm]
    congr
    apply funext
    intro i
    congr
    apply funext
    intro j
    ring


-- for easier match
lemma Fin_sum_sum_mul (f : Fin n → Fin n → ℂ) (g : Fin n → ℂ)
        : (∑ (i : Fin n), ((∑ (j : Fin n), f i j) ⬝ (g i)))
        = (∑ (i : Fin n) (j : Fin n), f i j ⬝ g i)
:= by
    rw[Finset.sum_product]
    simp
    ring_nf
    congr
    funext x
    rw[Finset.sum_mul]


variable {m : ℕ}

lemma trace_mul_rotate_l (a : qMatrix m n) (b : qMatrix n m)
        : Tr(a ⬝ v ⬝ b) = Tr(v ⬝ b ⬝ a)
:= by
    unfold qMatrix.trace
    unfold HMul.hMul instHMulOfFintypeOfMulOfAddCommMonoid dotProduct
    simp
    nth_rw  2[Finset.sum_comm]
    ring_nf
    congr
    apply funext
    intro k
    have h : ∑ x : Fin n, (∑ x_1 : Fin n, a k x_1 ⬝ v x_1 x) ⬝ b x k=∑ x : Fin n, ∑ x_1 : Fin n, a k x_1 ⬝ v x_1 x ⬝ b x k:=by
        rw [Finset.sum_congr rfl]
        simp
        intro w
        rw[Finset.sum_mul]
    rw [h]
    have h2: ∑ x : Fin n, (∑ x_1 : Fin n, v x x_1 ⬝ b x_1 k) ⬝ a k x=∑ x : Fin n, ∑ x_1 : Fin n, v x x_1 ⬝ b x_1 k ⬝ a k x :=by
        rw [Finset.sum_congr rfl]
        simp
        intro w
        rw[Finset.sum_mul]
    rw[h2]
    have h3:  ∑ x : Fin n, ∑ x_1 : Fin n, a k x_1 ⬝ v x_1 x ⬝ b x k =  ∑ x : Fin n, ∑ x_1 : Fin n,  v x_1 x ⬝ b x k ⬝ a k x_1:=by
        apply Finset.sum_congr rfl
        intros x _
        apply Finset.sum_congr rfl
        intros x_1 _
        rw [mul_assoc, mul_comm (a k x_1)]
    rw[h3]
    rw [Finset.sum_comm]



theorem trace_kron {x : Square m}: Tr(v ⊗ x) = Tr(v) * Tr(x)
:= by
    unfold qMatrix.trace kron
    rw [kron_sum_mul_mul]


end trace


section trace_proj

variable {n : ℕ} (s t : Vector n)

theorem trace_outer_eq_inner : Tr(s ⬝ (t†)) = (t† ⬝ s) 0 0:= by
    unfold qMatrix.trace
    unfold HMul.hMul instHMulOfFintypeOfMulOfAddCommMonoid dotProduct
    simp
    congr 1
    apply funext
    intro x
    rw[mul_comm]


lemma trace_outer_eq_trace_inner : Tr(s ⬝ (t†)) = Tr((t†) ⬝ s) := by
    rw [trace_outer_eq_inner]
    unfold qMatrix.trace
    rw [Finset.sum_fin_eq_sum_range]
    rw [Finset.sum_eq_single 0]
    simp
    simp
    simp

theorem trace_proj : Tr(proj s) = ((s†) ⬝ s) 0 0 := by
    unfold proj
    rw [trace_outer_eq_inner]

lemma trace_proj_eq_one_of_unit {s : Vector n} : unit s → Tr(proj s) = 1
:= by
    intro h
    rw [trace_proj]
    rw [unfold_unit h]
    simp

lemma trace_proj_eq_one_of_unit' {s : Vector n} : unit s → Tr(s ⬝ (s†)) = 1
:= by
    intro h
    rw [trace_outer_eq_inner]
    rw [unfold_unit h]
    simp

lemma unit_of_trace_proj_eq_one : Tr(proj s) = 1 → unit s
:= by
    rw [trace_proj]
    intro h
    unfold unit
    apply Matrix.ext
    intro i j
    have i0 : i = 0 := by
        cases j with | mk i hi =>
        apply Fin.ext
        simp
    have j0 : j = 0 := by
        cases i with | mk j hj =>
        apply Fin.ext
        simp
    rw[i0 ,j0]
    simp
    exact h

lemma trace_proj_inner_prod : Tr(proj (s† ⬝ t)) = Tr(proj s ⬝ proj t)
:= by
    unfold proj
    rw [adjoint_mul]
    simp
    rw [←  Matrix.mul_assoc]
    rw [Matrix.mul_assoc (s†)]
    rw [trace_mul_rotate_l]
    rw [Matrix.mul_assoc]
    rw [trace_mul_comm]

lemma conj_trace_outer_product : Tr(s ⬝ t†)† = Tr(s† ⬝ t)
:= by
    have f1: adjoint (t ⬝ s†) = (s ⬝ t†):=by
        rw [adjoint_mul]
        simp
    rw [← f1]
    rw [trace_adjoint]
    simp
    apply trace_outer_eq_trace_inner

end trace_proj


-- partial_trace lemmas

section partial_trace_add

variable {n m : ℕ} {x y : Square n * m}

lemma partial_trace_add : partial_trace (x + y) = partial_trace x + partial_trace y
:= by
    unfold partial_trace
    simp
    apply funext
    intro k
    apply funext
    intro i
    simp
    rw [Finset.sum_add_distrib]


end partial_trace_add


section partial_trace_kron

variable {n m : ℕ} (v : Square n) (w : Square m)

lemma partial_trace_kron : partial_trace (v ⊗ w) = Tr(w) • v
:= by
    unfold partial_trace qMatrix.trace
    apply funext
    intros k
    apply funext
    intros i
    simp
    rw [Finset.sum_mul]
    congr 1
    apply funext
    intros j
    rw [mul_comm]
    rw [mul_to_kron]

@[simp]
theorem trace_partial_trace {v : Square n*m} : Tr(partial_trace v) = Tr(v)
:= by
    unfold qMatrix.trace partial_trace
    rw [← Finset.sum_product']
    rw [←  Finset.sum_preimage (λ x : Fin n × Fin m=> (kronLoc x.1 x.2 : Fin (n * m)))]
    case hf=>
        unfold Set.InjOn
        simp
        intro x y
        intro i j
        intro h
        have h1:(m ⬝ ↑x + ↑y)%m = (m ⬝ ↑i + ↑j)%m:=by
            simp[h]
        simp at h1
        have h2: ↑y % m = ↑y := Nat.mod_eq_of_lt y.isLt
        have h3: ↑j % m = ↑j := Nat.mod_eq_of_lt j.isLt
        rw[h2,h3]at h1
        clear h2 h3
        have h4:(m ⬝ ↑x + ↑y)/m = (m ⬝ ↑i + ↑j)/m:=by
            simp[h]
        rw[h1]at h4
        rw[add_comm]at h4
        rw[Nat.add_mul_div_left]at h4
        nth_rw 2[add_comm]at h4
        rw[Nat.add_mul_div_left]at h4
        simp at h4
        rw[Fin.val_eq_val]at h1 h4
        simp[h1,h4]
        exact Fin.pos y
        exact Fin.pos y
    case hg=>
        simp
        intro x y
        unfold kronLoc at y
        exfalso
        have h2:m>0:=by
            exact fin_mul_right_has_zero x
        cases x with|mk x xp=>
        have xp':=xp
        rw[mul_comm]at xp
        set i : Fin n :=  ⟨x / m, Nat.div_lt_of_lt_mul xp⟩--have failed
        set j : Fin m := ⟨x % m, Nat.mod_lt _ h2⟩
        have h : kronLoc i j = Fin.mk x xp':= by
            rw [kronLoc]
            simp
            rw[Fin.val_mk]
            rw[Fin.val_mk]
            exact Nat.div_add_mod _ m
        apply y i j h
    simp

lemma partial_trace_kron_eq {o} (x : Square o): Tr(v) = Tr(w)
        → partial_trace (x ⊗ v) = partial_trace (x ⊗ w)
:= by
    intros t
    repeat rw [partial_trace_kron ]
    rw [t]

lemma partial_trace_kron_neq {o} (x y : Square o): Tr(v) = Tr(w)
        → partial_trace (x ⊗ v) ≠ partial_trace (y ⊗ w)
        → x ≠ y
:= by
    intro t h c
    apply h
    cases c
    apply partial_trace_kron_eq
    assumption

end partial_trace_kron

section partial_trace_proj

variable {n : ℕ} {s t : Vector n}
variable {m : ℕ} {a b : Vector m}

lemma partial_proj_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → proj a = proj b
:= by
    intros h vt wt
    have f1: partial_trace (proj (a ⊗ s)) = partial_trace (proj (b ⊗ t)):=by
        rw [h]
    repeat rw [proj_kron] at f1
    repeat rw [partial_trace_kron] at f1
    rw [vt] at f1
    rw [wt] at f1
    simp at f1
    exact f1

lemma partial_proj_eq_of_kron_eq' :
        a ⊗ s = b ⊗ t
        → unit s → unit t
        → proj a = proj b
:= by
    intro h su tu
    apply partial_proj_eq_of_kron_eq
    assumption
    rw [trace_proj]
    rw [unfold_unit su]
    simp
    rw [trace_proj]
    rw [unfold_unit tu]
    simp

end partial_trace_proj


section partial_trace_add_kron

variable {n : ℕ} (v w x y : Square n)
variable {m : ℕ} (a b c d : Square m)

lemma partial_trace_add_kron : partial_trace (a ⊗ v + b ⊗ w) = Tr(v) • a + Tr(w) • b
:= by
    unfold partial_trace qMatrix.trace
    apply funext
    intros k
    apply funext
    intros i
    simp

    rw [Finset.sum_add_distrib]
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    congr 1
    {
        congr 1
        apply funext
        intros j
        rw [mul_comm (v j j)]
        rw [mul_to_kron]
    }
    {
        congr 1
        apply funext
        intro j
        rw [mul_comm (w j j)]
        rw [mul_to_kron]
    }

lemma partial_trace_add_kron2 : partial_trace (a ⊗ v + b ⊗ w + c ⊗ x + d ⊗ y)
                                = Tr(v) • a + Tr(w) • b + Tr(x) • c + Tr(y) • d
:= by
    unfold partial_trace qMatrix.trace
    apply funext
    intros k
    apply funext
    intros i
    simp

    repeat rw [Finset.sum_add_distrib]
    repeat rw [Finset.sum_mul]
    congr 1
    {
        congr 1
        {
            congr 1
            {
                congr 1
                apply funext
                intros j
                rw [mul_comm (v j j)]
                rw [mul_to_kron]
            }
            {
                congr 1
                apply funext
                intros j
                rw [mul_comm (w j j)]
                rw [mul_to_kron]
            }
        }
        {
            congr 1
            apply funext
            intro j
            rw [mul_comm (x j j)]
            rw [mul_to_kron]
        }
    }
    {
        congr 1
        apply funext
        intros j
        rw [mul_comm (y j j)]
        rw [mul_to_kron]
    }

end partial_trace_add_kron


section partial_trace_proj_add_kron

variable {n: ℕ} (s t p: Vector n)
variable {m: ℕ} (v w q: Vector m)

lemma proj_add_kron : proj ((t ⊗ w) + (p ⊗ q))
            = t ⬝ (t†) ⊗ (w ⬝ (w†)) + t ⬝ (p†) ⊗ (w ⬝ (q†)) + p ⬝ (t†) ⊗ (q ⬝ (w†)) + p ⬝ (p†) ⊗ (q ⬝ (q†))
:= by
    unfold proj
    repeat rw[adjoint_add]
    repeat rw[adjoint_kron]
    repeat rw[Matrix.add_mul]
    repeat rw[Matrix.mul_add]
    repeat rw[kron_mixed_prod]
    rw[← add_assoc]


lemma partial_trace_proj_add_kron : unit w → unit q → (w†) ⬝ q = 1
            → partial_trace (proj ((t ⊗ w) + (p ⊗ q))) = proj (t + p)
:= by
    intros wu qu h
    rw [proj_add_kron]
    rw [partial_trace_add_kron2]
    rw [trace_proj_eq_one_of_unit' wu]
    rw [trace_proj_eq_one_of_unit' qu]

    have f1: Tr(q ⬝ (w†)) = 1:=by
        rw[trace_outer_eq_trace_inner]
        rw[h]
        unfold qMatrix.trace
        simp
    have f2: Tr(w ⬝ (q†)) = 1:=by
        have : (q†) ⬝ w =1:=by
            apply adjoint_inj
            rw[adjoint_mul]
            simp
            exact h
        rw[trace_outer_eq_trace_inner]
        rw[this]
        unfold qMatrix.trace
        simp

    rw [f1, f2]
    simp
    unfold proj
    rw[Matrix.add_mul]
    repeat rw[adjoint_add]
    repeat rw[Matrix.mul_add]
    rw[← add_assoc]


lemma partial_trace_proj_add_kron2 : unit w → unit q → (w†) ⬝ q = 0
            → partial_trace (proj ((t ⊗ w) + (p ⊗ q))) = proj t + proj p
:= by
    intros wu qu h
    rw [proj_add_kron]
    rw [partial_trace_add_kron2]
    rw [trace_proj_eq_one_of_unit' wu]
    rw [trace_proj_eq_one_of_unit' qu]
    have f1: Tr(q ⬝ (w†)) = 0:=by
        rw [trace_outer_eq_trace_inner]
        rw [h]
        unfold qMatrix.trace
        simp
    have f2: Tr(w ⬝ (q†)) = 0:=by
        have : (q†) ⬝ w = 0:=by
            apply adjoint_inj
            rw[adjoint_mul]
            simp
            exact h
        rw [trace_outer_eq_trace_inner]
        rw[this]
        unfold qMatrix.trace
        simp
    rw[f1,f2]
    unfold proj
    simp

end partial_trace_proj_add_kron


-- state_after_measure lemmas

section state_after_measure_lemmas

variable {n : ℕ} {s : Vector n} {m : Fin n}

lemma state_after_measure_eq_zero {i : Fin n}
        : ¬ i = m → (stateAfterMeasure s m) i 0 = 0
:= by
    intro h
    unfold stateAfterMeasure
    simp
    right
    unfold proj
    simp[Matrix.mul_apply]
    have h : std_basis m i 0=0:=by
        apply std_basis_eq_zero h
    rw[h]
    simp



lemma abs_state_after_measure_eq_one {i : Fin n}
        : (⟦s⟧, m) ≠ 0 → i = m → |stateAfterMeasure s m i 0| = 1
:= by
    intro h x
    unfold stateAfterMeasure Quantum.measure
    unfold Quantum.measure at h
    unfold proj
    simp[Matrix.mul_apply]
    have h1 : std_basis m i 0=1:=by
        apply std_basis_eq_one x
    rw[h1]
    have h2: ∑ x : Fin n, 1 ⬝ std_basis m x 0 ⬝ s x 0= s m 0:=by
        unfold std_basis
        simp
    rw[h2]
    have h3: Complex.abs (s m 0)=√(Complex.normSq (s m 0)):=by
        rw[Complex.normSq_eq_norm_sq]
        simp
    rw[← h3]
    simp at h
    simp[h]


lemma measure_state_after_measure_eq_one {i : Fin n}
        : (⟦s⟧, m) ≠ 0 → i = m → measure (stateAfterMeasure s m) i = 1
:= by
    intro h x
    have h:|stateAfterMeasure s m i 0|=1:=by
        apply abs_state_after_measure_eq_one h x
    unfold Quantum.measure
    rw[Complex.normSq_eq_norm_sq]
    simp[h]

lemma measure_state_after_measure_eq_measure_std_basis
        : (⟦s⟧, m) ≠ 0 → measure (stateAfterMeasure s m) = measure (std_basis m)
:= by
    intro h
    have h1: Quantum.measure (std_basis m)=fun m_1 => Complex.normSq (std_basis m m_1 0):=by
        unfold Quantum.measure
        rfl
    rw[h1]
    funext i
    by_cases c: i = m
    {
        rw[measure_state_after_measure_eq_one]
        rw[c]
        simp
        exact h
        exact c
    }
    {
        unfold Quantum.measure
        rw[state_after_measure_eq_zero]
        simp[c]
        exact c
    }


end state_after_measure_lemmas


-- partial measure lemmas

section partialMeasure

variable {n : ℕ} {a b : Vector n}
variable {m : ℕ} {s t : Vector m}

lemma measure_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → measure a = measure b
:= by
    intros h su tu
    apply measure_eq_of_proj_eq
    apply partial_proj_eq_of_kron_eq h
    exact su
    exact tu

-- not true
-- example: a ⊗ (s + t) = b ⊗ (v + w)
--         → Tr(proj (s + t)) = 1 → Tr(proj (v + w)) = 1
--         → proj a = proj b

lemma partialMeasure_proj_kron
        : Tr(proj s) = 1
        → partialMeasure (a ⊗ s) = measure a
:= by
    intro h
    funext i
    unfold Quantum.measure partialMeasure
    rw[proj_kron]
    rw[partial_trace_kron]
    rw[h]
    simp
    rw[proj_diagnonal_eq_norm_sq]
    simp


lemma partialMeasure_eq_of_kron_eq :
        a ⊗ s = b ⊗ t
        → Tr(proj s) = 1 → Tr(proj t) = 1
        → measure a = measure b
:= by
    intro h stu vwu
    have f1: partialMeasure (a ⊗ s) = partialMeasure (b ⊗ t):=by
        rw [h]

    rw [partialMeasure_proj_kron stu] at f1
    rw [partialMeasure_proj_kron vwu] at f1
    exact f1


lemma unit_has_nonzero_measure
        : unit s → (∃ i, measure s i ≠ 0)
:= by
    intro h
    apply nonzero_vector_has_nonzero_measure
    apply unit_nonzero
    exact h


lemma measure_kron_apply {i : Fin n} {j : Fin m}
    : measure (a ⊗ s) (kronLoc i j)
      = measure a i * measure s j
:= by
    have h: (measure (a ⊗ s) (kronLoc i j) : ℂ)
                = measure a i * measure s j:=by
          repeat rw [measure_eq_proj]
          apply proj_kron_apply
    norm_cast at h


lemma measure_kron_cancel_right:
            measure (a ⊗ s) = measure (b ⊗ s)
            → unit s
            → measure a = measure b
:= by
    intro h us
    funext i
    rw [funext_iff] at h
    cases (unit_has_nonzero_measure us) with |intro j jp=>
        specialize (h (kronLoc i j))
        repeat rw[measure_kron_apply] at h
        simp [jp]at h
        exact h


lemma measure_kron_cancel_left:
            measure (s ⊗ a) = measure (s ⊗ b)
            → unit s
            → measure a = measure b
:= by
    intro h us
    funext i
    rw [funext_iff] at h
    cases (unit_has_nonzero_measure us) with |intro j jp=>
        specialize (h (kronLoc j i))
        repeat rw[measure_kron_apply] at h
        simp [jp]at h
        exact h


end partialMeasure

-- partial_measure_add_kron

section partial_measure_add_kron

variable {n : ℕ} {a b : Vector n}
variable {m : ℕ} {s t : Vector m}
variable {w : Fin n}

lemma partial_measure_add_kron_rhs {a b k : ℂ}
        : ((a + b).normSq : ℂ) - (2 * ((1 - k) * (a * b†)).re : ℝ)
            = (a.normSq + b.normSq : ℂ) + (2 * (k * (a * b†)).re : ℝ)
:= by
    have l1: ((a + b).normSq : ℂ) = (a.normSq + b.normSq)
            + (2 * (a * b†).re : ℝ):=by
            rw[Complex.normSq_add]
            norm_cast
    rw [l1]
    ring_nf
    norm_cast
    set sd:=a ⬝ b†
    simp
    ring


lemma partial_measure_add_kron : Tr(proj s) = 1 → Tr(proj t) = 1
        → ⦃ a ⊗ s + b ⊗ t ⦄
            = λ i=> ‖(a i 0 + b i 0).normSq - 2 * ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re‖
:= by
    intro h h1
    funext i
    have lhs: ⦃a ⊗ s + b ⊗ t⦄ i
                = ‖((a ⬝ a†) i i + (b ⬝ b†) i i) + (Tr(s ⬝ t†) • ((a ⬝ b†) i i) + Tr(t ⬝ s†) • ((b ⬝ a†) i i))‖:=by
                unfold partialMeasure
                rw[proj_add_kron]
                repeat rw[partial_trace_add]
                repeat rw[partial_trace_kron]
                unfold proj at h h1
                rw[h, h1]
                simp
                ring_nf
    rw[lhs]
    repeat rw[outer_product_self_diagnonal_apply_eq_norm_sq]
    repeat rw[outer_product_diagnonal_apply]
    have rhs: (((a i 0 + b i 0).normSq - 2 * ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re : ℝ) : ℂ)
            = ((a i 0).normSq + (b i 0).normSq : ℂ)
                    + (2 * (Tr(s ⬝ t†) * (a i 0 * (b i 0)†)).re : ℝ):=by
                    norm_cast
                    apply_mod_cast partial_measure_add_kron_rhs
    norm_cast at rhs
    rw[rhs]
    have h3: Tr(t ⬝ s†) • b i 0 ⬝ a i 0†= (Tr(s ⬝ t†) • a i 0 ⬝ b i 0†)† :=by
        rw[star_smul]
        rw[← trace_adjoint]
        rw[adjoint_mul]
        rw[StarMul.star_mul]
        simp
    rw[h3]
    nth_rw 2[RCLike.star_def]
    rw[Complex.add_conj]
    norm_cast


lemma partial_measure_add_kron' : Tr(proj s) = 1 → Tr(proj t) = 1
        → ⦃ a ⊗ s + b ⊗ t ⦄
            = λ i=> ‖(a i 0 + b i 0).normSq - 2 * ((1 - Tr(s† ⬝ t)) * ((a i 0)† * b i 0)).re‖
:= by
    intros su tu
    rw [partial_measure_add_kron su tu]
    funext i

    have f1: ((1 - Tr(s ⬝ t†)) * (a i 0 * (b i 0)†)).re
                = ((1 - Tr(s† ⬝ t)) * ((a i 0)† * b i 0)).re:=by
        rw [← Complex.re_conj_eq_re]
        congr 1
        simp
        left
        rw [← RCLike.star_def]
        rw [conj_trace_outer_product]
    rw [f1]


lemma partial_measure_add_kron_of_orthogonal : Tr(proj s) = 1 → Tr(proj t) = 1
        → (∀ i, (a i 0)† * b i 0 = 0)
        → ⦃ a ⊗ s + b ⊗ t ⦄ = ⟦ a + b ⟧,
:= by
    intro su tu h
    rw [partial_measure_add_kron' su tu]
    funext i
    rw [h]
    simp
    unfold Quantum.measure
    apply _root_.abs_of_nonneg
    simp


end partial_measure_add_kron


-- std_basis lemmas for proof automation

macro "solve_std_basis_zero" : tactic => do
 `(tactic| first |rw [std_basis_eq_zero]; decide )


@[simp] lemma std_basis_0_2_1 : (std_basis 0 : Vector 2) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_2_0 : (std_basis 1 : Vector 2) 0 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_0_4_1 : (std_basis 0 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_0_4_2 : (std_basis 0 : Vector 4) 2 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_0_4_3 : (std_basis 0 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_1_4_0 : (std_basis 1 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_4_2 : (std_basis 1 : Vector 4) 2 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_1_4_3 : (std_basis 1 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_2_4_0 : (std_basis 2 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_2_4_1 : (std_basis 2 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_2_4_3 : (std_basis 2 : Vector 4) 3 0 = 0 := by solve_std_basis_zero

@[simp] lemma std_basis_3_0_1 : (std_basis 3 : Vector 4) 0 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_3_4_1 : (std_basis 3 : Vector 4) 1 0 = 0 := by solve_std_basis_zero
@[simp] lemma std_basis_3_4_2 : (std_basis 3 : Vector 4) 2 0 = 0 := by solve_std_basis_zero


-- More proof automation lemmas related to "fin" type.
-- Instances for zero and one on fin types
instance fin_has_zero_one_by_one : Zero (Fin (1 * 1)) :=
  ⟨⟨0, by decide⟩⟩

instance fin_has_zero_two_by_two : Zero (Fin (2 * 2)) :=
  ⟨⟨0, by decide⟩⟩

instance fin_has_one_two_by_two : One (Fin (2 * 2)) :=
  ⟨⟨1, by decide⟩⟩

-- Simplification lemmas for Fin values
@[simp] lemma fin_one_succ : (⟨(1 : ℕ).succ, by decide⟩ : Fin 4) = ⟨2, by decide⟩ := by norm_num
@[simp] lemma fin_one_succ_succ : (⟨(1 : ℕ).succ.succ, by decide⟩ : Fin 4) = ⟨3, by decide⟩ := by norm_num

@[simp] lemma fin_0_div_1 : (⟨((0 : Fin 1) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_num
@[simp] lemma fin_0_mod_1 : (⟨((0 : Fin 1) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_num

@[simp] lemma fin_0_div_2' : (⟨((0 : Fin (2 * 2)) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_cast
@[simp] lemma fin_0_mod_2' : (⟨((0 : Fin (2 * 2)) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_cast

@[simp] lemma fin_1_div_2 : (⟨1 / 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_num
@[simp] lemma fin_1_div_2' : (⟨((1 : Fin (2 * 2)) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_cast
@[simp] lemma fin_1_mod_2 : (⟨((1 : Fin (2 * 2)) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast

@[simp] lemma fin_2_div_2' : (⟨((2 : Fin (2 * 2)) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast
@[simp] lemma fin_2_mod_2' : (⟨((2 : Fin (2 * 2)) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := by norm_cast

@[simp] lemma fin_3_div_2 : (⟨((3 : Fin (3 + 1)) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast
@[simp] lemma fin_3_mod_2 : (⟨((3 : Fin (3 + 1)) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast
@[simp] lemma fin_3_div_2' : (⟨((3 : Fin (2 * 2)) : ℕ) / 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast
@[simp] lemma fin_3_mod_2' : (⟨((3 : Fin (2 * 2)) : ℕ) % 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast

@[simp] lemma fin_one_succ_succ_div_2' : (⟨(1 : ℕ).succ.succ / 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast
@[simp] lemma fin_one_succ_succ_mod_2' : (⟨(1 : ℕ).succ.succ % 2, by decide⟩ : Fin 2) = ⟨1, by decide⟩ := by norm_cast


macro "finish_complex_arith" : tactic =>
  `(tactic| repeat
    (first| simp | rw [RCLike.star_def] | rw [Real.sq_sqrt (by positivity)] | rfl | decide | ring_nf | linarith |norm_cast))

macro "grind_dot_product" : tactic =>
  `(tactic|
    repeat (first | simp[Matrix.mul_apply] | unfold adjoint | rw [Finset.sum_fin_eq_sum_range] | rw [Finset.sum_range_succ] | rw [Finset.sum_range_zero] | rw [dif_pos (by decide)]))


open Lean Meta Elab Tactic

-- 判断一个 `Expr` 是否形如 `_ < _`，并自动解出矛盾
def finishFinOutOfRangeH (h : Expr) : TacticM Unit := do
  let t ← inferType h
  match t.getAppFnArgs with
  | (``LT.lt, #[_, _, _]) =>
      withMainContext do
        evalTactic (← `(tactic|
          exfalso;
          apply not_le_of_gt h;
          repeat (rw [← Nat.add_one]);linarith))
  | _ => throwError "finishFinOutOfRangeH: not a < goal"

-- 遍历局部上下文，尝试对某个 `<` 假设使用上面的 tactic
elab "finishFinOutOfRange" : tactic => do
  let lctx ← getLCtx
  for localDecl in lctx do
    if !localDecl.isImplementationDetail then
      let h := mkFVar localDecl.fvarId
      try
        finishFinOutOfRangeH h
        return
      catch _ => pure () -- 忽略错误，继续尝试下一个
  throwError "finishFinOutOfRange: no < hypothesis found"

-- 判断一个表达式是否是“可能的数值”
def maybeNumeral (e : Expr) : MetaM Bool := do
  if e.isBVar || e.isFVar || e.isMVar then
    return false
  else if e.isApp then
    return true
  else if e.isConst then
    return true
  else if e.isLit then
    return true
  else
    return false


-- 从表达式中提取出局部变量（local const）
-- def findLocalConst (e : Expr) : MetaM Expr := do
--   match e with
--   | .fvar _ => return e  -- 如果是局部变量，直接返回
--   | .app (.const ``Nat.succ _) arg => findLocalConst arg  -- 递归查找 nat.succ 中的局部常量
--   | _ => throwError "findLocalConst: not a local const"  -- 如果不是局部常量，抛出错误

-- -- 解构 fin 1 类型
-- def destructFinOne (h : Expr) : TacticM Unit := do
--   let hType ← inferType h
--   let fin1 ← elabTerm (← `(Fin 1)) none
--   if ← isDefEq hType fin1 then
--     -- 如果类型是 fin 1，直接进行 cases
--     evalTactic (← `(tactic| cases h))
--   else
--     -- 如果类型不匹配，抛出错误
--     throwError "destructFinOne: unsupported type {hType}"

-- def destructFinSucc (h : Expr) : TacticM Unit := do
--   let hType ← inferType h
--   match hType.getAppFnArgs with
--   | (``Fin, #[arg]) =>
--       -- h : Fin (something)
--       if arg.isAppOfArity ``Nat.succ 1 || arg.isAppOfArity ``Num.bit0 1 then
--         evalTactic (← `(tactic| cases h))
--       else
--         throwError "destructFinSucc: Fin argument is not Nat.succ or bit0"
--   | (``LT.lt, #[_, lhs, rhs]) =>
--       -- h : lhs < rhs
--       if rhs.isAppOfArity ``Nat.succ 1 || rhs.isAppOfArity ``Num.bit0 1 then
--         let c ← findLocalConst lhs
--         evalTactic (← `(tactic| cases c))
--       else
--         throwError "destructFinSucc: RHS of < is not Nat.succ or bit0"
--   | _ =>
--       throwError "destructFinSucc: unsupported type {hType}"


-- elab "destructFin" : tactic => do
--   try
--     evalTactic (← `(tactic| finishFinOutOfRange))
--   catch _ =>
--     let lctx ← getLCtx
--     for decl in lctx do
--       if !decl.isImplementationDetail then
--         let h := mkFVar decl.fvarId
--         try
--           destructFinOne h
--           return
--         catch _ => pure ()
--         try
--           destructFinSucc h
--           return
--         catch _ => pure ()
--     throwError "destructFin: no applicable hypothesis found"




/-- Recursively find the local constant inside expressions like `succ x`, etc. -/
def findLocalConst (e : Expr) : MetaM Expr := do
  match e with
  | .fvar _ => return e  -- 如果是局部变量，直接返回
  | .app (.const ``Nat.succ _) arg => findLocalConst arg  -- 递归查找 nat.succ 中的局部常量
  | _ => throwError "findLocalConst: not a local const"



macro "unfold_qubits" : tactic =>
    `(tactic|repeat( first
    |unfold ket0|unfold ket1
    |unfold ket00|unfold ket01|unfold ket10 |unfold ket11
    |unfold ket_plus|unfold ket_minus ))


-- state lemmas
@[simp] lemma ket0_unit : |0⟩† ⬝ |0⟩ = 1 := by
    unfold_qubits
    simp
@[simp] lemma ket1_unit : |1⟩† ⬝ |1⟩ = 1 := by
    unfold_qubits
    simp

macro "unit_vector" : tactic =>
    `(tactic|first|
    apply Matrix.ext;intros;
    unfold_qubits;grind_dot_product;
    norm_cast;finish_complex_arith; )

macro "solve_vector_eq" : tactic =>
    `(tactic|first|
    unfold_qubits;apply Matrix.ext;
    intros i j;
    fin_cases i;fin_cases j;simp [stdBasisMatrix, Pi.single, Matrix.of])


@[simp] lemma ket_plus_unit : (|+⟩†) ⬝ |+⟩ = 1 := by
    unit_vector

@[simp] lemma ket_minus_unit : (|-⟩†) ⬝ |-⟩ = 1 := by
    unit_vector

macro "solve_vector_eq" : tactic =>
    `(tactic|first|
    repeat(unfold_qubits);
    --grind_matrix;
    simp; )



lemma ket_plus_alt_def : |+⟩ = (/√2 • |0⟩) + (/√2 • |1⟩) :=by
    unfold_qubits
    apply Matrix.ext
    intros i j
    fin_cases i
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]

lemma ket_minus_alt_def : |-⟩ = (/√2 • |0⟩) + (-/√2 • |1⟩) := by
    unfold_qubits
    apply Matrix.ext
    intros i j
    fin_cases i
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]

@[simp] lemma ket_zeros_unit {n : ℕ} : (((ket_zeros n)†) ⬝ (ket_zeros n) = 1):= by
    unfold ket_zeros
    simp

@[simp] lemma ket_phi_plus_unit : ket_phi_plus† ⬝ ket_phi_plus = 1:= by
    unfold ket_phi_plus
    unit_vector

@[simp]
lemma vec_head_fin_one (f : Fin 1 → ℂ) : Matrix.vecHead (λ x : Fin 1=> f x) = f 0
:= by
    unfold vecHead
    simp

lemma ket_phi_plus_alt_def : ket_phi_plus = /√2 • (|00⟩) + /√2 • (|11⟩):=by
    unfold ket_phi_plus
    unfold_qubits
    apply Matrix.ext
    intros i j
    fin_cases i
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]


lemma ket_phi_plus_alt_def' : ket_phi_plus = /√2 • (|0⟩ ⊗ |0⟩) + /√2 • (|1⟩ ⊗ |1⟩)
:= by
    rw [ket_phi_plus_alt_def]
    unfold ket0 ket1 ket00 ket11
    repeat rw [kron_std_basis ]
    norm_cast

-- The "unit" flavor (`unit s`), instead of `s† ⬝ s`.
@[simp] lemma ket0_unit': unit |0⟩ := by
    unfold_qubits
    simp
@[simp] lemma ket1_unit': unit |1⟩ := by
    unfold_qubits
    simp
@[simp] lemma ket_plus_unit': unit |+⟩ := by
    unfold unit
    simp
@[simp] lemma ket_minus_unit': unit |-⟩ := by
    unfold unit
    simp

-- Inner product values

-- This could be read as `⟨0|+⟩` on books.
@[simp] lemma inner_ket0_ket_plus :  ⟪ |0⟩, |+⟩ ⟫ = (/√2 : ℂ)
:= by
    unfold inner instInnerComplexOfNatNat qMatrix.inner_product
    unfold_qubits
    grind_dot_product

macro "unfold_gates" : tactic =>
    `(tactic|repeat( first
    |unfold X|unfold y
    |unfold Z|unfold H|unfold CNOT |unfold CZ
    |unfold SWAP))

macro "solve_matrix_apply_eq" : tactic =>
  `(tactic|try
    unfold_gates;
    apply Matrix.ext;
    intros i j;
    fin_cases i;
    repeat (
      fin_cases j
      simp [stdBasisMatrix, Pi.single, Matrix.of]
      grind_dot_product
      try unfold_qubits
      try simp
      try ring_nf
      try norm_cast
      try simp))


@[simp] lemma X_unitary : X.adjoint ⬝ X = 1 :=by
    solve_matrix_apply_eq

@[simp] lemma Z_unitary : Z.adjoint ⬝ Z = 1 := by
    solve_matrix_apply_eq

@[simp] lemma H_unitary : H.adjoint ⬝ H = 1 := by
    unfold_gates
    apply Matrix.ext
    intros i j
    fin_cases i
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    grind_dot_product
    norm_cast
    ring_nf
    simp
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    grind_dot_product
    fin_cases j
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    simp [stdBasisMatrix, Pi.single, Matrix.of]
    norm_cast
    ring_nf
    simp

@[simp] lemma CNOT_self_inner_0_0 : (CNOT.adjoint ⬝ CNOT) 0 0 = 1 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_self_inner_0_1 : (CNOT.adjoint ⬝ CNOT) 0 1 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_self_inner_0_2 : (CNOT.adjoint ⬝ CNOT) 0 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_0_3 : (CNOT.adjoint ⬝ CNOT) 0 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_self_inner_1_0 : (CNOT.adjoint ⬝ CNOT) 1 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_1_1 : (CNOT.adjoint ⬝ CNOT) 1 1 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_1_2 : (CNOT.adjoint ⬝ CNOT) 1 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_1_3 : (CNOT.adjoint ⬝ CNOT) 1 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_self_inner_2_0 : (CNOT.adjoint ⬝ CNOT) 2 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_2_1 : (CNOT.adjoint ⬝ CNOT) 2 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_2_2 : (CNOT.adjoint ⬝ CNOT) 2 2 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_2_3 : (CNOT.adjoint ⬝ CNOT) 2 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_self_inner_3_0 : (CNOT.adjoint ⬝ CNOT) 3 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_3_1 : (CNOT.adjoint ⬝ CNOT) 3 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_3_2 : (CNOT.adjoint ⬝ CNOT) 3 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CNOT_self_inner_3_3 : (CNOT.adjoint ⬝ CNOT) 3 3 = 1 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CNOT_unitary : CNOT.adjoint ⬝ CNOT = 1 := by
    solve_matrix_apply_eq

@[simp] lemma CZ_inner_self_0_0 : (CZ.adjoint ⬝ CZ) 0 0 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_0_1 : (CZ.adjoint ⬝ CZ) 0 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_0_2 : (CZ.adjoint ⬝ CZ) 0 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_0_3 : (CZ.adjoint ⬝ CZ) 0 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CZ_inner_self_1_0 : (CZ.adjoint ⬝ CZ) 1 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_1_1 : (CZ.adjoint ⬝ CZ) 1 1 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_1_2 : (CZ.adjoint ⬝ CZ) 1 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_1_3 : (CZ.adjoint ⬝ CZ) 1 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CZ_inner_self_2_0 : (CZ.adjoint ⬝ CZ) 2 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_2_1 : (CZ.adjoint ⬝ CZ) 2 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_2_2 : (CZ.adjoint ⬝ CZ) 2 2 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_2_3 : (CZ.adjoint ⬝ CZ) 2 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma CZ_inner_self_3_0 : (CZ.adjoint ⬝ CZ) 3 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_3_1 : (CZ.adjoint ⬝ CZ) 3 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_3_2 : (CZ.adjoint ⬝ CZ) 3 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma CZ_inner_self_3_3 : (CZ.adjoint ⬝ CZ) 3 3 = 1 := by
    unfold_gates
    grind_dot_product


lemma CZ_unitary : CZ.adjoint ⬝ CZ = 1 := by
    solve_matrix_apply_eq


@[simp] lemma SWAP_inner_self_0_0 : (SWAP.adjoint ⬝ SWAP) 0 0 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_0_1 : (SWAP.adjoint ⬝ SWAP) 0 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_0_2 : (SWAP.adjoint ⬝ SWAP) 0 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_0_3 : (SWAP.adjoint ⬝ SWAP) 0 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma SWAP_inner_self_1_0 : (SWAP.adjoint ⬝ SWAP) 1 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_1_1 : (SWAP.adjoint ⬝ SWAP) 1 1 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_1_2 : (SWAP.adjoint ⬝ SWAP) 1 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_1_3 : (SWAP.adjoint ⬝ SWAP) 1 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma SWAP_inner_self_2_0 : (SWAP.adjoint ⬝ SWAP) 2 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_2_1 : (SWAP.adjoint ⬝ SWAP) 2 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_2_2 : (SWAP.adjoint ⬝ SWAP) 2 2 = 1 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_2_3 : (SWAP.adjoint ⬝ SWAP) 2 3 = 0 := by
    unfold_gates
    grind_dot_product

@[simp] lemma SWAP_inner_self_3_0 : (SWAP.adjoint ⬝ SWAP) 3 0 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_3_1 : (SWAP.adjoint ⬝ SWAP) 3 1 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_3_2 : (SWAP.adjoint ⬝ SWAP) 3 2 = 0 := by
    unfold_gates
    grind_dot_product
@[simp] lemma SWAP_inner_self_3_3 : (SWAP.adjoint ⬝ SWAP) 3 3 = 1 := by
    unfold_gates
    grind_dot_product

lemma SWAP_unitary : SWAP.adjoint ⬝ SWAP = 1 := by
    solve_matrix_apply_eq

-- gate and state lemmas

@[simp] lemma X_ket0_eq_ket1 : X ⬝ |0⟩ = |1⟩ := by
    solve_matrix_apply_eq

@[simp] lemma X_ket1_eq_ket0 : X ⬝ |1⟩ = |0⟩ := by
    solve_matrix_apply_eq

@[simp] lemma H_ket0_eq_ket_plus  : H ⬝ |0⟩ = |+⟩ := by
    solve_matrix_apply_eq
@[simp] lemma H_ket1_eq_ket_minus : H ⬝ |1⟩ = |-⟩ := by
    solve_matrix_apply_eq
@[simp] lemma H_ket_plus_eq_ket0  : H ⬝ |+⟩ = |0⟩ := by
    solve_matrix_apply_eq
@[simp] lemma H_ket_minus_eq_ket1 : H ⬝ |-⟩ = |1⟩ := by
    solve_matrix_apply_eq


@[simp] lemma CNOT_ket00_eq_ket00 : CNOT ⬝ |00⟩ = |00⟩ := by
    solve_matrix_apply_eq

@[simp] lemma CNOT_ket01_eq_ket01 : CNOT ⬝ |01⟩ = |01⟩ := by
    solve_matrix_apply_eq

@[simp] lemma CNOT_ket10_eq_ket11 : CNOT ⬝ |10⟩ = |11⟩ := by
    solve_matrix_apply_eq

@[simp] lemma CNOT_ket11_eq_ket10 : CNOT ⬝ |11⟩ = |10⟩ := by
    solve_matrix_apply_eq


-- SWAP gate lemmas

section SWAP_lemmas

variable {a b : Vector 2}

macro "unfold_swap_app" : tactic =>
    `(tactic|try
    unfold SWAP;
    try simp;
    try unfold Matrix.vecHead Matrix.vecTail
    )

macro "solve_swap_kron" : tactic =>
    `(tactic|try
    unfold_swap_app
    simp
    unfold Matrix.vecHead Matrix.vecTail
    unfold kron kronDiv kronMod
    repeat(first|simp|ring)
    )


lemma SWAP_kron_0 : (SWAP ⬝ (a ⊗ b)) ⟨0, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 0 0
:= by
    unfold_swap_app
    unfold kron kronDiv kronMod
    simp
    grind_dot_product
    rw[mul_comm]


lemma SWAP_kron_1 : (SWAP ⬝ (a ⊗ b)) ⟨1, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 1 0
:= by
    unfold_swap_app
    unfold kron kronDiv kronMod
    simp
    grind_dot_product
    rw[mul_comm]
lemma SWAP_kron_2 : (SWAP ⬝ (a ⊗ b)) ⟨2, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 2 0
:= by
    unfold_swap_app
    unfold kron kronDiv kronMod
    simp
    grind_dot_product
    rw[mul_comm]
lemma SWAP_kron_3 : (SWAP ⬝ (a ⊗ b)) ⟨3, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 3 0
:= by
    unfold_swap_app
    unfold kron kronDiv kronMod
    simp
    grind_dot_product
    rw[mul_comm]

@[simp] lemma SWAP_kron_0' :
  (SWAP ⬝ (a ⊗ b)) ⟨0, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 0 0 := by apply SWAP_kron_0

@[simp] lemma SWAP_kron_1' :
  (SWAP ⬝ (a ⊗ b)) ⟨1, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 1 0 := by apply SWAP_kron_1

@[simp] lemma SWAP_kron_2' :
  (SWAP ⬝ (a ⊗ b)) ⟨2, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 2 0 := by apply SWAP_kron_2

@[simp] lemma SWAP_kron_3' :
  (SWAP ⬝ (a ⊗ b)) ⟨3, by decide⟩ ⟨0, by decide⟩ = (b ⊗ a) 3 0 := by apply SWAP_kron_3

lemma SWAP_kron : SWAP ⬝ (a ⊗ b) = b ⊗ a:=by
    funext x y
    fin_cases x
    fin_cases y
    apply SWAP_kron_0'
    fin_cases y
    apply SWAP_kron_1'
    fin_cases y
    apply SWAP_kron_2'
    fin_cases y
    apply SWAP_kron_3'

end SWAP_lemmas

-- Numeric constants lemmas for proof automation

@[simp] lemma sqrt_2_nonneg : 0 ≤ √2:=by
    apply Real.sqrt_nonneg

@[simp] lemma one_lt_sqrt_2 : 1 < √2:=by
    have :1=√1:=by
        simp
    rw[this]
    have h:(1:ℝ) <(2:ℝ):=by norm_cast
    apply Real.sqrt_lt_sqrt
    norm_cast
    exact h

@[simp] lemma sqrt_2_nonzero : √2 ≠ 0:=by
    linarith [one_lt_sqrt_2]

@[simp] lemma sqrt_two_mul_self : √2 * √2 = 2:=by
    simp

@[simp] lemma one_over_sqrt_two_mul_self : /√2 * /√2 = 1/2:=by
    norm_cast
    ring_nf
    simp

@[simp] lemma sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = 1/2:=by
    ring_nf
    simp

-- Gate decompositions

lemma P0_eq_proj_ket0 : P0 = proj |0⟩:=by
    unfold P0 ket0
    rw [proj_std_basis_eq_diagonal]
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    fin_cases y
    simp
    simp

lemma P1_eq_proj_ket1 : P1 = proj |1⟩:=by
    unfold P1 ket1
    rw [proj_std_basis_eq_diagonal]
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    fin_cases y
    simp
    simp

lemma I_eq_add_P0_P1 : (I 2) = P0 + P1:=by
    unfold P0 P1
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    fin_cases y
    simp
    simp

lemma I_eq_add_P_plus_P_minus : (I 2) = P_plus + P_minus:=by
    unfold P_plus P_minus
    funext x y
    fin_cases x
    fin_cases y
    simp
    ring_nf
    simp
    fin_cases y
    simp
    simp
    ring_nf

lemma X_eq_sub_P_plus_P_minus : X = P_plus - P_minus:=by
    unfold P_plus P_minus X
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    ring_nf
    fin_cases y
    simp
    ring_nf
    simp

lemma Z_eq_sub_P0_P1 : Z = P0 - P1:=by
    unfold P0 P1 Z
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    fin_cases y
    simp
    simp

lemma CNOT_decompose : CNOT = P0 ⊗ (I 2) + P1 ⊗ X:=by
    unfold P0 P1 CNOT X
    unfold kron kronMod kronDiv
    simp
    funext x y
    fin_cases x
    fin_cases y
    repeat simp
    fin_cases y
    simp
    simp
    norm_cast
    simp
    simp
    fin_cases y
    repeat simp
    fin_cases y
    repeat simp

lemma CZ_decompose : CZ = P0 ⊗ (I 2) + P1 ⊗ Z:=by
    unfold CZ P0 P1 Z
    unfold kron kronMod kronDiv
    simp
    funext x y
    fin_cases x
    fin_cases y
    repeat simp
    fin_cases y
    repeat simp
    norm_cast
    repeat simp
    norm_cast
    fin_cases y
    repeat simp
    fin_cases y
    repeat simp

lemma CZ_decompose_alt : CZ = (I 2) ⊗ P0 + Z ⊗ P1:=by
    unfold CZ P0 Z P1
    funext i j
    fin_cases i
    fin_cases j
    repeat simp [kron, Matrix.add, Matrix.one, stdBasisMatrix, Pi.single]
    fin_cases j
    repeat simp [kron, Matrix.add, Matrix.one, stdBasisMatrix, Pi.single]
    fin_cases j
    repeat simp [kron, Matrix.add, Matrix.one, stdBasisMatrix, Pi.single]
    norm_cast
    simp [kron, Matrix.add, Matrix.one, stdBasisMatrix, Pi.single]
    fin_cases j
    repeat simp [kron, Matrix.add, Matrix.one, stdBasisMatrix, Pi.single]

lemma mul_P0_H : P0 ⬝ H = ![ ![ /√2, /√2 ], ![ 0, 0 ] ]:=by
    rw [P0_eq_proj_ket0]
    unfold ket0
    rw [mul_proj_std_basis_left]
    unfold H
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    simp
    fin_cases y
    simp
    simp

lemma mul_P1_H : P1 ⬝ H = ![ ![ 0, 0 ], ![ /√2, -/√2 ] ]:=by
    rw [P1_eq_proj_ket1]
    unfold ket1
    rw [mul_proj_std_basis_left]
    unfold H
    funext x y
    fin_cases x
    fin_cases y
    simp
    simp
    simp

lemma H_P0_H_eq_P_plus : H ⬝ P0 ⬝ H = P_plus:=by
    rw [Matrix.mul_assoc]
    rw [mul_P0_H]
    unfold H P_plus
    funext x y
    fin_cases x
    fin_cases y
    grind_dot_product
    ring_nf
    norm_cast
    simp
    grind_dot_product
    ring_nf
    norm_cast
    simp
    fin_cases y
    grind_dot_product
    ring_nf
    norm_cast
    simp
    grind_dot_product
    ring_nf
    norm_cast
    simp

lemma H_P1_H_eq_P_minus : H ⬝ P1 ⬝ H = P_minus:=by
    rw [Matrix.mul_assoc]
    rw [mul_P1_H]
    unfold H P_minus
    funext x y
    fin_cases x
    fin_cases y
    grind_dot_product
    ring_nf
    norm_cast
    simp
    grind_dot_product
    ring_nf
    norm_cast
    simp
    fin_cases y
    grind_dot_product
    ring_nf
    norm_cast
    simp
    grind_dot_product
    ring_nf
    norm_cast
    simp

theorem CNOT_eq_H_CZ_H : CNOT = ((I 2) ⊗ H) ⬝ CZ ⬝ ((I 2) ⊗ H)
:= by
    rw [CNOT_decompose]
    rw [I_eq_add_P_plus_P_minus]
    rw [X_eq_sub_P_plus_P_minus]
    have : P0 ⊗ (P_plus + P_minus) + P1 ⊗ (P_plus - P_minus)
        = (P0 + P1) ⊗ P_plus + (P0 - P1) ⊗ P_minus:=by
        rw [kron_dist_over_add_right]
        rw [kron_dist_over_sub_right]
        rw [kron_dist_over_add_left]
        rw [kron_dist_over_sub_left]
        abel
    rw [this]
    clear this
    rw [← I_eq_add_P0_P1]
    rw [← Z_eq_sub_P0_P1]
    have l1: (I 2) ⊗ P_plus = ((I 2) ⊗ H) ⬝ ((I 2) ⊗ P0) ⬝ ((I 2) ⊗ H):=by
        rw [← H_P0_H_eq_P_plus]
        rw [kron_mixed_prod_I_left]
        rw [kron_mixed_prod_I_left]
    have l2: Z ⊗ P_minus = ((I 2) ⊗ H) ⬝ (Z ⊗ P1) ⬝ ((I 2) ⊗ H):=by
        rw [← H_P1_H_eq_P_minus]
        rw [kron_mixed_prod_I_left]
        rw [kron_mixed_prod_I_right]
    rw [l1]
    rw [l2]
    rw [← I_eq_add_P_plus_P_minus]
    rw [← Matrix.add_mul]
    congr 1
    rw [← Matrix.mul_add]
    congr 1
    rw [CZ_decompose_alt]

-- Controlled-U gates definitions

lemma CNOT_def : CNOT = controlled_gate X
:= by
    rw [CNOT_decompose]
    unfold controlled_gate
    rw [P0_eq_proj_ket0]
    rw [P1_eq_proj_ket1]

lemma CZ_def : CZ = controlled_gate Z
:= by
    rw [CZ_decompose]
    unfold controlled_gate
    rw [P0_eq_proj_ket0]
    rw [P1_eq_proj_ket1]

macro "numify_SWAP" : tactic =>
  `(tactic|first| simp only [SWAP]; norm_num)
macro "numify_CZ" : tactic =>
  `(tactic|first| simp only [CZ]; norm_num)

-- CZ gate's control and target can be swapped and the operater is still the same.
lemma CZ_symmetry : CZ = SWAP ⬝ CZ ⬝ SWAP
:= by
    --unfold CZ SWAP
    funext i j
    have := Matrix.mul_assoc SWAP CZ SWAP
    rw [this]
    simp only [Matrix.mul_apply]
    fin_cases i
    fin_cases j
    grind_dot_product
    numify_SWAP
    grind_dot_product
    numify_SWAP
    numify_CZ
    grind_dot_product
    numify_SWAP
    numify_CZ
    grind_dot_product
    numify_SWAP
    numify_CZ
    grind_dot_product
    numify_SWAP
    numify_CZ
    grind_dot_product
    numify_SWAP
    grind_dot_product
    numify_SWAP
    numify_CZ
    fin_cases j
    all_goals simp


lemma CZ_def' : CZ = gate_controlled Z
:= by
    unfold gate_controlled
    rw [← CZ_def]
    apply CZ_symmetry
