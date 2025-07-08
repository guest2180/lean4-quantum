import Myyt.quantum_lemma

open qMatrix

local notation "|0^(" n ")⟩" => ket_zeros n

lemma no_cloning_contra :
   ¬ (∀ (x y : Vector 2), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y)) := by
  intro h

  have f1 : (|0⟩† ⬝ |+⟩) = ![![ /√2]] := by
    unfold_qubits
    apply Matrix.ext
    intros x y
    fin_cases x
    fin_cases y
    simp


  have f2 : (|0⟩† ⬝ |+⟩) = ![![ 1/2]] := by
    rw [h]
    rw [f1]
    unfold kron
    apply Matrix.ext
    intros i j
    simp
    norm_cast
    field_simp

  have f1' : (|0⟩† ⬝ |+⟩) 0 0 = /√2 := by
    rw [f1]
    simp
  have f2' : (|0⟩† ⬝ |+⟩) 0 0 = 1/ 2 := by
    rw [f2]
    simp

  have c : /√2 = 1 / 2 := by
    rw [←f1', ←f2']
  simp at c
  have h4:(2:ℂ )=√2* √2:=by
    norm_cast
    rw[Real.mul_self_sqrt]
    simp
  rw[c] at h4
  simp at h4


theorem no_cloning_1
    : ¬ (∃ (U : qMatrix 4 4), U.unitary ∧ ∀ s : Vector 2, U ⬝ (s ⊗ |0⟩) = s ⊗ s):=by
    intro h
    rcases h with ⟨U, ⟨H1, H2⟩⟩
    have f1: ∀ (x y : Vector 2), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y):=by
      intro x y
      rw[← kron_mixed_prod]
      have g1: (x† ⊗ (|0⟩†)) ⬝ (U.adjoint ⬝ U) ⬝ (y ⊗ |0⟩) = (x† ⊗ (x†)) ⬝ (y ⊗ y):=by
        rw[← Matrix.mul_assoc]
        rw[← adjoint_kron]
        rw[← adjoint_mul]
        rw[← H2]
        rw[← Matrix.mul_assoc]
        congr
        rw[H2]
        rw[adjoint_kron]
      rw[← g1]
      unfold qMatrix.unitary at H1
      rw[H1]
      rw[Matrix.mul_one]
      rw[kron_mixed_prod]
      simp
    have f2:¬ (∀ (x y : Vector 2), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y)):=by
      apply no_cloning_contra
    tauto


lemma no_cloning_contra_2 (n : ℕ) : ¬ (∀ (x y : Vector 2 * (2^n)), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y)):=by
  intro h
  have f1: ((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩) = λ x y=> /√2:=by
    rw[adjoint_kron]
    rw[kron_mixed_prod]
    simp
    unfold_qubits
    apply Matrix.ext
    intros x y
    fin_cases x
    fin_cases y
    simp
  have f2: ((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩) = λ x y=> 1/2:=by
    rw[h]
    rw[f1]
    unfold kron
    funext x y
    simp only
    norm_cast
    field_simp
  let fin0 := (⟨0, by simp⟩ : Fin (1*1))
  have f1': (((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩)) fin0 fin0 = /√2:=by rw[f1]
  have f2': (((|0⟩ ⊗ |0^(n)⟩)†) ⬝ (|+⟩ ⊗ |0^(n)⟩)) fin0 fin0 = 1/2:=by rw[f2]
  have c : /√2 = 1 / 2 := by
    rw [←f1', ←f2']
  simp at c
  have h4:(2:ℂ )=√2* √2:=by
    norm_cast
    rw[Real.mul_self_sqrt]
    simp
  rw[c] at h4
  simp at h4

theorem no_cloning_2(n : ℕ)(npos : 0 < n)
    : ¬ (∃ (U : Square (2^n * 2^n))
         , U.unitary ∧ ∀ (s : Vector 2^n), U ⬝ (s ⊗ |0^(n)⟩) = s ⊗ s):=by
    intro h
    rcases h with ⟨U, ⟨H1, H2⟩⟩
    have f1: ∀ (x y : Vector 2^n), (x† ⬝ y) = (x† ⬝ y) ⊗ (x† ⬝ y):=by
      intro x y
      have g1: (x† ⊗ (|0^(n)⟩†)) ⬝ (U.adjoint ⬝ U) ⬝ (y ⊗ |0^(n)⟩) = (x† ⊗ (x†)) ⬝ (y ⊗ y):=by
        rw[← Matrix.mul_assoc]
        rw[← adjoint_kron]
        rw[← adjoint_mul]
        rw[← H2]
        rw[← Matrix.mul_assoc]
        congr
        rw[H2]
        rw[adjoint_kron]
      rw[← kron_mixed_prod]
      rw[← g1]
      unfold qMatrix.unitary at H1
      rw[H1]
      rw[Matrix.mul_one]
      rw[kron_mixed_prod]
      simp
    cases n
    {
        linarith
    }
    {
      exfalso
      rw[pow_add]at f1
      rw[mul_comm]at f1
      apply no_cloning_contra_2 _ f1
    }
