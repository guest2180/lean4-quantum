import Myyt
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


lemma even_if_square_even' {n : ℕ} (hn2 : 2 ∣ (n ^ 2)) : 2 ∣ n :=
  by
    cases Nat.even_or_odd n with
    | inl h =>
      rw [Nat.even_iff] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      exact h
    | inr h =>
      rw [Nat.odd_iff] at h
      have hsq : (n ^ 2) % 2 = 1 := by
        rw [Nat.pow_mod, h]
      rw [Nat.dvd_iff_mod_eq_zero] at hn2
      rw[hn2] at hsq
      tauto

theorem sqrt_2_irrational : ¬∃ (p : ℚ), p ^ 2 = 2 := by
  by_contra h
  cases h with
  | intro p hp =>
    set m := Int.natAbs p.num with hm
    set n := p.den with hn

    have hm2 : p.num * p.num = m * m := by
      norm_cast
      rw [hm]
      rw [Int.natAbs_mul_self]
    have hm2_rat : (p.num : ℚ) * (p.num : ℚ) = (m : ℚ) * (m : ℚ) := by
      norm_cast

    have hp2 :  (1:ℚ) * m * m = (2:ℚ) * n * n := by
      rw [← hp]
      rw [one_mul]
      rw [← hm2_rat]
      rw [← Rat.den_mul_eq_num]
      rw[hn]
      ring

    have hp2_nat : m * m = 2 * n * n := by
      norm_cast at hp2
      rw[one_mul] at hp2
      exact hp2

    have hmmeven : 2 ∣ m * m := by
      rw[hp2_nat]
      rw[mul_assoc ]
      exact Nat.dvd_mul_right _ _

    rw[← pow_two] at hmmeven

    have hmeven : 2 ∣ m  := by
      apply even_if_square_even'
      exact hmmeven


    have h4m2 : 4 ∣ m * m := by
      have h2m : 2 ∣ m := hmeven
      apply Nat.mul_dvd_mul hmeven hmeven

    have h2nneven : 4 ∣ 2 * n * n := by
      rw [← hp2_nat]
      exact h4m2

    have hnneven : 2 ∣ n * n := by
      have h4_eq_2_mul_2 : 4 = 2 * 2 := by norm_num
      rw [h4_eq_2_mul_2] at h2nneven
      apply Nat.dvd_div_of_mul_dvd at h2nneven
      rw [mul_assoc] at h2nneven
      rw [mul_comm] at h2nneven
      rw [Nat.mul_div_assoc] at h2nneven
      rw [Nat.div_self] at h2nneven
      rw [mul_one] at h2nneven
      exact h2nneven
      norm_num
      exact Nat.dvd_refl 2

    rw[← pow_two] at hnneven

    have hneven : 2 ∣ n  := by
      apply even_if_square_even'
      exact hnneven

    have hcop := p.reduced

    rw[← hm] at hcop
    rw[← hn] at hcop

    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) hmeven hneven hcop
