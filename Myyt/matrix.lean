import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Reflection

open Complex Matrix

notation "|" x "|" => ‖x‖
notation x "†" => star x

@[reducible]
def qMatrix (m n : Nat) := Matrix (Fin m) (Fin n) ℂ

namespace qMatrix

variable {m n : Nat}

def adjoint (M : qMatrix m n) : qMatrix n m :=
  fun x y => (M y x)†

end qMatrix

notation "Vector" n => qMatrix n 1
notation "Square" n => qMatrix n n
notation "I" n => (1 : qMatrix n n)

infixl:75 " ⬝ " => HMul.hMul
postfix:102 "†" => qMatrix.adjoint


variable {n : Nat}

def unit (s : Vector n) : Prop := s† ⬝ s = 1



namespace qMatrix

variable {n : Nat} (M : Square n)

def normal : Prop :=
  qMatrix.adjoint M ⬝ M = M ⬝ qMatrix.adjoint M

def unitary : Prop :=
  qMatrix.adjoint M ⬝ M = 1

end qMatrix

section std_basis

variable {m : Type*} [Fintype m] [DecidableEq m]

def std_basis (i : m) : Matrix m (Fin 1) ℂ :=
  fun j _ => if j = i then 1 else 0

end std_basis

lemma fin_mul_right_has_zero {m p : ℕ} (i : Fin (m * p)) : 0 < p := by
  apply Nat.pos_of_mul_pos_left
  exact Fin.pos i

section kron

variable {m n p q : Nat}

lemma fin_add_mul_lt {m p : ℕ} (r : Fin m) (v : Fin p) :
    p * (r : ℕ) + (v : ℕ) < m * p := by
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

lemma kronDiv_prove {m p : ℕ} (i : Fin (m * p)) : i.val / p < m := by
  have f0 : 0 < p :=by
    apply Nat.pos_of_mul_pos_left
    exact Fin.pos i
  cases i with | mk i hi =>
  simp only [Fin.val_mk]
  rw[mul_comm] at hi
  exact Nat.div_lt_of_lt_mul hi



def kronDiv2 (i : Fin (m * p)) : Fin m :=
  ⟨i.val / p, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.2 ((Nat.mul_comm m p)))⟩
@[reducible]
def kronDiv (i : Fin (m * p)) : Fin m :=
   ⟨i.val / p, kronDiv_prove i⟩

  --(nat.div_lt_iff_lt_mul (i : ℕ) m (fin_mul_right_has_zero i)).mpr i.property

@[reducible]
def kronMod (i : Fin (m*n)) : Fin n :=
⟨ (i : ℕ)%n, Nat.mod_lt (i : ℕ) (Nat.pos_of_mul_pos_left (Fin.pos i)) ⟩


def kron (A : qMatrix m n) (B : qMatrix p q) : qMatrix (m * p) (n * q) :=
  fun i j =>
    A (kronDiv i) (kronDiv j) * B (kronMod i) (kronMod j)


@[reducible]
def kronLoc (r : Fin m) (v : Fin p) : Fin (m * p) :=
  ⟨p * r.1 + v.1, fin_add_mul_lt r v⟩

end kron

infixl:75 " ⊗ " => kron
