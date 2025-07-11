import Myyt.matrix

open scoped BigOperators
open qMatrix

------------------------------------------------------------------------------
-- Matrix helpers for measurement definitions

namespace qMatrix

variable {n m : ℕ} (s : Vector n)

/-- Projection operator onto the state `s` (aka "observable").
    `proj s` can be read as `|ψ⟩⟨ψ|`, when `|ψ⟩ = s`. -/
noncomputable
def proj : Square n := s ⬝ (s†)

/-- Trace of a square matrix -/
noncomputable
def trace (A : Square n) : ℂ := ∑ i, A i i

notation "Tr(" x ")" => trace x

/-- `n × n` partial trace of `m × m` subcomponents of an `(n * m) × (n * m)` square matrix. -/
noncomputable
def partial_trace (M : Square (n * m)) : Square n
:= λ i j=> ∑ k, M (kronLoc i k) (kronLoc j k)

notation "Tr'(" x ")" => partial_trace x

end qMatrix

open qMatrix

namespace Quantum

variable {n m : ℕ} (s : Vector n)

/-- Measurement in the standard basis -/
def measure (m : Fin n) : ℝ := Complex.normSq (s m 0)

notation "⟦" x "⟧,"  => measure x --extra ,

/-- State after measurement (using `measure`) -/
noncomputable
def stateAfterMeasure (m : Fin n)  :=
  (1 / Real.sqrt (⟦s⟧, m) ) • proj (std_basis m) ⬝ s

/-- Partial measurement in the standard basis -/
noncomputable
def partialMeasure (v : Vector (n * m)) (i : Fin n) : ℝ := |v.proj.partial_trace i i|

notation "⦃" x "⦄" => partialMeasure x

end Quantum

-- Common constant numerals

notation "√2" => Real.sqrt 2

-- `/√2` is not allowed as a notation in Lean. So, use `/√2`, instead.
notation "/√2" => (1 / (Real.sqrt 2) : ℂ)

notation "i/√2" => Complex.I / (Real.sqrt 2)


------------------------------------------------------------------------------
-- Common states

-- |0⟩ and |1⟩ using `std_basis`
def ket0 : Vector 2 := std_basis 0
def ket1 : Vector 2 := std_basis 1

notation "|0⟩" => ket0
notation "|1⟩" => ket1

-- |00⟩~|11⟩ using `std_basis`
-- In `ketXY` and "|XY⟩", `Y` is the least significant bit.
def ket00 : Vector 4 := std_basis 0
def ket01 : Vector 4 := std_basis 1
def ket10 : Vector 4 := std_basis 2
def ket11 : Vector 4 := std_basis 3

notation "|00⟩" => ket00
notation "|10⟩" => ket10
notation "|01⟩" => ket01
notation "|11⟩" => ket11

noncomputable
def ket_plus : Vector 2 := ![
    ![ /√2 ],
    ![ /√2 ]]

noncomputable
def ket_minus : Vector 2 := ![
    ![  /√2 ],
    ![ -/√2 ]]

notation "|+⟩" => ket_plus
notation "|-⟩" => ket_minus

-- |00...0⟩ (= |0⟩ ⊗ ... ⊗ |0⟩ or the `n`-th tensor power of |0⟩).
-- Used for zero padding or ancillae qubits.
def ket_zeros (n : ℕ) : Vector (2^n) := std_basis ⟨0, by simp⟩

-- |Φ+⟩ : One of the four bell states
noncomputable
def ket_phi_plus : Vector 4 := ![
    ![ /√2 ],
    ![   0 ],
    ![   0 ],
    ![ /√2 ]]

notation "|Φ+⟩" => ket_phi_plus


-- Common gates

-- X gate (aka NOT gate)
def X : Square 2 := ![
    ![ 0, 1 ],
    ![ 1, 0 ]]

def Z : Square 2 := ![
    ![ 1, 0 ],
    ![ 0, -1 ]]

-- Hadamard gate
noncomputable
def H : Square 2 := ![
    ![ /√2,  /√2 ],
    ![ /√2, -/√2 ]]

-- Controlled-NOT gate (aka CX gate)
def CNOT : Square 4 := ![
    ![ 1, 0, 0, 0 ],
    ![ 0, 1, 0, 0 ],
    ![ 0, 0, 0, 1 ],
    ![ 0, 0, 1, 0 ]]

-- Controlled-Z gate
def CZ : Square 4 := ![
    ![ 1, 0, 0, 0 ],
    ![ 0, 1, 0, 0 ],
    ![ 0, 0, 1, 0 ],
    ![ 0, 0, 0, -1 ]]

def SWAP : Square 4 :=
    ![ ![1, 0, 0, 0],
       ![0, 0, 1, 0],
       ![0, 1, 0, 0],
       ![0, 0, 0, 1]]


-- Controlled-U gates

section controlled_gate

variable {n : ℕ} (U : Square n)

/-- Controlled-U gate : |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U -/
noncomputable
def controlled_gate := |0⟩.proj ⊗ (I n) + |1⟩.proj ⊗ U

/-- Upside-down Controlled-U gate (2-qubit case)-/
noncomputable
def gate_controlled (U : Square 2) := SWAP ⬝ controlled_gate U ⬝ SWAP

end controlled_gate

-- Common projection operators

def P0 : Square 2 := ![
    ![ 1, 0 ],
    ![ 0, 0 ]]

def P1 : Square 2 := ![
    ![ 0, 0 ],
    ![ 0, 1 ]]

noncomputable
def P_plus : Square 2 := ![
    ![ 1/2, 1/2 ],
    ![ 1/2, 1/2 ]]

noncomputable
def P_minus : Square 2 := ![
    ![ 1/2, -(1/2) ],
    ![ -(1/2), 1/2 ]]
