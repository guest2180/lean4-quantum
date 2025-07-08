# Readme based on orginal project:
## Quantum Computing in Lean

This is an implementation of the theory of quantum computing in the Lean programming language (using the Lean theorem prover version 4). [The original lean3 project](https://github.com/duckki/lean-quantum)

It's built on top of the "mathlib" library written by the Lean Community.


### Organization

#### The [Myyt](Myyt) directory

* [common_lemmas.lean](Myyt/common_lemma.lean): Contains lemmas that are not specific to complex matrix or quantum computing.

* [matrix_inner_product.lean](Myyt/matrix_inner_product.lean): The `inner_product_space` instantiation for the `Matrix` type.

* [matrix.lean](Myyt/matrix.lean): Matrix-related definitions, notably `qMatrix` and `kron` (the Kronecker product).

  * The `Matrix` type is defined based on the mathlib's `Matrix` type, but specialized for complex number and the `Fin` range type.

* [matrix_lemma.lean](Myyt/matrix_lemma.lean): Derived facts from the definitions of `qMatrix`, `kron` and `adjoint`.

* [quantum.lean](Myyt/quantum.lean): Definitions for quantum computing, such as measurements and basic states and circuits.

* [quantum_lemma.lean](Myyt/quantum_lemma.lean): Derived facts from the definitions in the [quantum.lean](Myyt/quantum.lean) file.

* [measurement.lean]: More generalized definitions of measurements and theorems about them.(This part has not been converted into lean 4 because writer is lazy)


##### The [Myyt/src](Myyt/src) directory

* [no_cloning.lean](Myyt/src/no_cloning.lean): Several different versions of the "no-cloning" theorems.

* [random-number-generator.lean]: A few examples of Hadamard transform algorithm. (This part has not been converted into lean 4 because writer is lazy)
  
* [uncertainty.lean](Myyt/src/uncertainty.lean): A version of Heisenberg Uncertainty Principle which can be discribed as $\sigma_A \sigma_B \geq \frac{1}{2} \left| \langle [A, B] \rangle \right|$


### Reference materials

* Tutorial: Quantum Programming: https://sites.google.com/ncsu.edu/qc-tutorial/home

* An Introduction to Quantum Computing, Without the Physics : https://arxiv.org/abs/1708.03684

* The "Verified Quantum Computing" book: https://www.cs.umd.edu/~rrand/vqc/


### Related project

* Lean: https://leanprover.github.io

* Lean Community: https://leanprover-community.github.io

* QWIRE: https://github.com/inQWIRE/QWIRE
  * "A quantum circuit language and formal verification tool" by Robert Rand et al.


# Readme from lean4 vision writer:

* This project can be running on Lean v4.16.0 and mathlib.

* I don't know if anybody else is working on these things, at least I can't find anything similar when I begin this project.

* It's not recommend to simply integration this project into other lean 4 project, because this project is completely based on the old lean 3 version, which may contain outdated definitions, lemmas and theorems. Besides, the low performance of macros used in [quantum_lemma.lean](Myyt/quantum_lemma.lean) will lead to slow compilation speed and high performance occupancy.

* It seems that I won’t modify this project for a long time, so I may not update this project even if someone offers some improvement ideas.
     