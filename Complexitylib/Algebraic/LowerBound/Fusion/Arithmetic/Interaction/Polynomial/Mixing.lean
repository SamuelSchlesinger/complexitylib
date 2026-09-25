/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Linear mixtures of monomial outputs

Apply an arbitrary coefficient matrix to a family of distinct selected
monomials.  The selected coefficient matrix of the resulting outputs is
exactly the mixing matrix, so its rank lower-bounds multiplication cost.

The unitriangular prefix matrix supplies a concrete full-rank example over
every field: output `j` is the sum of monomials `0, ..., j`.  These outputs
have strongly overlapping support, unlike the basis family itself.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Mixing

noncomputable section

variable {K : Type u} {C : Type v} {σ : Type w}

/-- Outputs obtained by using the columns of `mix` as coefficients of the
selected monomial family. -/
def targets
    [CommSemiring K]
    (exponent : Fin m → σ →₀ ℕ)
    (mix : Matrix (Fin m) (Fin m) K) :
    Fin m → MvPolynomial σ K :=
  fun output => ∑ selected : Fin m,
    MvPolynomial.monomial (exponent selected) (mix selected output)

/-- Distinct monomials make the selected coefficient matrix of mixed outputs
equal to the mixing matrix itself. -/
theorem coefficientMatrix_targets
    [CommSemiring K]
    [DecidableEq σ]
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (mix : Matrix (Fin m) (Fin m) K) :
    coefficientMatrix exponent (targets exponent mix) = mix := by
  classical
  ext selected output
  simp [coefficientMatrix, targets,
    MvPolynomial.coeff_monomial, injective.eq_iff]

/-- The rank of any monomial mixing matrix lower-bounds multiplication cost. -/
theorem matrix_rank_le_multiplicationCost
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (mix : Matrix (Fin m) (Fin m) K)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (targets exponent mix) circuit) :
    mix.rank ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  rw [← coefficientMatrix_targets exponent injective mix]
  exact coefficientMatrix_rank_le_multiplicationCost constant inputVariables
    exponent nonconstant notInput (targets exponent mix) circuit constructs

/-- A nonsingular mixing of `m` monomials still requires at least `m`
multiplications. -/
theorem circuit_multiplication_lowerBound_of_det_ne_zero
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (mix : Matrix (Fin m) (Fin m) K)
    (det_ne_zero : mix.det ≠ 0)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (targets exponent mix) circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  have rank_eq : mix.rank = m := by
    simpa using Matrix.rank_of_det_ne_zero det_ne_zero
  calc
    m = mix.rank := rank_eq.symm
    _ ≤ circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
      matrix_rank_le_multiplicationCost constant inputVariables exponent
        injective nonconstant notInput mix circuit constructs

/-- Upper-unitriangular prefix-sum mixing matrix. -/
def prefixMatrix
    (K : Type u)
    [Zero K]
    [One K]
    (m : Nat) : Matrix (Fin m) (Fin m) K :=
  fun selected output => if selected ≤ output then 1 else 0

/-- The prefix matrix is upper triangular. -/
theorem prefixMatrix_isUpperTriangular
    [Semiring K]
    (m : Nat) :
    (prefixMatrix K m).IsUpperTriangular := by
  intro row column column_lt_row
  change column < row at column_lt_row
  simp [prefixMatrix, (not_le_of_gt column_lt_row)]

@[simp] theorem prefixMatrix_diagonal
    [Semiring K]
    (m : Nat)
    (index : Fin m) :
    prefixMatrix K m index index = 1 := by
  simp [prefixMatrix]

@[simp] theorem prefixMatrix_det
    [CommRing K]
    (m : Nat) :
    (prefixMatrix K m).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (prefixMatrix_isUpperTriangular m)]
  simp

/-- Prefix sums of a selected monomial family. -/
def prefixTargets
    [CommSemiring K]
    (exponent : Fin m → σ →₀ ℕ) :
    Fin m → MvPolynomial σ K :=
  targets exponent (prefixMatrix K m)

/-- Computing all prefix sums of `m` distinct nonlinear monomials requires at
least `m` multiplications over every field. -/
theorem prefixTargets_multiplication_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (prefixTargets exponent) circuit) :
    m ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply circuit_multiplication_lowerBound_of_det_ne_zero constant
    inputVariables exponent injective nonconstant notInput (prefixMatrix K m)
  · simp
  · exact constructs

/-- Prefix-sum outputs also force total gate cost at least `m`. -/
theorem prefixTargets_gate_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (prefixTargets exponent) circuit) :
    m ≤ circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) :=
  (prefixTargets_multiplication_lowerBound constant inputVariables exponent
    injective nonconstant notInput circuit constructs).trans
      (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Prefix-sum outputs force raw circuit size at least `m`. -/
theorem prefixTargets_size_lowerBound
    [Field K]
    [DecidableEq σ]
    (constant : C → K)
    (inputVariables : Fin n → σ)
    (exponent : Fin m → σ →₀ ℕ)
    (injective : Function.Injective exponent)
    (nonconstant : ∀ selected, exponent selected ≠ 0)
    (notInput : ∀ selected input,
      exponent selected ≠ Finsupp.single (inputVariables input) 1)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) n g m)
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem inputVariables) (prefixTargets exponent) circuit) :
    m ≤ circuit.size :=
  (prefixTargets_gate_lowerBound constant inputVariables exponent injective
    nonconstant notInput circuit constructs).trans
      (Combined.circuit_gateCost_le_size circuit)

end
end Mixing
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
