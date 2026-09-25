/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Mixing
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Squarefree

/-!
# Mixed squarefree-layer output bounds

Specialize monomial mixing to the squarefree degree-`k` layer.  Any mixing
matrix contributes its full rank as a multiplication lower bound.  In
particular, the unitriangular prefix sums of the layer require `choose n k`
multiplications over every field.

For the middle layer this is an exponential multi-output lower bound whose
outputs have nested, highly overlapping supports.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Squarefree
namespace Mixing

noncomputable section

variable {K : Type u} {C : Type v}

/-- A matrix mixture of all squarefree degree-`k` monomials. -/
def targets
    (K : Type u)
    [CommSemiring K]
    (n k : Nat)
    (mix : Matrix (Fin (Nat.choose n k)) (Fin (Nat.choose n k)) K) :
    Fin (Nat.choose n k) → MvPolynomial (Fin n) K :=
  Polynomial.Mixing.targets (Squarefree.exponent n k) mix

/-- Mixing-matrix rank lower-bounds multiplication cost for the squarefree
layer. -/
theorem matrix_rank_le_multiplicationCost
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (mix : Matrix (Fin (Nat.choose n k)) (Fin (Nat.choose n k)) K)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K n) (targets K n k mix) circuit) :
    mix.rank ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Polynomial.Mixing.matrix_rank_le_multiplicationCost constant
    (fun input : Fin n => input) (Squarefree.exponent n k)
    (Squarefree.exponent_injective n k)
  · exact fun output => Squarefree.exponent_ne_zero (by omega) output
  · exact fun output input =>
      Squarefree.exponent_ne_input two_le output input
  · exact constructs

/-- Every nonsingular mixing of the squarefree layer needs one multiplication
per layer monomial. -/
theorem circuit_multiplication_lowerBound_of_det_ne_zero
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (mix : Matrix (Fin (Nat.choose n k)) (Fin (Nat.choose n k)) K)
    (det_ne_zero : mix.det ≠ 0)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K n) (targets K n k mix) circuit) :
    Nat.choose n k ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Polynomial.Mixing.circuit_multiplication_lowerBound_of_det_ne_zero
    constant (fun input : Fin n => input) (Squarefree.exponent n k)
    (Squarefree.exponent_injective n k)
  · exact fun output => Squarefree.exponent_ne_zero (by omega) output
  · exact fun output input =>
      Squarefree.exponent_ne_input two_le output input
  · exact det_ne_zero
  · exact constructs

/-- Unitriangular prefix sums of the squarefree layer. -/
def prefixTargets
    (K : Type u)
    [CommSemiring K]
    (n k : Nat) :
    Fin (Nat.choose n k) → MvPolynomial (Fin n) K :=
  Polynomial.Mixing.prefixTargets (K := K) (Squarefree.exponent n k)

/-- Computing every prefix sum of the squarefree degree-`k` layer requires
`choose n k` multiplications. -/
theorem prefixTargets_multiplication_lowerBound
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K n) (prefixTargets K n k) circuit) :
    Nat.choose n k ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Polynomial.Mixing.prefixTargets_multiplication_lowerBound constant
    (fun input : Fin n => input) (Squarefree.exponent n k)
    (Squarefree.exponent_injective n k)
  · exact fun output => Squarefree.exponent_ne_zero (by omega) output
  · exact fun output input =>
      Squarefree.exponent_ne_input two_le output input
  · exact constructs

/-- Prefix squarefree outputs force raw size at least the layer cardinality. -/
theorem prefixTargets_size_lowerBound
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K n) (prefixTargets K n k) circuit) :
    Nat.choose n k ≤ circuit.size :=
  (prefixTargets_multiplication_lowerBound constant n k two_le circuit
    constructs).trans
      ((Combined.circuit_multiplicationCost_le_gateCost circuit).trans
        (Combined.circuit_gateCost_le_size circuit))

/-- Middle-layer prefix outputs require central-binomial multiplication cost. -/
theorem centralBinom_prefixTargets_multiplication_lowerBound
    [Field K]
    (constant : C → K)
    (n : Nat)
    (two_le : 2 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K (2 * n))
      (prefixTargets K (2 * n) n) circuit) :
    Nat.centralBinom n ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  simpa [Nat.centralBinom] using
    prefixTargets_multiplication_lowerBound constant (2 * n) n two_le
      circuit constructs

/-- Explicit exponential cost bound for nested middle-layer prefix outputs. -/
theorem four_pow_lt_mul_multiplicationCost
    [Field K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K (2 * n))
      (prefixTargets K (2 * n) n) circuit) :
    4 ^ n < n * circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      (centralBinom_prefixTargets_multiplication_lowerBound constant n
        (by omega) circuit constructs))

/-- Explicit exponential raw-size bound for nested middle-layer prefixes. -/
theorem four_pow_lt_mul_size
    [Field K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (Squarefree.inputProblem K (2 * n))
      (prefixTargets K (2 * n) n) circuit) :
    4 ^ n < n * circuit.size :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      ((centralBinom_prefixTargets_multiplication_lowerBound constant n
        (by omega) circuit constructs).trans
          ((Combined.circuit_multiplicationCost_le_gateCost circuit).trans
            (Combined.circuit_gateCost_le_size circuit))))

end
end Mixing
end Squarefree
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
