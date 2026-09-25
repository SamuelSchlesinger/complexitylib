/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Layer

/-!
# Multi-output squarefree-monomial lower bounds

Enumerate every squarefree degree-`k` monomial in `n` variables and request
them as simultaneous outputs.  The selected-coefficient Fusion theorem gives
an exact `choose n k` multiplication lower bound over every field, with
arbitrary constants and cancellation.

At the middle layer this is a central-binomial, hence exponential, direct-sum
bound.  This is explicitly a multi-output theorem: the output family itself
has exponential cardinality.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Squarefree

noncomputable section

open MonotonePolynomial

variable {K : Type u} {C : Type v}

/-- Canonical finite enumeration of the squarefree degree-`k` layer. -/
def indexEquiv (n k : Nat) :
    Layer.Index n k ≃ Fin (Nat.choose n k) :=
  Fintype.equivFinOfCardEq (Layer.card_index n k)

/-- Squarefree degree-`k` exponent selected by an output index. -/
def exponent
    (n k : Nat) :
    Fin (Nat.choose n k) → Fin n →₀ ℕ :=
  fun output => Layer.exponent ((indexEquiv n k).symm output)

/-- The enumerated squarefree exponents are pairwise distinct. -/
theorem exponent_injective (n k : Nat) :
    Function.Injective (exponent n k) :=
  Layer.exponent_injective.comp (indexEquiv n k).symm.injective

/-- Positive-degree squarefree exponents are nonconstant. -/
theorem exponent_ne_zero
    (positive : 0 < k)
    (output : Fin (Nat.choose n k)) :
    exponent n k output ≠ 0 := by
  intro equal
  have sumEqual := congrArg
    (fun candidate : Fin n →₀ ℕ =>
      candidate.sum (fun _ multiplicity => multiplicity)) equal
  change (Layer.exponent ((indexEquiv n k).symm output)).sum
      (fun _ multiplicity => multiplicity) = _ at sumEqual
  rw [Layer.exponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- A squarefree exponent of degree at least two is not any free input
variable exponent. -/
theorem exponent_ne_input
    (two_le : 2 ≤ k)
    (output : Fin (Nat.choose n k))
    (input : Fin n) :
    exponent n k output ≠ Finsupp.single input 1 := by
  intro equal
  have sumEqual := congrArg
    (fun candidate : Fin n →₀ ℕ =>
      candidate.sum (fun _ multiplicity => multiplicity)) equal
  change (Layer.exponent ((indexEquiv n k).symm output)).sum
      (fun _ multiplicity => multiplicity) = _ at sumEqual
  rw [Layer.exponent_sum] at sumEqual
  simp at sumEqual
  omega

/-- All squarefree degree-`k` monomials, enumerated as circuit outputs. -/
def targets
    (K : Type u)
    [CommSemiring K]
    (n k : Nat) :
    Fin (Nat.choose n k) → MvPolynomial (Fin n) K :=
  Polynomial.targets (K := K) (exponent n k)

/-- Common input family for squarefree multi-output circuits. -/
abbrev inputProblem
    (K : Type u)
    [CommSemiring K]
    (n : Nat) : Problem (MvPolynomial (Fin n) K) :=
  Polynomial.inputProblem (K := K) (fun input : Fin n => input)

/-- Producing all squarefree degree-`k` monomials requires one multiplication
per monomial. -/
theorem circuit_multiplication_lowerBound
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n k) circuit) :
    Nat.choose n k ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  apply Polynomial.circuit_multiplication_lowerBound
    constant (fun input : Fin n => input) (exponent n k)
    (exponent_injective n k)
  · exact fun output => exponent_ne_zero (by omega) output
  · exact fun output input => exponent_ne_input two_le output input
  · exact constructs

/-- Total nonconstant arithmetic-gate cost is at least the squarefree layer
cardinality. -/
theorem circuit_gate_lowerBound
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n k) circuit) :
    Nat.choose n k ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) :=
  (circuit_multiplication_lowerBound constant n k two_le circuit
    constructs).trans (Combined.circuit_multiplicationCost_le_gateCost circuit)

/-- Raw circuit size is at least the squarefree layer cardinality. -/
theorem circuit_size_lowerBound
    [Field K]
    (constant : C → K)
    (n k : Nat)
    (two_le : 2 ≤ k)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      n (Nat.choose n k))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K n) (targets K n k) circuit) :
    Nat.choose n k ≤ circuit.size :=
  (circuit_gate_lowerBound constant n k two_le circuit constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

/-- The middle squarefree layer forces central-binomial multiplication cost. -/
theorem centralBinom_multiplication_lowerBound
    [Field K]
    (constant : C → K)
    (n : Nat)
    (two_le : 2 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K (2 * n)) (targets K (2 * n) n) circuit) :
    Nat.centralBinom n ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  simpa [Nat.centralBinom] using
    circuit_multiplication_lowerBound constant (2 * n) n two_le circuit
      constructs

/-- Explicit exponential multiplication lower bound for all middle-layer
outputs. -/
theorem four_pow_lt_mul_multiplicationCost
    [Field K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K (2 * n)) (targets K (2 * n) n) circuit) :
    4 ^ n < n * circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      (centralBinom_multiplication_lowerBound constant n (by omega) circuit
        constructs))

/-- Explicit exponential raw-size lower bound for all middle-layer outputs. -/
theorem four_pow_lt_mul_size
    [Field K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) (Nat.centralBinom n))
    (constructs : Multiple.Constructs
      (constant := fun scalar => MvPolynomial.C (constant scalar))
      (inputProblem K (2 * n)) (targets K (2 * n) n) circuit) :
    4 ^ n < n * circuit.size :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      ((centralBinom_multiplication_lowerBound constant n (by omega) circuit
        constructs).trans
          ((Combined.circuit_multiplicationCost_le_gateCost circuit).trans
            (Combined.circuit_gateCost_le_size circuit))))

end
end Squarefree
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
