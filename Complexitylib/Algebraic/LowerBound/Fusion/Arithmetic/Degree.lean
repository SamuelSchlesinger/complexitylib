/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic
public import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Polynomial-degree fusion lower bounds

Polynomial `natDegree` is a dyadic arithmetic measure: addition is bounded by
the maximum of the input degrees, multiplication by their sum, and scalar
constants have degree zero.  The generic dyadic fusion theorem therefore gives
a multiplicative-complexity lower bound from the degree of the target.

As a concrete exact-scale example, constructing `X ^ (2 ^ n)` from `X` and
arbitrary scalar constants requires at least `n` multiplication gates.  The
statement permits an unrestricted number of free additions.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace PolynomialDegree

open Polynomial

noncomputable section

/-- Polynomial natural degree as a degree-like dyadic measure. -/
def measure
    (K : Type u)
    [Semiring K] :
    Dyadic.Measure K K[X] Polynomial.C where
  value := Polynomial.natDegree
  add_le := Polynomial.natDegree_add_le
  mul_le := by
    intro left right
    exact Polynomial.natDegree_mul_le
  constant_le_one := by
    intro scalar
    simp

/-- Polynomial degree gives a multiplication lower bound for any construction
problem whose generators have degree at most one. -/
theorem multiplication_lowerBound
    {K : Type u}
    [Semiring K]
    (problem : Problem K[X])
    (levels : Nat)
    (input_le_one : ∀ input,
      (problem.inputs input).natDegree ≤ 1)
    (target_ge : 2 ^ levels ≤ problem.target.natDegree)
    (circuit : Circuit (Arithmetic.signature K) problem.inputCount g 1)
    (constructs : problem.Constructs circuit
      (Arithmetic.interpretation Polynomial.C)) :
    levels ≤ circuit.cost (Arithmetic.multiplicationCost (K := K)) :=
  Dyadic.circuit_multiplication_lowerBound (measure K) problem levels
    input_le_one target_ge circuit constructs

/-- Construct the power `X ^ (2 ^ n)` from the single generator `X`. -/
abbrev powerProblem
    (K : Type u)
    [Semiring K]
    (n : Nat) : Problem K[X] where
  inputCount := 1
  inputs := fun _ => X
  target := X ^ (2 ^ n)

/-- Computing `X ^ (2 ^ n)` requires at least `n` multiplications, even with
arbitrary scalar constants and free additions. -/
theorem power_multiplication_lowerBound
    {K : Type u}
    [Semiring K]
    [Nontrivial K]
    (circuit : Circuit (Arithmetic.signature K) 1 g 1)
    (constructs : (powerProblem K n).Constructs circuit
      (Arithmetic.interpretation Polynomial.C)) :
    n ≤ circuit.cost (Arithmetic.multiplicationCost (K := K)) := by
  apply multiplication_lowerBound (powerProblem K n) n
  · intro input
    simp
  · simp
  · exact constructs

end

end PolynomialDegree
end Fusion
end Algebraic
