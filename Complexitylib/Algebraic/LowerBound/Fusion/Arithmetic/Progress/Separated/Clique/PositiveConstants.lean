/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.PositiveConstants

/-!
# Clique-polynomial lower bounds with positive constants

This module combines the clique-support separation theorem with the generic
positive-constant Schnorr measure.  The resulting bounds allow an arbitrary
alphabet of free named constants, provided their natural interpretation is
strictly positive.  Thus positive coefficients and reusable positive scalar
gates do not weaken the clique-polynomial addition lower bound.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique
namespace PositiveConstants

noncomputable section

/-- Every polynomial with clique support needs one fewer addition than its
number of monomials, even when the circuit has free positive constants. -/
theorem circuit_addition_lowerBound_of_support_eq
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (target : MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)
    (supportEqual : target.support =
      cliqueSupport vertexCount cliqueSize)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) := by
  have targetSeparated : IsSeparated target.support target.support := by
    rw [supportEqual]
    exact cliqueSupport_isSeparated vertexCount cliqueSize
  have bound :=
    Closure.PositiveConstants.circuit_addition_lowerBound_of_isSeparated
      constant positive target targetSeparated circuit constructs
  simpa [supportEqual] using bound

/-- Schnorr's addition lower bound for the clique polynomial, allowing free
positive named constants. -/
theorem circuit_addition_lowerBound
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) ℕ)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  circuit_addition_lowerBound_of_support_eq constant positive
    (polynomial vertexCount cliqueSize) (polynomial_support _ _)
    circuit constructs

/-- The central-binomial clique family retains its addition bound in the
presence of arbitrary positive constants. -/
theorem central_circuit_addition_lowerBound
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℕ)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin ((2 * halfVertices) * (2 * halfVertices))))) :
    Nat.centralBinom halfVertices - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) := by
  simpa [Nat.centralBinom] using
    (circuit_addition_lowerBound constant positive
      (vertexCount := 2 * halfVertices)
      (cliqueSize := halfVertices) circuit constructs)

/-- Explicit exponential addition lower bound for the middle clique layer,
still valid for circuits with free positive named constants. -/
theorem central_circuit_exponential_lowerBound
    (constant : K → ℕ)
    (positive : ∀ scalar, 0 < constant scalar)
    (halfVerticesBig : 4 ≤ halfVertices)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℕ)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin ((2 * halfVertices) * (2 * halfVertices))))) :
    4 ^ halfVertices <
      halfVertices *
        (circuit.cost
          (Algebraic.Arithmetic.additionCost (K := K)) + 1) := by
  have costBound := central_circuit_addition_lowerBound
    constant positive circuit constructs
  have centralLe : Nat.centralBinom halfVertices ≤
      circuit.cost
          (Algebraic.Arithmetic.additionCost (K := K)) + 1 := by
    have centralPositive := Nat.centralBinom_pos halfVertices
    omega
  exact (Nat.four_pow_lt_mul_centralBinom halfVertices halfVerticesBig).trans_le
    (Nat.mul_le_mul_left halfVertices centralLe)

end
end PositiveConstants
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
