/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Addition

/-!
# Clique-polynomial lower bounds with arbitrary natural constants

Weighted Schnorr closure permits zero-weight substitutions, so it remains a
valid addition measure even when the circuit has free named constants whose
natural values may vanish.  Combining it with clique-support separation gives
the full clique-polynomial lower-bound family without any positivity premise
on constants.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique
namespace NaturalConstants

noncomputable section

/-- Every polynomial with clique support needs one fewer addition than its
number of monomials, for any natural interpretation of named constants. -/
theorem circuit_addition_lowerBound_of_support_eq
    (constant : K → ℕ)
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
    Closure.Weighted.Addition.circuit_addition_lowerBound_of_isSeparated
      constant target targetSeparated circuit constructs
  simpa [supportEqual] using bound

/-- Schnorr's addition lower bound for the clique polynomial with arbitrary
natural constants, including zero. -/
theorem circuit_addition_lowerBound
    (constant : K → ℕ)
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
  circuit_addition_lowerBound_of_support_eq constant
    (polynomial vertexCount cliqueSize) (polynomial_support _ _)
    circuit constructs

/-- The central-binomial clique family retains its addition bound for every
natural constant alphabet. -/
theorem central_circuit_addition_lowerBound
    (constant : K → ℕ)
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
    (circuit_addition_lowerBound constant
      (vertexCount := 2 * halfVertices)
      (cliqueSize := halfVertices) circuit constructs)

/-- Explicit exponential addition lower bound for the middle clique layer,
valid even with free zero constants. -/
theorem central_circuit_exponential_lowerBound
    (constant : K → ℕ)
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
    constant circuit constructs
  have centralLe : Nat.centralBinom halfVertices ≤
      circuit.cost
          (Algebraic.Arithmetic.additionCost (K := K)) + 1 := by
    have centralPositive := Nat.centralBinom_pos halfVertices
    omega
  exact (Nat.four_pow_lt_mul_centralBinom halfVertices halfVerticesBig).trans_le
    (Nat.mul_le_mul_left halfVertices centralLe)

end
end NaturalConstants
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
