/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.NNRat

/-!
# Clique-polynomial lower bounds over nonnegative rationals

The coefficient-one clique polynomial can be formed over `ℚ≥0` with exactly
the same separated support as its natural-coefficient counterpart.  The
support-only nonnegative-rational Schnorr measure therefore gives the full
central-binomial and explicit exponential addition lower bounds for circuits
with arbitrary named nonnegative-rational constants, including zero.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique
namespace NNRat

noncomputable section

/-- Coefficient-one clique polynomial over nonnegative rationals. -/
def polynomial
    (vertexCount cliqueSize : Nat) :
    MvPolynomial (Fin (vertexCount * vertexCount)) ℚ≥0 :=
  ∑ exponent ∈ cliqueSupport vertexCount cliqueSize,
    MvPolynomial.monomial exponent 1

@[simp] theorem polynomial_support
    (vertexCount cliqueSize : Nat) :
    (polynomial vertexCount cliqueSize).support =
      cliqueSupport vertexCount cliqueSize := by
  classical
  rw [polynomial, ExactSupport.support_finset_sum]
  simp_rw [MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : ℚ≥0) ≠ 0)]
  exact Finset.biUnion_singleton_eq_self

theorem card_polynomial_support
    (vertexCount cliqueSize : Nat) :
    (polynomial vertexCount cliqueSize).support.card =
      Nat.choose vertexCount cliqueSize := by
  simp

/-- Every nonnegative-rational polynomial with clique support needs one fewer
addition than its number of monomials. -/
theorem circuit_addition_lowerBound_of_support_eq
    (constant : K → ℚ≥0)
    (target : MvPolynomial (Fin (vertexCount * vertexCount)) ℚ≥0)
    (supportEqual : target.support =
      cliqueSupport vertexCount cliqueSize)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X, target := target } :
        Problem
          (MvPolynomial (Fin (vertexCount * vertexCount)) ℚ≥0)).Constructs
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
    Closure.Weighted.NNRat.circuit_addition_lowerBound_of_isSeparated
      constant target targetSeparated circuit constructs
  simpa [supportEqual] using bound

/-- Addition lower bound for the nonnegative-rational clique polynomial. -/
theorem circuit_addition_lowerBound
    (constant : K → ℚ≥0)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial vertexCount cliqueSize } :
        Problem
          (MvPolynomial (Fin (vertexCount * vertexCount)) ℚ≥0)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  circuit_addition_lowerBound_of_support_eq constant
    (polynomial vertexCount cliqueSize) (polynomial_support _ _)
    circuit constructs

/-- Central-binomial addition lower bound over nonnegative rationals. -/
theorem central_circuit_addition_lowerBound
    (constant : K → ℚ≥0)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℚ≥0)).Constructs
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

/-- Explicit exponential middle-layer lower bound over nonnegative
rationals. -/
theorem central_circuit_exponential_lowerBound
    (constant : K → ℚ≥0)
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
            (Fin ((2 * halfVertices) * (2 * halfVertices))) ℚ≥0)).Constructs
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
end NNRat
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
