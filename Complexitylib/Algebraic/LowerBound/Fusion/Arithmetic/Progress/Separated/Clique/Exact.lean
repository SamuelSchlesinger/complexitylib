/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure.Weighted.Exact

/-!
# Clique-polynomial bounds over exact-support semirings

The coefficient-one clique polynomial and its addition lower bounds are
uniform over every nontrivial zero-sum-free commutative semiring without zero
divisors.  This single family specializes to natural and nonnegative-rational
coefficients and remains compatible with arbitrary named constants, including
zero.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique
namespace Exact

noncomputable section

/-- Coefficient-one clique polynomial over a selected commutative semiring. -/
def polynomial
    (R : Type u)
    [CommSemiring R]
    (vertexCount cliqueSize : Nat) :
    MvPolynomial (Fin (vertexCount * vertexCount)) R :=
  ∑ exponent ∈ cliqueSupport vertexCount cliqueSize,
    MvPolynomial.monomial exponent 1

@[simp] theorem polynomial_support
    (R : Type u)
    [CommSemiring R] [Nontrivial R]
    [ExactSupport.ZeroSumFree R]
    (vertexCount cliqueSize : Nat) :
    (polynomial R vertexCount cliqueSize).support =
      cliqueSupport vertexCount cliqueSize := by
  classical
  rw [polynomial, ExactSupport.support_finset_sum]
  simp_rw [MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : R) ≠ 0)]
  exact Finset.biUnion_singleton_eq_self

theorem card_polynomial_support
    (R : Type u)
    [CommSemiring R] [Nontrivial R]
    [ExactSupport.ZeroSumFree R]
    (vertexCount cliqueSize : Nat) :
    (polynomial R vertexCount cliqueSize).support.card =
      Nat.choose vertexCount cliqueSize := by
  simp

section Bounds

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R] [ExactSupport.ZeroSumFree R]

/-- Every polynomial with clique support needs one fewer addition than its
number of monomials over any exact-support coefficient semiring. -/
theorem circuit_addition_lowerBound_of_support_eq
    (constant : K → R)
    (target : MvPolynomial (Fin (vertexCount * vertexCount)) R)
    (supportEqual : target.support =
      cliqueSupport vertexCount cliqueSize)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X, target := target } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) R)).Constructs
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
    Closure.Weighted.Exact.circuit_addition_lowerBound_of_isSeparated
      constant target targetSeparated circuit constructs
  simpa [supportEqual] using bound

/-- Addition lower bound for the exact-semiring clique polynomial. -/
theorem circuit_addition_lowerBound
    (constant : K → R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial R vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount)))) :
    Nat.choose vertexCount cliqueSize - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := K)) :=
  circuit_addition_lowerBound_of_support_eq constant
    (polynomial R vertexCount cliqueSize) (polynomial_support R _ _)
    circuit constructs

/-- Central-binomial addition lower bound over every exact-support semiring. -/
theorem central_circuit_addition_lowerBound
    (constant : K → R)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial R (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) R)).Constructs
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

/-- Explicit exponential middle-layer lower bound over every exact-support
semiring. -/
theorem central_circuit_exponential_lowerBound
    (constant : K → R)
    (halfVerticesBig : 4 ≤ halfVertices)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial R (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) R)).Constructs
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

end Bounds

end
end Exact
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
