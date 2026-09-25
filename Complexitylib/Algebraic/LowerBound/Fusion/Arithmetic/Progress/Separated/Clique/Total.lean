/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Combined
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MonotonePolynomial.Exact
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Clique.Exact

/-!
# Total-gate bounds for clique polynomials

Schnorr separation controls additions in a clique-polynomial circuit.  Exact
support Fusion independently controls multiplications when the supports at
multiplication inputs have bounded width.  This module proves the elementary
support side conditions for clique monomials and combines both certificates
into a single lower bound on all nonconstant arithmetic gates.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Clique

noncomputable section

/-- Total degree of an ordered-clique exponent.  Loops are included, so a
clique on `k` vertices has degree `k * k`. -/
theorem cliqueExponent_sum
    (vertices : Finset (Fin vertexCount)) :
    (cliqueExponent vertices).sum (fun _ multiplicity => multiplicity) =
      vertices.card * vertices.card := by
  unfold cliqueExponent
  rw [Finsupp.sum_indicator_index
    (s := edgeSet vertices) (fun _ => (1 : Nat))
    (h := fun _ multiplicity => multiplicity) (by intros; rfl)]
  simp [edgeSet]

/-- A positive-size clique support contains no constant exponent. -/
theorem zero_not_mem_cliqueSupport
    (positive : 0 < cliqueSize) :
    0 ∉ cliqueSupport vertexCount cliqueSize := by
  intro present
  obtain ⟨vertices, verticesPresent, equal⟩ :=
    Finset.mem_map.mp present
  have verticesCard :=
    (Finset.mem_powersetCard.mp verticesPresent).2
  have sumEqual := congrArg
    (fun exponent : Fin (vertexCount * vertexCount) →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) equal
  change (cliqueExponent vertices).sum
    (fun _ multiplicity => multiplicity) = _ at sumEqual
  rw [cliqueExponent_sum, verticesCard] at sumEqual
  simp at sumEqual
  have productPositive : 0 < cliqueSize * cliqueSize :=
    Nat.mul_pos positive positive
  omega

/-- For clique size at least two, no clique exponent is the exponent of one
input variable. -/
theorem cliqueSupport_disjoint_single
    (two_le : 2 ≤ cliqueSize)
    (coordinate : Fin (vertexCount * vertexCount)) :
    Disjoint (cliqueSupport vertexCount cliqueSize)
      {Finsupp.single coordinate 1} := by
  rw [Finset.disjoint_left]
  intro candidate targetPresent variablePresent
  obtain ⟨vertices, verticesPresent, targetEqual⟩ :=
    Finset.mem_map.mp targetPresent
  have verticesCard :=
    (Finset.mem_powersetCard.mp verticesPresent).2
  have variableEqual : candidate = Finsupp.single coordinate 1 :=
    Finset.mem_singleton.mp variablePresent
  have exponentEqual :
      cliqueExponent vertices = Finsupp.single coordinate 1 :=
    targetEqual.trans variableEqual
  have sumEqual := congrArg
    (fun exponent : Fin (vertexCount * vertexCount) →₀ ℕ =>
      exponent.sum (fun _ multiplicity => multiplicity)) exponentEqual
  rw [cliqueExponent_sum, verticesCard] at sumEqual
  simp at sumEqual
  have four_le : 4 ≤ cliqueSize * cliqueSize := by
    simpa using Nat.mul_le_mul two_le two_le
  omega

namespace Exact

section Bounds

variable [CommSemiring R] [Nontrivial R]
variable [NoZeroDivisors R]
variable [Algebraic.Fusion.Arithmetic.ExactSupport.ZeroSumFree R]

omit [NoZeroDivisors R] in
/-- A positive-size exact-semiring clique polynomial has no constant
monomial. -/
theorem zero_not_mem_polynomial_support
    (positive : 0 < cliqueSize) :
    0 ∉ (polynomial R vertexCount cliqueSize).support := by
  rw [polynomial_support]
  exact zero_not_mem_cliqueSupport positive

omit [NoZeroDivisors R] in
/-- When the clique size is at least two, the target support is disjoint from
every individual input-variable support. -/
theorem polynomial_support_disjoint_X
    (two_le : 2 ≤ cliqueSize)
    (coordinate : Fin (vertexCount * vertexCount)) :
    Disjoint (polynomial R vertexCount cliqueSize).support
      (MvPolynomial.X coordinate :
        MvPolynomial (Fin (vertexCount * vertexCount)) R).support := by
  rw [polynomial_support, MvPolynomial.support_X]
  exact cliqueSupport_disjoint_single two_le coordinate

/-- Exact-support Fusion gives a multiplication lower bound for the clique
polynomial under the circuit-local support-width promise. -/
theorem circuit_multiplication_lowerBound
    (constant : K → R)
    (two_le : 2 ≤ cliqueSize)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) g 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial R vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin (vertexCount * vertexCount) →
        MvPolynomial (Fin (vertexCount * vertexCount)) R)
      width) :
    Nat.choose vertexCount cliqueSize ⌈/⌉ (width * width) ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := K)) := by
  simpa using
    MonotonePolynomial.Exact.circuit_multiplication_lowerBound_of_disjoint
      constant
      (MvPolynomial.X : Fin (vertexCount * vertexCount) →
        MvPolynomial (Fin (vertexCount * vertexCount)) R)
      (polynomial R vertexCount cliqueSize)
      (polynomial_support_disjoint_X two_le)
      (zero_not_mem_polynomial_support (by omega))
      width positiveWidth circuit constructs widthBound

/-- Addition and multiplication Fusion certificates combine into one lower
bound for all nonconstant gates in a clique-polynomial circuit. -/
theorem circuit_gate_lowerBound
    (constant : K → R)
    (two_le : 2 ≤ cliqueSize)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) g 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial R vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin (vertexCount * vertexCount) →
        MvPolynomial (Fin (vertexCount * vertexCount)) R)
      width) :
    (Nat.choose vertexCount cliqueSize - 1) +
        (Nat.choose vertexCount cliqueSize ⌈/⌉ (width * width)) ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) := by
  exact Combined.circuit_gate_lowerBound_of_components circuit _ _
    (circuit_addition_lowerBound constant circuit constructs)
    (circuit_multiplication_lowerBound constant two_le width positiveWidth
      circuit constructs widthBound)

/-- The combined lower bound also applies to raw circuit size, which may
additionally count scalar-constant gates. -/
theorem circuit_size_lowerBound
    (constant : K → R)
    (two_le : 2 ≤ cliqueSize)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        (vertexCount * vertexCount) g 1)
    (constructs :
      ({ inputCount := vertexCount * vertexCount,
          inputs := MvPolynomial.X,
          target := polynomial R vertexCount cliqueSize } :
        Problem (MvPolynomial (Fin (vertexCount * vertexCount)) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin (vertexCount * vertexCount))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin (vertexCount * vertexCount) →
        MvPolynomial (Fin (vertexCount * vertexCount)) R)
      width) :
    (Nat.choose vertexCount cliqueSize - 1) +
        (Nat.choose vertexCount cliqueSize ⌈/⌉ (width * width)) ≤
      circuit.size := by
  exact (circuit_gate_lowerBound constant two_le width positiveWidth
    circuit constructs widthBound).trans
      (Combined.circuit_gateCost_le_size circuit)

/-- Middle-layer specialization of the combined total-gate lower bound. -/
theorem central_circuit_gate_lowerBound
    (constant : K → R)
    (halfVertices : Nat)
    (two_le : 2 ≤ halfVertices)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) g 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial R (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin ((2 * halfVertices) * (2 * halfVertices)))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin ((2 * halfVertices) * (2 * halfVertices)) →
        MvPolynomial
          (Fin ((2 * halfVertices) * (2 * halfVertices))) R)
      width) :
    (Nat.centralBinom halfVertices - 1) +
        (Nat.centralBinom halfVertices ⌈/⌉ (width * width)) ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) := by
  simpa [Nat.centralBinom] using
    circuit_gate_lowerBound constant two_le width positiveWidth
      circuit constructs widthBound

/-- The middle-layer clique family yields an explicit exponential
support-width versus total-gate tradeoff. -/
theorem central_four_pow_lt_mul_width_sq_gateCost
    (constant : K → R)
    (halfVertices : Nat)
    (halfVerticesBig : 4 ≤ halfVertices)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) g 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial R (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin ((2 * halfVertices) * (2 * halfVertices)))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin ((2 * halfVertices) * (2 * halfVertices)) →
        MvPolynomial
          (Fin ((2 * halfVertices) * (2 * halfVertices))) R)
      width) :
    4 ^ halfVertices <
      halfVertices * ((width * width) *
        circuit.cost (Algebraic.Arithmetic.gateCost (K := K))) := by
  have capacityPositive : 0 < width * width :=
    Nat.mul_pos positiveWidth positiveWidth
  have centralLeMultiplication : Nat.centralBinom halfVertices ≤
      (width * width) *
        circuit.cost
          (Algebraic.Arithmetic.multiplicationCost (K := K)) :=
    (ceilDiv_le_iff_le_mul capacityPositive).1 (by
      simpa [Nat.centralBinom] using
        circuit_multiplication_lowerBound constant
          (by omega : 2 ≤ halfVertices) width positiveWidth
          circuit constructs widthBound)
  have centralLeGate : Nat.centralBinom halfVertices ≤
      (width * width) *
        circuit.cost (Algebraic.Arithmetic.gateCost (K := K)) :=
    centralLeMultiplication.trans
      (Nat.mul_le_mul_left (width * width)
        (Combined.circuit_multiplicationCost_le_gateCost circuit))
  exact
    (Nat.four_pow_lt_mul_centralBinom halfVertices halfVerticesBig).trans_le
      (Nat.mul_le_mul_left halfVertices centralLeGate)

/-- Raw circuit size satisfies the same exponential support-width tradeoff. -/
theorem central_four_pow_lt_mul_width_sq_size
    (constant : K → R)
    (halfVertices : Nat)
    (halfVerticesBig : 4 ≤ halfVertices)
    (width : Nat)
    (positiveWidth : 0 < width)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature K)
        ((2 * halfVertices) * (2 * halfVertices)) g 1)
    (constructs :
      ({ inputCount := (2 * halfVertices) * (2 * halfVertices),
          inputs := MvPolynomial.X,
          target := polynomial R (2 * halfVertices) halfVertices } :
        Problem
          (MvPolynomial
            (Fin ((2 * halfVertices) * (2 * halfVertices))) R)).Constructs
          circuit
          (General.polynomialInterpretation constant
            (Fin ((2 * halfVertices) * (2 * halfVertices)))))
    (widthBound : MonotonePolynomial.Exact.MultiplicationSupportWidthAtMost
      constant circuit
      (MvPolynomial.X : Fin ((2 * halfVertices) * (2 * halfVertices)) →
        MvPolynomial
          (Fin ((2 * halfVertices) * (2 * halfVertices))) R)
      width) :
    4 ^ halfVertices <
      halfVertices * ((width * width) * circuit.size) := by
  exact (central_four_pow_lt_mul_width_sq_gateCost constant halfVertices
    halfVerticesBig width positiveWidth circuit constructs widthBound).trans_le
      (Nat.mul_le_mul_left halfVertices
        (Nat.mul_le_mul_left (width * width)
          (Combined.circuit_gateCost_le_size circuit)))

end Bounds

end Exact
end
end Clique
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
