/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.Residue
public import Complexitylib.Algebraic.MassProduction.HighRate.PolynomialSupport
public import Complexitylib.Algebraic.MassProduction.Scheduler

/-!
# Line parity for common-zero-block monomials

Splitting every exponent at the end of a common zero block factors its
affine-line restriction as a low-degree polynomial times a Frobenius power.
The resulting residue gap excludes positive multiples of `q - 1` from the
support. Summing over the field therefore gives zero on every affine line.
This proof uses Frobenius directly and does not assume Lucas' theorem.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators LinearAlgebra.Projectivization

variable {K Coordinate : Type*} [Field K] [Fintype Coordinate]

/-- The evaluation of a reduced multivariate monomial. -/
def monomialValue (degrees : Coordinate → Nat) (point : Coordinate → K) : K :=
  ∏ coordinate, point coordinate ^ degrees coordinate

/-- The univariate polynomial obtained by restricting a monomial to a line. -/
noncomputable def lineMonomial (degrees : Coordinate → Nat)
    (center direction : Coordinate → K) : Polynomial K :=
  ∏ coordinate, lineCoordinate center direction coordinate ^ degrees coordinate

/-- Evaluation commutes with affine-line restriction. -/
theorem lineMonomial_eval (degrees : Coordinate → Nat)
    (center direction : Coordinate → K) (parameter : K) :
    (lineMonomial degrees center direction).eval parameter =
      monomialValue degrees (fun coordinate => center coordinate + direction coordinate * parameter) := by
  simp [lineMonomial, monomialValue, lineCoordinate, Polynomial.eval_prod]

/-- Restriction cannot increase the total monomial degree. -/
theorem lineMonomialNatDegree_le (degrees : Coordinate → Nat)
    (center direction : Coordinate → K) :
    (lineMonomial degrees center direction).natDegree ≤ ∑ coordinate, degrees coordinate := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply Finset.sum_le_sum
  intro coordinate _
  simpa using Polynomial.natDegree_pow_le_of_le (degrees coordinate)
    (natDegree_lineCoordinate_le center direction coordinate)

/-- Splitting exponents modulo a power of two separates the low-degree
factor from a Frobenius power. -/
theorem lineMonomialSplit (degrees : Coordinate → Nat)
    (center direction : Coordinate → K) (width : Nat) :
    lineMonomial degrees center direction =
      lineMonomial (fun coordinate => degrees coordinate % 2 ^ width) center direction *
        (lineMonomial (fun coordinate => degrees coordinate / 2 ^ width) center direction) ^
          2 ^ width := by
  classical
  unfold lineMonomial
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro coordinate _
  rw [← pow_mul, Nat.mul_comm (degrees coordinate / 2 ^ width),
    ← pow_add, Nat.mod_add_div]

/-- A common zero block forbids every positive multiple of `q - 1` in the
support of the affine-line restriction. -/
theorem lineMonomialNoPositiveMultiple
    [Fintype K] [CharP K 2] [Nonempty Coordinate]
    (degrees : Coordinate → Nat) (center direction : Coordinate → K)
    (width start blockWidth : Nat) (fieldCard : Fintype.card K = 2 ^ width)
    (blockPositive : 0 < blockWidth) (blockFits : start + blockWidth ≤ width)
    (dimensionFits : Fintype.card Coordinate ≤ 2 ^ blockWidth)
    (reduced : ∀ coordinate, degrees coordinate < 2 ^ width)
    (zeroBlock : CommonZeroBlock degrees start blockWidth)
    (exponent : Nat) (inSupport : exponent ∈ (lineMonomial degrees center direction).support)
    (positive : 0 < exponent) :
    ¬ (Fintype.card K - 1) ∣ exponent := by
  have degreesSmall (coordinate : Coordinate) : degrees coordinate < 2 ^ width - 1 :=
    exponentLtCardPredOfZeroBlock width start blockWidth (degrees coordinate)
      blockPositive blockFits (reduced coordinate) (zeroBlock coordinate)
  have sumSmall : (∑ coordinate, degrees coordinate) <
      Fintype.card Coordinate * (2 ^ width - 1) := by
    calc
      _ < ∑ _coordinate : Coordinate, (2 ^ width - 1) := by
        apply Finset.sum_lt_sum (fun coordinate _ => (degreesSmall coordinate).le)
        exact ⟨Classical.arbitrary Coordinate, Finset.mem_univ _, degreesSmall _⟩
      _ = _ := by simp
  have exponentSmall : exponent < Fintype.card Coordinate * (2 ^ width - 1) :=
    ((Polynomial.le_natDegree_of_mem_supp exponent inSupport).trans
      (lineMonomialNatDegree_le degrees center direction)).trans_lt sumSmall
  have residueLe := residueLeNatDegreeOfMemSupportMulPowTwo
    (lineMonomial (fun coordinate => degrees coordinate % 2 ^ (start + blockWidth)) center direction)
    (lineMonomial (fun coordinate => degrees coordinate / 2 ^ (start + blockWidth)) center direction)
    (start + blockWidth) exponent (by
      rwa [← lineMonomialSplit degrees center direction (start + blockWidth)])
  have residueSum := residueLe.trans
    (lineMonomialNatDegree_le _ center direction)
  have residueGap : exponent % 2 ^ (start + blockWidth) + Fintype.card Coordinate ≤
      2 ^ (start + blockWidth) :=
    (Nat.add_le_add_right residueSum _).trans
      (commonZeroBlockSumResidueGap degrees start blockWidth zeroBlock dimensionFits)
  rw [fieldCard]
  exact notDvdOfResidueGap (2 ^ width) (Fintype.card Coordinate) (2 ^ (start + blockWidth))
    exponent (Nat.pow_dvd_pow 2 blockFits) positive exponentSmall residueGap

private theorem sumPowEqZero [Fintype K] (exponent : Nat)
    (notMultiple : exponent ≠ 0 → ¬ (Fintype.card K - 1) ∣ exponent) :
    ∑ value : K, value ^ exponent = 0 := by
  classical
  by_cases zero : exponent = 0
  · simp [zero]
  let embedding : Kˣ ↪ K := ⟨fun value => value, Units.val_injective⟩
  have image : Finset.univ.map embedding = Finset.univ \ {(0 : K)} := by
    ext value
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and, Finset.mem_sdiff, Finset.mem_singleton, embedding] using! isUnit_iff_ne_zero
  calc
    _ = ∑ value ∈ Finset.univ \ {(0 : K)}, value ^ exponent := by
      rw [← Finset.sum_sdiff ({0} : Finset K).subset_univ,
        Finset.sum_singleton, zero_pow zero, add_zero]
    _ = ∑ value : Kˣ, (value ^ exponent : K) := by
      simp [embedding, ← image, Finset.univ.sum_map embedding]
    _ = 0 := by rw [FiniteField.sum_pow_units K exponent, ite_eq_right (notMultiple zero)]

omit [Fintype Coordinate] in
/-- A polynomial with no positive `q - 1` multiples in its support has
zero evaluation sum over the finite field. -/
theorem polynomialSumEqZeroOfNoPositiveMultiples [Fintype K]
    (polynomial : Polynomial K)
    (notMultiple : ∀ exponent ∈ polynomial.support,
      0 < exponent → ¬ (Fintype.card K - 1) ∣ exponent) :
    ∑ value : K, polynomial.eval value = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro exponent inSupport
  rw [← Finset.mul_sum, sumPowEqZero exponent
    (fun nonzero => notMultiple exponent inSupport (Nat.pos_of_ne_zero nonzero)), mul_zero]

/-- Every retained monomial has parity zero on every affine line. -/
theorem monomialValueLineParity
    [Fintype K] [CharP K 2] [Nonempty Coordinate]
    (degrees : Coordinate → Nat) (center direction : Coordinate → K)
    (width start blockWidth : Nat) (fieldCard : Fintype.card K = 2 ^ width)
    (blockPositive : 0 < blockWidth) (blockFits : start + blockWidth ≤ width)
    (dimensionFits : Fintype.card Coordinate ≤ 2 ^ blockWidth)
    (reduced : ∀ coordinate, degrees coordinate < 2 ^ width)
    (zeroBlock : CommonZeroBlock degrees start blockWidth) :
    ∑ parameter : K,
      monomialValue degrees (fun coordinate => center coordinate + direction coordinate * parameter) = 0 := by
  simpa only [lineMonomial_eval] using
    polynomialSumEqZeroOfNoPositiveMultiples (lineMonomial degrees center direction)
      (lineMonomialNoPositiveMultiple degrees center direction width start blockWidth fieldCard
        blockPositive blockFits dimensionFits reduced zeroBlock)

/-- Retained monomials recover at any target by summing over any punctured
projective line through it. -/
theorem monomialValueSumPuncturedLine
    [Fintype K] [CharP K 2] [Nonempty Coordinate]
    (degrees : Coordinate → Nat) (target : Coordinate → K)
    (direction : ℙ K (Coordinate → K))
    (width start blockWidth : Nat) (fieldCard : Fintype.card K = 2 ^ width)
    (blockPositive : 0 < blockWidth) (blockFits : start + blockWidth ≤ width)
    (dimensionFits : Fintype.card Coordinate ≤ 2 ^ blockWidth)
    (reduced : ∀ coordinate, degrees coordinate < 2 ^ width)
    (zeroBlock : CommonZeroBlock degrees start blockWidth) :
    monomialValue degrees target =
      ∑ point ∈ puncturedLine target direction, monomialValue degrees point := by
  classical
  have total := monomialValueLineParity degrees target direction.rep width start blockWidth
    fieldCard blockPositive blockFits dimensionFits reduced zeroBlock
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : K))] at total
  simp only [mul_zero, add_zero] at total
  have recover := eq_neg_of_add_eq_zero_right total
  rw [neg_eq_self_of_char_two] at recover
  rw [sum_puncturedLine]
  convert recover using 1
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  funext coordinate
  simp [Pi.smul_apply, mul_comm]

end Algebraic.MassProduction.HighRate
