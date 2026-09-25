/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Positive weighted monomial substitutions

A weighted monomial substitution sends each source variable to one monomial
with a specified natural coefficient.  If every weight is positive, the
weights affect coefficients but not support: the support is still the image
of the source support under the linear exponent map.

This is the coefficient-aware extension of `MonomialSubstitution` needed for
positive named constants.  A positive scalar is represented by a monomial of
exponent zero and that scalar as its weight.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace WeightedMonomialSubstitution

noncomputable section

variable {SourceVar : Type u}
variable {TargetVar : Type v}

/-- Send a source variable to a monomial with the prescribed exponent and
coefficient. -/
def substitution
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (source : SourceVar) : MvPolynomial TargetVar ℕ :=
  MvPolynomial.monomial (basis source) (weight source)

/-- Product of the coefficient weights contributed by a source monomial. -/
def coefficient
    (weight : SourceVar → ℕ)
    (exponent : SourceVar →₀ ℕ) : ℕ :=
  exponent.prod fun source power => weight source ^ power

/-- A weighted monomial substitution still expands one monomial to one
monomial; its exponent and coefficient are computed independently. -/
theorem monomialExpansion_eq
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    Expansion.monomialExpansion (substitution weight basis) exponent =
      MvPolynomial.monomial
        (MonomialSubstitution.exponentMap basis exponent)
        (coefficient weight exponent) := by
  rw [Expansion.monomialExpansion, MvPolynomial.bind₁_monomial]
  simp only [MvPolynomial.C_1, one_mul, substitution,
    MvPolynomial.monomial_pow]
  rw [MonomialSubstitution.exponentMap,
    Finsupp.linearCombination_apply, coefficient]
  simp only [Finsupp.prod, Finsupp.sum]
  exact (MvPolynomial.monomial_sum_prod exponent.support
    (fun source => exponent source • basis source)
    (fun source => weight source ^ exponent source)).symm

/-- Positivity of all variable weights implies positivity of every monomial
coefficient produced by the substitution. -/
theorem coefficient_pos
    (weight : SourceVar → ℕ)
    (positive : ∀ source, 0 < weight source)
    (exponent : SourceVar →₀ ℕ) :
    0 < coefficient weight exponent := by
  rw [coefficient, Finsupp.prod]
  exact Finset.prod_pos fun source _ =>
    pow_pos (positive source) _

/-- Without a positivity assumption, a weighted monomial expansion is either
zero or has the usual singleton exponent support. -/
theorem support_monomialExpansion_eq_if
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    (Expansion.monomialExpansion
      (substitution weight basis) exponent).support =
        if coefficient weight exponent = 0 then ∅
        else {MonomialSubstitution.exponentMap basis exponent} := by
  rw [monomialExpansion_eq, MvPolynomial.support_monomial]

/-- Even zero weights cannot create an exponent outside the ordinary linear
image; they can only delete that image monomial. -/
theorem support_monomialExpansion_subset
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (exponent : SourceVar →₀ ℕ) :
    (Expansion.monomialExpansion
      (substitution weight basis) exponent).support ⊆
        {MonomialSubstitution.exponentMap basis exponent} := by
  rw [support_monomialExpansion_eq_if]
  split <;> simp

/-- Under positive weights, every source monomial has singleton support at
the ordinary linear exponent image. -/
@[simp] theorem support_monomialExpansion
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (positive : ∀ source, 0 < weight source)
    (exponent : SourceVar →₀ ℕ) :
    (Expansion.monomialExpansion
      (substitution weight basis) exponent).support =
        {MonomialSubstitution.exponentMap basis exponent} := by
  rw [monomialExpansion_eq, MvPolynomial.support_monomial]
  simp [Nat.ne_of_gt (coefficient_pos weight positive exponent)]

/-- Apply a weighted monomial substitution to a polynomial. -/
def transform
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    MvPolynomial TargetVar ℕ :=
  MvPolynomial.bind₁ (substitution weight basis) polynomial

/-- Source monomials whose accumulated coefficient weight is nonzero. -/
def survivingSupport
    (weight : SourceVar → ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    Finset (SourceVar →₀ ℕ) :=
  polynomial.support.filter fun exponent => coefficient weight exponent ≠ 0

/-- Exact support with arbitrary weights: discard source monomials killed by
a zero accumulated weight, then apply the linear exponent map. -/
theorem support_transform_eq_surviving_image
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform weight basis polynomial).support =
      (survivingSupport weight polynomial).image
        (MonomialSubstitution.exponentMap basis) := by
  classical
  rw [transform, Expansion.support_bind₁]
  ext target
  constructor
  · intro targetPresent
    rw [Finset.mem_biUnion] at targetPresent
    obtain ⟨source, sourcePresent, targetPresent⟩ := targetPresent
    rw [support_monomialExpansion_eq_if] at targetPresent
    by_cases sourceKilled : coefficient weight source = 0
    · simp [sourceKilled] at targetPresent
    · have targetEqual : target =
          MonomialSubstitution.exponentMap basis source := by
        simpa [sourceKilled] using targetPresent
      exact Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨sourcePresent, sourceKilled⟩,
          targetEqual.symm⟩
  · intro targetPresent
    rw [Finset.mem_image] at targetPresent
    obtain ⟨source, sourcePresent, sourceEqual⟩ := targetPresent
    rw [survivingSupport, Finset.mem_filter] at sourcePresent
    rw [Finset.mem_biUnion]
    refine ⟨source, sourcePresent.1, ?_⟩
    rw [support_monomialExpansion_eq_if,
      ite_eq_right sourcePresent.2, Finset.mem_singleton]
    exact sourceEqual.symm

/-- Exact support of a positive weighted monomial substitution. -/
theorem support_transform
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (positive : ∀ source, 0 < weight source)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform weight basis polynomial).support =
      polynomial.support.image
        (MonomialSubstitution.exponentMap basis) := by
  classical
  rw [transform, Expansion.support_bind₁]
  simp_rw [support_monomialExpansion weight basis positive]
  exact Finset.biUnion_singleton

/-- Arbitrary natural weights, including zero, can only delete monomials from
the exponent image of the source support. -/
theorem support_transform_subset_image
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform weight basis polynomial).support ⊆
      polynomial.support.image
        (MonomialSubstitution.exponentMap basis) := by
  classical
  rw [transform, Expansion.support_bind₁]
  intro target targetPresent
  rw [Finset.mem_biUnion] at targetPresent
  obtain ⟨source, sourcePresent, targetPresent⟩ := targetPresent
  have targetImage :=
    support_monomialExpansion_subset weight basis source targetPresent
  have targetEqual := Finset.mem_singleton.mp targetImage
  exact Finset.mem_image.mpr ⟨source, sourcePresent, targetEqual.symm⟩

/-- A weighted monomial substitution never increases support cardinality,
whether or not some weights vanish. -/
theorem card_support_transform_le
    [DecidableEq TargetVar]
    (weight : SourceVar → ℕ)
    (basis : SourceVar → TargetVar →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform weight basis polynomial).support.card ≤
      polynomial.support.card :=
  (Finset.card_le_card
    (support_transform_subset_image weight basis polynomial)).trans
      Finset.card_image_le

end
end WeightedMonomialSubstitution
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
