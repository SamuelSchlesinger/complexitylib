/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Coefficient-one separated monomials

Raw support can have collision fibers under substitution.  A target monomial
whose coefficient is exactly one cannot: exact coefficient decomposition
gives it a unique source origin, and that source monomial also has coefficient
one.  This file packages the resulting collision-rigid separation measure.

Product enrichment is discharged completely: every source monomial has one
monomial-valued expansion, so the unique-origin map is injective.  The only
remaining input to `measure` is the genuinely additive score bound.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Unit

noncomputable section

/-- A separated support subset all of whose ambient coefficients are one. -/
def IsUnitSeparated
    (polynomial : MvPolynomial Variable ℕ)
    (selected : Finset (Variable →₀ ℕ)) : Prop :=
  IsSeparated polynomial.support selected ∧
    ∀ exponent ∈ selected, AddMonoidAlgebra.coeff polynomial exponent = 1

/-- Maximum coefficient-one separation score of a polynomial. -/
def separationNumber
    (polynomial : MvPolynomial Variable ℕ) : Nat := by
  classical
  exact polynomial.support.powerset.sup fun selected =>
    if IsUnitSeparated polynomial selected then selected.card - 1 else 0

/-- Every coefficient-one separated candidate lower-bounds the unit
separation number. -/
theorem candidate_card_sub_one_le
    {polynomial : MvPolynomial Variable ℕ}
    {selected : Finset (Variable →₀ ℕ)}
    (separated : IsUnitSeparated polynomial selected) :
    selected.card - 1 ≤ separationNumber polynomial := by
  classical
  unfold separationNumber
  have present : selected ∈ polynomial.support.powerset :=
    Finset.mem_powerset.mpr separated.1.subset
  simpa [separated] using
    (Finset.le_sup (α := Nat)
      (f := fun candidate =>
        if IsUnitSeparated polynomial candidate then candidate.card - 1
        else 0)
      present)

/-- Unit separation number is at most support cardinality minus one. -/
theorem separationNumber_le_card_sub_one
    (polynomial : MvPolynomial Variable ℕ) :
    separationNumber polynomial ≤ polynomial.support.card - 1 := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected _
  split_ifs with separated
  · exact Nat.sub_le_sub_right
      (Finset.card_le_card separated.1.subset) 1
  · exact Nat.zero_le _

/-- A single variable has zero unit separation score. -/
@[simp] theorem separationNumber_X
    (coordinate : Variable) :
    separationNumber
      (MvPolynomial.X coordinate : MvPolynomial Variable ℕ) = 0 := by
  apply Nat.le_zero.mp
  simpa [MvPolynomial.support_X] using
    separationNumber_le_card_sub_one
      (MvPolynomial.X coordinate : MvPolynomial Variable ℕ)

/-- Pull back coefficient-one separated candidates across one substitution. -/
structure Pullback
    (source : MvPolynomial SourceVar ℕ)
    (target : MvPolynomial TargetVar ℕ)
    (loss : Nat) : Prop where
  pullback : ∀ selected,
    IsUnitSeparated target selected →
      ∃ prior, IsUnitSeparated source prior ∧
        selected.card - 1 ≤ prior.card - 1 + loss

/-- Unit pullbacks imply the corresponding separation-number inequality. -/
theorem Pullback.separationNumber_le
    {source : MvPolynomial SourceVar ℕ}
    {target : MvPolynomial TargetVar ℕ}
    {loss : Nat}
    (pullback : Pullback source target loss) :
    separationNumber target ≤ separationNumber source + loss := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected _
  split_ifs with separated
  · obtain ⟨prior, priorSeparated, score⟩ :=
      pullback.pullback selected separated
    have priorBound : prior.card - 1 ≤
        source.support.powerset.sup fun candidate =>
          if IsUnitSeparated source candidate then candidate.card - 1 else 0 :=
      candidate_card_sub_one_le priorSeparated
    exact score.trans (Nat.add_le_add_right priorBound loss)
  · exact Nat.zero_le _

/-- Product reverse substitution preserves the coefficient-one separation
score. -/
theorem product_pullback
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    Pullback polynomial
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left * MvPolynomial.X right)
          MvPolynomial.X)
        polynomial) 0 := by
  classical
  let productSubstitution :
      Fin (variableCount + 1) → MvPolynomial (Fin variableCount) ℕ :=
    Fin.lastCases
      (MvPolynomial.X left * MvPolynomial.X right)
      MvPolynomial.X
  constructor
  intro selected separated
  let origin : ↥selected → Fin (variableCount + 1) →₀ ℕ := fun target =>
    Classical.choose
      (Expansion.exists_unique_source_of_coeff_eq_one
        productSubstitution polynomial target.1
        (separated.2 target.1 target.2))
  have originSpec : ∀ target,
      origin target ∈ polynomial.support ∧
        AddMonoidAlgebra.coeff polynomial (origin target) = 1 ∧
          AddMonoidAlgebra.coeff (Expansion.monomialExpansion productSubstitution
                (origin target)) target.1 = 1 ∧
            Expansion.IsNeighbor productSubstitution (origin target) target.1 ∧
              ∀ other ∈ polynomial.support,
                Expansion.IsNeighbor productSubstitution other target.1 →
                  other = origin target := by
    intro target
    exact Classical.choose_spec
      (Expansion.exists_unique_source_of_coeff_eq_one
        productSubstitution polynomial target.1
        (separated.2 target.1 target.2))
  have originInjective : Function.Injective origin := by
    intro first second originsEqual
    have firstNeighbor := (originSpec first).2.2.2.1
    have secondNeighbor :
        Expansion.IsNeighbor productSubstitution (origin first) second.1 := by
      rw [originsEqual]
      exact (originSpec second).2.2.2.1
    change first.1 ∈
        (Expansion.monomialExpansion productSubstitution
          (origin first)).support at firstNeighbor
    change second.1 ∈
        (Expansion.monomialExpansion productSubstitution
          (origin first)).support at secondNeighbor
    dsimp [productSubstitution] at firstNeighbor secondNeighbor
    rw [MonomialSubstitution.product_support_monomialExpansion]
      at firstNeighbor secondNeighbor
    exact Subtype.ext
      ((Finset.mem_singleton.mp firstNeighbor).trans
        (Finset.mem_singleton.mp secondNeighbor).symm)
  let selection : Expansion.OriginSelection
      productSubstitution polynomial selected 0 := {
    origin := origin
    origin_mem := fun target => (originSpec target).1
    neighbor := fun target => (originSpec target).2.2.2.1
    rigid := fun target other otherPresent otherNeighbor =>
      (originSpec target).2.2.2.2 other otherPresent otherNeighbor
    score := by
      rw [Finset.card_image_of_injective _ originInjective,
        Finset.card_attach]
      simp }
  refine ⟨selected.attach.image origin, ?_, selection.score⟩
  constructor
  · exact selection.prior_isSeparated separated.1
  · intro source sourcePresent
    obtain ⟨target, _, sourceEqual⟩ := Finset.mem_image.mp sourcePresent
    rw [← sourceEqual]
    exact (originSpec target).2.1

/-- The only additional combinatorial input needed for the unit-separated
measure: addition enrichment loses at most one unit-separated score. -/
structure AdditionPullbacks : Prop where
  add : ∀ variableCount
      (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
      (left right : Fin variableCount),
    Pullback polynomial
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left + MvPolynomial.X right)
          MvPolynomial.X)
        polynomial) 1

/-- Coefficient-one separated monomials form an addition-cost progress
measure once the additive one-loss theorem is supplied; product enrichment is
already proved internally. -/
def measure
    (additionPullbacks : AdditionPullbacks) :
    Progress.Measure
      (Algebraic.Arithmetic.additionCost (K := PEmpty)) where
  value := fun _ polynomial => separationNumber polynomial
  variable_zero := fun _ coordinate => separationNumber_X coordinate
  add_substitution_le := by
    intro variableCount polynomial left right
    simpa using
      (additionPullbacks.add variableCount polynomial left right).separationNumber_le
  mul_substitution_le := by
    intro variableCount polynomial left right
    simpa using
      (product_pullback polynomial left right).separationNumber_le

end
end Unit
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
