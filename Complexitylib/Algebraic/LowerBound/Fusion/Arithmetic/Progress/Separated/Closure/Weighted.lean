/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Closure
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.WeightedMonomialSubstitution

/-!
# Schnorr closure under weighted monomial substitutions

This strengthens `Closure.separationClosure` by allowing every source
variable to carry an arbitrary natural coefficient.  Positive weights merely
rescale monomials; a zero weight deletes every source monomial using that
variable.  The enlarged closure is therefore stable under substitution of
all natural constants, including zero.

The closure is still finite because a weighted monomial substitution can only
identify or delete source monomials.  This file proves the finite bound, its
comparison with ordinary Schnorr closure, and the zero-cost product and
constant laws.  The addition law is developed separately because it is the
only step that can create a new support branch.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure
namespace Weighted

noncomputable section

variable {SourceVar : Type u}

/-- Apply a natural-weighted monomial substitution into countably many target
variables. -/
def transform
    (weight : SourceVar → ℕ)
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    MvPolynomial ℕ ℕ :=
  WeightedMonomialSubstitution.transform weight basis polynomial

/-- A score witnessed after a weighted monomial substitution. -/
def Achievable
    (polynomial : MvPolynomial SourceVar ℕ)
    (score : Nat) : Prop :=
  ∃ (weight : SourceVar → ℕ) (basis : SourceVar → ℕ →₀ ℕ),
    score ≤ separationNumber (transform weight basis polynomial).support

/-- Every weighted substitution score is bounded by the original support
cardinality minus one. -/
theorem separationNumber_transform_le_card_sub_one
    (weight : SourceVar → ℕ)
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationNumber (transform weight basis polynomial).support ≤
      polynomial.support.card - 1 :=
  (separationNumber_le_card_sub_one _).trans
    (Nat.sub_le_sub_right
      (WeightedMonomialSubstitution.card_support_transform_le
        weight basis polynomial) 1)

/-- Schnorr's separation measure closed under arbitrary natural-weighted
monomial substitutions. -/
def separationClosure
    (polynomial : MvPolynomial SourceVar ℕ) : Nat := by
  classical
  exact Nat.findGreatest (Achievable polynomial)
    (polynomial.support.card - 1)

/-- Every particular weighted substitution lower-bounds the weighted
closure. -/
theorem separationNumber_transform_le_closure
    (weight : SourceVar → ℕ)
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationNumber (transform weight basis polynomial).support ≤
      separationClosure polynomial := by
  classical
  unfold separationClosure
  exact Nat.le_findGreatest
    (separationNumber_transform_le_card_sub_one weight basis polynomial)
    ⟨weight, basis, Nat.le_refl _⟩

/-- Weighted closure retains the finite support-cardinality bound. -/
theorem separationClosure_le_card_sub_one
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationClosure polynomial ≤ polynomial.support.card - 1 := by
  classical
  unfold separationClosure
  exact Nat.findGreatest_le _

/-- A positive weighted-closure score has an actual substitution witness. -/
theorem achievable_separationClosure_of_pos
    {polynomial : MvPolynomial SourceVar ℕ}
    (positive : 0 < separationClosure polynomial) :
    Achievable polynomial (separationClosure polynomial) := by
  classical
  unfold separationClosure at positive ⊢
  exact Nat.findGreatest_of_ne_zero rfl positive.ne'

/-- Weighted transformed support depends only on source support. -/
theorem transform_support_eq_of_support_eq
    (weight : SourceVar → ℕ)
    (basis : SourceVar → ℕ →₀ ℕ)
    {left right : MvPolynomial SourceVar ℕ}
    (supportEqual : left.support = right.support) :
    (transform weight basis left).support =
      (transform weight basis right).support := by
  rw [transform, transform,
    WeightedMonomialSubstitution.support_transform_eq_surviving_image,
    WeightedMonomialSubstitution.support_transform_eq_surviving_image]
  unfold WeightedMonomialSubstitution.survivingSupport
  rw [supportEqual]

/-- Weighted Schnorr closure is coefficient-insensitive: polynomials with the
same support have exactly the same value. -/
theorem separationClosure_eq_of_support_eq
    {left right : MvPolynomial SourceVar ℕ}
    (supportEqual : left.support = right.support) :
    separationClosure left = separationClosure right := by
  classical
  apply Nat.le_antisymm
  · by_cases positive : 0 < separationClosure left
    · obtain ⟨weight, basis, witnessed⟩ :=
        achievable_separationClosure_of_pos positive
      calc
        separationClosure left ≤
            separationNumber (transform weight basis left).support :=
          witnessed
        _ = separationNumber (transform weight basis right).support := by
          rw [transform_support_eq_of_support_eq weight basis supportEqual]
        _ ≤ separationClosure right :=
          separationNumber_transform_le_closure _ _ _
    · omega
  · by_cases positive : 0 < separationClosure right
    · obtain ⟨weight, basis, witnessed⟩ :=
        achievable_separationClosure_of_pos positive
      calc
        separationClosure right ≤
            separationNumber (transform weight basis right).support :=
          witnessed
        _ = separationNumber (transform weight basis left).support := by
          rw [transform_support_eq_of_support_eq weight basis
            supportEqual.symm]
        _ ≤ separationClosure left :=
          separationNumber_transform_le_closure _ _ _
    · omega

/-- A single variable has zero weighted closure, even though it may be
deleted by a zero weight. -/
@[simp] theorem separationClosure_X
    (coordinate : Fin variableCount) :
    separationClosure
      (MvPolynomial.X coordinate :
        MvPolynomial (Fin variableCount) ℕ) = 0 := by
  apply Nat.le_zero.mp
  simpa [MvPolynomial.support_X] using
    separationClosure_le_card_sub_one
      (MvPolynomial.X coordinate :
        MvPolynomial (Fin variableCount) ℕ)

/-- Unit weights recover the ordinary coefficient-one monomial transform. -/
theorem transform_one_eq
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    transform (fun _ => 1) basis polynomial =
      Closure.transform basis polynomial := rfl

/-- Weighted closure dominates Schnorr's ordinary monomial-substitution
closure. -/
theorem ordinary_separationClosure_le
    (polynomial : MvPolynomial SourceVar ℕ) :
    Closure.separationClosure polynomial ≤ separationClosure polynomial := by
  classical
  by_cases positive : 0 < Closure.separationClosure polynomial
  · obtain ⟨basis, witnessed⟩ :=
      Closure.achievable_separationClosure_of_pos positive
    calc
      Closure.separationClosure polynomial ≤
          separationNumber (Closure.transform basis polynomial).support :=
        witnessed
      _ = separationNumber
          (transform (fun _ => 1) basis polynomial).support := by
        rw [transform_one_eq]
      _ ≤ separationClosure polynomial :=
        separationNumber_transform_le_closure _ _ _
  · omega

/-- In particular, displayed support separation lower-bounds weighted
closure on finite circuit-variable sets. -/
theorem separationNumber_le_closure
    (polynomial : MvPolynomial (Fin variableCount) ℕ) :
    separationNumber polynomial.support ≤ separationClosure polynomial :=
  (Closure.separationNumber_le_closure polynomial).trans
    (ordinary_separationClosure_le polynomial)

/-- Weight lift for reverse substitution of the newest variable by a
product. -/
def productWeight
    (weight : Fin variableCount → ℕ)
    (left right : Fin variableCount) :
    Fin (variableCount + 1) → ℕ :=
  Fin.lastCases (weight left * weight right) weight

/-- Weighted monomial substitution commutes exactly with reverse product
substitution. -/
theorem transform_product_eq
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    transform weight basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      transform (productWeight weight left right)
        (Closure.productLift basis left right) polynomial := by
  rw [transform, transform,
    WeightedMonomialSubstitution.transform,
    WeightedMonomialSubstitution.transform,
    MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [WeightedMonomialSubstitution.substitution,
      productWeight, Closure.productLift]
  · simp [WeightedMonomialSubstitution.substitution,
      productWeight, Closure.productLift]

/-- Product reverse substitution cannot increase weighted Schnorr closure. -/
theorem product_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    separationClosure
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) ≤
      separationClosure polynomial := by
  by_cases positive : 0 < separationClosure
      (MvPolynomial.bind₁
        (Fin.lastCases
          (MvPolynomial.X left * MvPolynomial.X right)
          MvPolynomial.X)
        polynomial)
  · obtain ⟨weight, basis, witnessed⟩ :=
      achievable_separationClosure_of_pos positive
    calc
      separationClosure
          (MvPolynomial.bind₁
            (Fin.lastCases
              (MvPolynomial.X left * MvPolynomial.X right)
              MvPolynomial.X)
            polynomial) ≤
          separationNumber
            (transform weight basis
              (MvPolynomial.bind₁
                (Fin.lastCases
                  (MvPolynomial.X left * MvPolynomial.X right)
                  MvPolynomial.X)
                polynomial)).support := witnessed
      _ = separationNumber
          (transform (productWeight weight left right)
            (Closure.productLift basis left right) polynomial).support := by
        rw [transform_product_eq]
      _ ≤ separationClosure polynomial :=
        separationNumber_transform_le_closure _ _ _
  · omega

/-- Weight lift for reverse substitution of the newest variable by an
arbitrary natural scalar. -/
def constantWeight
    (weight : Fin variableCount → ℕ)
    (scalar : ℕ) : Fin (variableCount + 1) → ℕ :=
  Fin.lastCases scalar weight

/-- Exponent lift for a scalar, whose monomial exponent is zero. -/
def constantBasis
    (basis : Fin variableCount → ℕ →₀ ℕ) :
    Fin (variableCount + 1) → ℕ →₀ ℕ :=
  Fin.lastCases 0 basis

/-- Weighted monomial substitution commutes exactly with substitution of any
natural scalar, including zero. -/
theorem transform_constant_eq
    (weight : Fin variableCount → ℕ)
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (scalar : ℕ) :
    transform weight basis
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) =
      transform (constantWeight weight scalar)
        (constantBasis basis) polynomial := by
  rw [transform, transform,
    WeightedMonomialSubstitution.transform,
    WeightedMonomialSubstitution.transform,
    MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [WeightedMonomialSubstitution.substitution,
      constantWeight, constantBasis]
  · simp [WeightedMonomialSubstitution.substitution,
      constantWeight, constantBasis]

/-- Reverse substitution of every natural scalar, zero included, cannot
increase weighted Schnorr closure. -/
theorem constant_substitution_le
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (scalar : ℕ) :
    separationClosure
        (MvPolynomial.bind₁
          (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
          polynomial) ≤
      separationClosure polynomial := by
  by_cases positive : 0 < separationClosure
      (MvPolynomial.bind₁
        (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
        polynomial)
  · obtain ⟨weight, basis, witnessed⟩ :=
      achievable_separationClosure_of_pos positive
    calc
      separationClosure
          (MvPolynomial.bind₁
            (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
            polynomial) ≤
          separationNumber
            (transform weight basis
              (MvPolynomial.bind₁
                (Fin.lastCases (MvPolynomial.C scalar) MvPolynomial.X)
                polynomial)).support := witnessed
      _ = separationNumber
          (transform (constantWeight weight scalar)
            (constantBasis basis) polynomial).support := by
        rw [transform_constant_eq]
      _ ≤ separationClosure polynomial :=
        separationNumber_transform_le_closure _ _ _
  · omega

end
end Weighted
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
