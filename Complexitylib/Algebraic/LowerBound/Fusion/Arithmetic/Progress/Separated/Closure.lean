/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.MonomialSubstitution
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.Find

/-!
# Schnorr closure under monomial substitutions

Schnorr's original progress measure is not merely separation of the displayed
support.  It is the maximum separation obtainable after replacing every
variable by an arbitrary coefficient-one monomial.  This closure is what
makes the argument stable under the later identification of fresh gate
variables with old wires (and under their replacement by constants).

This file builds that closure over a fixed countable target variable type,
proves its finite bound, shows that it dominates ordinary separation, and
discharges the zero-cost product reverse substitution.  The additive
enrichment theorem is developed separately.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Closure

noncomputable section

variable {SourceVar : Type u}

/-- Apply a coefficient-one monomial substitution into countably many target
variables. -/
def transform
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    MvPolynomial ℕ ℕ :=
  MvPolynomial.bind₁ (MonomialSubstitution.substitution basis) polynomial

/-- Exact support of a monomial substitution: it is the image of the source
support under the induced linear exponent map. -/
theorem support_transform
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform basis polynomial).support =
      polynomial.support.image
        (MonomialSubstitution.exponentMap basis) := by
  classical
  rw [transform, Expansion.support_bind₁]
  simp_rw [MonomialSubstitution.support_monomialExpansion]
  exact Finset.biUnion_singleton

/-- Monomial substitution cannot increase the number of support monomials. -/
theorem card_support_transform_le
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    (transform basis polynomial).support.card ≤
      polynomial.support.card := by
  rw [support_transform]
  exact Finset.card_image_le

/-- Every substituted separation score is bounded by the original support
cardinality minus one. -/
theorem separationNumber_transform_le_card_sub_one
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationNumber (transform basis polynomial).support ≤
      polynomial.support.card - 1 :=
  (separationNumber_le_card_sub_one _).trans
    (Nat.sub_le_sub_right
      (card_support_transform_le basis polynomial) 1)

/-- A score witnessed after some monomial substitution. -/
def Achievable
    (polynomial : MvPolynomial SourceVar ℕ)
    (score : Nat) : Prop :=
  ∃ basis : SourceVar → ℕ →₀ ℕ,
    score ≤ separationNumber (transform basis polynomial).support

/-- Schnorr's substitution-closed separation number.  `findGreatest` is
bounded by support cardinality, so the definition remains a concrete natural
number despite quantifying over infinitely many monomial substitutions. -/
def separationClosure
    (polynomial : MvPolynomial SourceVar ℕ) : Nat := by
  classical
  exact Nat.findGreatest (Achievable polynomial)
    (polynomial.support.card - 1)

/-- Every particular monomial substitution lower-bounds the closed measure. -/
theorem separationNumber_transform_le_closure
    (basis : SourceVar → ℕ →₀ ℕ)
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationNumber (transform basis polynomial).support ≤
      separationClosure polynomial := by
  classical
  unfold separationClosure
  exact Nat.le_findGreatest
    (separationNumber_transform_le_card_sub_one basis polynomial)
    ⟨basis, Nat.le_refl _⟩

/-- The closed measure retains the same finite support-cardinality bound. -/
theorem separationClosure_le_card_sub_one
    (polynomial : MvPolynomial SourceVar ℕ) :
    separationClosure polynomial ≤ polynomial.support.card - 1 := by
  classical
  unfold separationClosure
  exact Nat.findGreatest_le _

/-- A positive closed score is witnessed by an actual monomial
substitution. -/
theorem achievable_separationClosure_of_pos
    {polynomial : MvPolynomial SourceVar ℕ}
    (positive : 0 < separationClosure polynomial) :
    Achievable polynomial (separationClosure polynomial) := by
  classical
  unfold separationClosure at positive ⊢
  exact Nat.findGreatest_of_ne_zero rfl positive.ne'

/-- Injective renaming of exponent coordinates preserves separatedness. -/
theorem IsSeparated.image_mapDomain
    [DecidableEq TargetVar]
    (embedding : Variable → TargetVar)
    (injective : Function.Injective embedding)
    {ambient selected : Finset (Variable →₀ ℕ)}
    (separated : IsSeparated ambient selected) :
    IsSeparated
      (ambient.image (Finsupp.mapDomain embedding))
      (selected.image (Finsupp.mapDomain embedding)) := by
  classical
  constructor
  · exact (Finset.image_mono (Finsupp.mapDomain embedding))
      separated.subset
  · intro left leftPresent right rightPresent middle middlePresent middleLe
    obtain ⟨leftSource, leftSourcePresent, leftEqual⟩ :=
      Finset.mem_image.mp leftPresent
    obtain ⟨rightSource, rightSourcePresent, rightEqual⟩ :=
      Finset.mem_image.mp rightPresent
    obtain ⟨middleSource, middleSourcePresent, middleEqual⟩ :=
      Finset.mem_image.mp middlePresent
    subst left
    subst right
    subst middle
    have sourceLe : middleSource ≤ leftSource + rightSource := by
      apply (Finsupp.mapDomain_le_mapDomain_iff_le injective
        middleSource (leftSource + rightSource)).mp
      simpa only [Finsupp.mapDomain_add] using middleLe
    rcases separated.2 leftSource leftSourcePresent
        rightSource rightSourcePresent middleSource middleSourcePresent
        sourceLe with equal | equal
    · exact Or.inl (congrArg (Finsupp.mapDomain embedding) equal)
    · exact Or.inr (congrArg (Finsupp.mapDomain embedding) equal)

/-- Separation number cannot decrease under an injective coordinate
renaming. -/
theorem separationNumber_le_image_mapDomain
    [DecidableEq TargetVar]
    (embedding : Variable → TargetVar)
    (injective : Function.Injective embedding)
    (ambient : Finset (Variable →₀ ℕ)) :
    separationNumber ambient ≤
      separationNumber
        (ambient.image (Finsupp.mapDomain embedding)) := by
  classical
  unfold separationNumber
  apply Finset.sup_le
  intro selected _
  split_ifs with separated
  · have mappedSeparated := IsSeparated.image_mapDomain
      embedding injective separated
    have candidate := candidate_card_sub_one_le mappedSeparated
    rw [Finset.card_image_of_injective _
      (Finsupp.mapDomain_injective injective)] at candidate
    exact candidate
  · exact Nat.zero_le _

/-- Canonical injection of a finite circuit-variable set into the countable
substitution universe. -/
def finiteBasis (variableCount : Nat) : Fin variableCount → ℕ →₀ ℕ :=
  fun coordinate => Finsupp.single coordinate.1 1

/-- The canonical monomial substitution is ordinary injective renaming into
`Nat`. -/
theorem transform_finiteBasis_eq_rename
    (polynomial : MvPolynomial (Fin variableCount) ℕ) :
    transform (finiteBasis variableCount) polynomial =
      MvPolynomial.rename Fin.val polynomial := by
  have substitutionEqual :
      MonomialSubstitution.substitution (finiteBasis variableCount) =
        fun coordinate => MvPolynomial.X coordinate.1 := by
    funext coordinate
    simp [MonomialSubstitution.substitution, finiteBasis, MvPolynomial.X]
  rw [transform, substitutionEqual]
  have homEqual :
      MvPolynomial.bind₁
          (fun coordinate : Fin variableCount =>
            MvPolynomial.X coordinate.1) =
        (MvPolynomial.rename Fin.val :
          MvPolynomial (Fin variableCount) ℕ →ₐ[ℕ]
            MvPolynomial ℕ ℕ) := by
    ext coordinate
    simp
  exact AlgHom.congr_fun homEqual polynomial

/-- Schnorr closure dominates ordinary separation of the displayed support. -/
theorem separationNumber_le_closure
    (polynomial : MvPolynomial (Fin variableCount) ℕ) :
    separationNumber polynomial.support ≤
      separationClosure polynomial := by
  calc
    separationNumber polynomial.support ≤
        separationNumber
          (polynomial.support.image (Finsupp.mapDomain Fin.val)) :=
      separationNumber_le_image_mapDomain Fin.val Fin.val_injective _
    _ = separationNumber
          (transform (finiteBasis variableCount) polynomial).support := by
      rw [transform_finiteBasis_eq_rename,
        MvPolynomial.support_rename_of_injective Fin.val_injective]
    _ ≤ separationClosure polynomial :=
      separationNumber_transform_le_closure _ _

/-- A single variable has zero substitution-closed separation. -/
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

/-- Lift a target monomial substitution across reverse product enrichment. -/
def productLift
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (left right : Fin variableCount) :
    Fin (variableCount + 1) → ℕ →₀ ℕ :=
  Fin.lastCases (basis left + basis right) basis

/-- Monomial substitution commutes with reverse product enrichment after
lifting the eliminated variable to the product exponent. -/
theorem transform_product_eq
    (basis : Fin variableCount → ℕ →₀ ℕ)
    (polynomial : MvPolynomial (Fin (variableCount + 1)) ℕ)
    (left right : Fin variableCount) :
    transform basis
        (MvPolynomial.bind₁
          (Fin.lastCases
            (MvPolynomial.X left * MvPolynomial.X right)
            MvPolynomial.X)
          polynomial) =
      transform (productLift basis left right) polynomial := by
  rw [transform, transform, MvPolynomial.bind₁_bind₁]
  congr 1
  apply MvPolynomial.algHom_ext
  intro source
  simp only [MvPolynomial.bind₁_X_right]
  refine Fin.lastCases ?_ (fun prior => ?_) source
  · simp [MonomialSubstitution.substitution, productLift]
  · simp [MonomialSubstitution.substitution, productLift]

/-- Product reverse substitution cannot increase Schnorr's closed measure. -/
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
  · obtain ⟨basis, witnessed⟩ :=
      achievable_separationClosure_of_pos positive
    calc
      separationClosure
          (MvPolynomial.bind₁
            (Fin.lastCases
              (MvPolynomial.X left * MvPolynomial.X right)
              MvPolynomial.X)
            polynomial) ≤
          separationNumber
            (transform basis
              (MvPolynomial.bind₁
                (Fin.lastCases
                  (MvPolynomial.X left * MvPolynomial.X right)
                  MvPolynomial.X)
                polynomial)).support := witnessed
      _ = separationNumber
          (transform (productLift basis left right) polynomial).support := by
        rw [transform_product_eq]
      _ ≤ separationClosure polynomial :=
        separationNumber_transform_le_closure _ _
  · omega

end
end Closure
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
