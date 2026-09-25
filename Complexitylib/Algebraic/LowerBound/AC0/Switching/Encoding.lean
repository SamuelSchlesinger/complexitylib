/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.RandomRestriction

/-!
# Weighted encodings for switching arguments

The switching lemma is proved by injecting each bad random restriction into a
more fully assigned restriction together with bounded finite advice. This
module isolates the exact finite probability calculation behind that method.

Its principal statement is division-free. If every encoded restriction fixes
exactly `s` formerly live variables, multiplying the bad-event probability by
`((1 - p) / 2) ^ s` is at most the number of advice strings times `p ^ s`.
Later estimates may divide by the fixed-coordinate weight under an explicit
positivity hypothesis. No asymptotics or search enter this layer.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace RandomRestriction

open scoped BigOperators ENNReal

/-- Fixing only previously live variables gives an exact, division-free point
mass identity. Each newly fixed coordinate exchanges one factor of `p` for
one factor of `(1 - p) / 2`. -/
theorem distribution_refine_cross_mul
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (rho extension : PartialAssignment n)
    (fixesOnlyLive :
      extension.fixedVariables ⊆ rho.liveVariables) :
    (fixedWeight p : ENNReal) ^ extension.fixedCount *
        distribution n p atMostOne rho =
      (p : ENNReal) ^ extension.fixedCount *
        distribution n p atMostOne (rho.refine extension) := by
  rw [distribution_apply_eq_live_fixed,
    distribution_apply_eq_live_fixed]
  have liveCount := PartialAssignment.liveCount_refine_add_fixedCount_eq
    rho extension fixesOnlyLive
  have fixedCount := PartialAssignment.fixedCount_refine_eq_add
    rho extension fixesOnlyLive
  rw [← liveCount, fixedCount, pow_add, pow_add]
  ac_rfl

/-- A weighted injection from an event into restrictions paired with finite
advice bounds the scaled event probability by the advice cardinality times
the output-side factor. -/
theorem probability_scaled_le_of_injective_encoding
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (event : PartialAssignment n → Prop)
    [DecidablePred event]
    (Advice : Type)
    [Fintype Advice]
    [DecidableEq Advice]
    (scale factor : ENNReal)
    (encode : PartialAssignment n → PartialAssignment n × Advice)
    (injectiveOnEvent : ∀ left, event left →
      ∀ right, event right →
        encode left = encode right → left = right)
    (massBound : ∀ rho, event rho →
      scale * distribution n p atMostOne rho ≤
        factor * distribution n p atMostOne (encode rho).1) :
    scale * probability n p atMostOne event ≤
      (Fintype.card Advice : ENNReal) * factor := by
  classical
  let bad : Finset (PartialAssignment n) := Finset.univ.filter event
  have injectiveOn : Set.InjOn encode (bad : Set (PartialAssignment n)) := by
    intro left leftPresent right rightPresent equal
    exact injectiveOnEvent left (Finset.mem_filter.1 leftPresent).2
      right (Finset.mem_filter.1 rightPresent).2 equal
  calc
    scale * probability n p atMostOne event =
        ∑ rho ∈ bad, scale * distribution n p atMostOne rho := by
      change scale * (∑ rho ∈ bad,
        distribution n p atMostOne rho) = _
      rw [Finset.mul_sum]
    _ ≤ ∑ rho ∈ bad,
        factor * distribution n p atMostOne (encode rho).1 := by
      apply Finset.sum_le_sum
      intro rho present
      exact massBound rho (Finset.mem_filter.1 present).2
    _ = ∑ output ∈ Finset.image encode bad,
        factor * distribution n p atMostOne output.1 := by
      exact (Finset.sum_image
        (f := fun output =>
          factor * distribution n p atMostOne output.1)
        injectiveOn).symm
    _ ≤ ∑ output : PartialAssignment n × Advice,
        factor * distribution n p atMostOne output.1 := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = (Fintype.card Advice : ENNReal) * factor *
        ∑ rho : PartialAssignment n, distribution n p atMostOne rho := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
    _ = (Fintype.card Advice : ENNReal) * factor := by
      rw [show (∑ rho : PartialAssignment n,
        distribution n p atMostOne rho) = 1 by
          simpa [distribution] using sum_weight n p atMostOne]
      simp

/-- Exact encoding bound specialized to extensions that fix exactly
`fixedCount` live variables. This is the probability engine used by the
canonical switching-path encoding. -/
theorem probability_scaled_le_of_refinement_encoding
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (event : PartialAssignment n → Prop)
    [DecidablePred event]
    (Advice : Type)
    [Fintype Advice]
    [DecidableEq Advice]
    (fixedCount : Nat)
    (extension : PartialAssignment n → PartialAssignment n)
    (encode : PartialAssignment n → PartialAssignment n × Advice)
    (injectiveOnEvent : ∀ left, event left →
      ∀ right, event right →
        encode left = encode right → left = right)
    (output_eq : ∀ rho, event rho →
      (encode rho).1 = rho.refine (extension rho))
    (fixesOnlyLive : ∀ rho, event rho →
      (extension rho).fixedVariables ⊆ rho.liveVariables)
    (extensionCount : ∀ rho, event rho →
      (extension rho).fixedCount = fixedCount) :
    (fixedWeight p : ENNReal) ^ fixedCount *
        probability n p atMostOne event ≤
      (Fintype.card Advice : ENNReal) * (p : ENNReal) ^ fixedCount := by
  apply probability_scaled_le_of_injective_encoding n p atMostOne event
    Advice ((fixedWeight p : ENNReal) ^ fixedCount)
    ((p : ENNReal) ^ fixedCount) encode injectiveOnEvent
  intro rho present
  rw [output_eq rho present, ← extensionCount rho present]
  exact le_of_eq <| distribution_refine_cross_mul n p atMostOne rho
    (extension rho) (fixesOnlyLive rho present)

end RandomRestriction
end AC0
end Algebraic
