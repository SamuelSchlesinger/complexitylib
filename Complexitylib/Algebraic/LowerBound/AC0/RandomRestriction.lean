/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.PartialAssignment
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Option
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The finite p-random restriction distribution

For `0 <= p <= 1`, every input coordinate is independently left live with
probability `p`, fixed to false with probability `(1 - p) / 2`, and fixed to
true with the same probability. Parameters are nonnegative reals and event
probabilities are extended nonnegative reals, matching mathlib's `PMF` API.

The distribution is defined by its exact finite product mass. The normalization
proof factors the sum over all partial assignments into the product of the
three-state coordinate sums. No sampler or empirical approximation is used.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace RandomRestriction

open scoped BigOperators ENNReal

/-- Probability of either fixed Boolean value at one coordinate. -/
noncomputable def fixedWeight (p : NNReal) : NNReal :=
  (1 - p) / 2

/-- One-coordinate mass: `p` for a live variable and `(1 - p) / 2` for either
fixed value. -/
noncomputable def coordinateWeight
    (p : NNReal) : Option Bool -> NNReal
  | none => p
  | some _ => fixedWeight p

@[simp] theorem coordinateWeight_none (p : NNReal) :
    coordinateWeight p none = p := rfl

@[simp] theorem coordinateWeight_some
    (p : NNReal)
    (value : Bool) :
    coordinateWeight p (some value) = fixedWeight p := rfl

/-- The three one-coordinate masses sum exactly to one. -/
theorem sum_coordinateWeight
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    ∑ state : Option Bool, (coordinateWeight p state : ENNReal) = 1 := by
  norm_cast
  rw [Fintype.sum_option, Fintype.sum_bool]
  simp only [coordinateWeight, fixedWeight]
  have two_ne : (2 : NNReal) ≠ 0 := by norm_num
  rw [← two_mul, mul_div_cancel₀ _ two_ne]
  rw [add_comm, tsub_add_cancel_of_le atMostOne]

/-- Product mass of a particular restriction. -/
noncomputable def weight
    (p : NNReal)
    (rho : PartialAssignment n) : ENNReal :=
  ∏ index, (coordinateWeight p (rho index) : ENNReal)

/-- The finite product masses over all restrictions sum exactly to one. -/
theorem sum_weight
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    ∑ rho : PartialAssignment n, weight p rho = 1 := by
  simp only [weight]
  calc
    (∑ rho : PartialAssignment n,
        ∏ index, (coordinateWeight p (rho index) : ENNReal)) =
        ∏ _index : Fin n,
          ∑ state : Option Bool, (coordinateWeight p state : ENNReal) :=
      (Fintype.prod_sum
        (fun (_index : Fin n) (state : Option Bool) =>
          (coordinateWeight p state : ENNReal))).symm
    _ = 1 := by simp [sum_coordinateWeight p atMostOne]

/-- The standard independent `p`-random restriction on `n` variables. -/
noncomputable def distribution
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) : PMF (PartialAssignment n) :=
  PMF.ofFintype (weight p) (sum_weight n p atMostOne)

@[simp] theorem distribution_apply
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (rho : PartialAssignment n) :
    distribution n p atMostOne rho = weight p rho := rfl

/-- The product mass depends only on the numbers of live and fixed variables.
-/
theorem weight_eq_live_fixed
    (p : NNReal)
    (rho : PartialAssignment n) :
    weight p rho =
      (p : ENNReal) ^ rho.liveCount *
        (fixedWeight p : ENNReal) ^ rho.fixedCount := by
  unfold weight
  rw [← PartialAssignment.liveVariables_union_fixedVariables rho,
    Finset.prod_union
      (PartialAssignment.disjoint_liveVariables_fixedVariables rho)]
  congr 1
  · calc
      (∏ index ∈ rho.liveVariables,
          (coordinateWeight p (rho index) : ENNReal)) =
          ∏ _index ∈ rho.liveVariables, (p : ENNReal) := by
        apply Finset.prod_congr rfl
        intro index present
        rw [(PartialAssignment.mem_liveVariables rho index).1 present]
        rfl
      _ = (p : ENNReal) ^ rho.liveCount := by
        rw [Finset.prod_const]
        rfl
  · calc
      (∏ index ∈ rho.fixedVariables,
          (coordinateWeight p (rho index) : ENNReal)) =
          ∏ _index ∈ rho.fixedVariables,
            (fixedWeight p : ENNReal) := by
        apply Finset.prod_congr rfl
        intro index present
        have fixed :=
          (PartialAssignment.mem_fixedVariables rho index).1 present
        cases value : rho index with
        | none => exact False.elim (fixed value)
        | some bit => rfl
      _ = (fixedWeight p : ENNReal) ^ rho.fixedCount := by
        rw [Finset.prod_const]
        rfl

/-- Closed form for the mass assigned to an individual restriction. -/
theorem distribution_apply_eq_live_fixed
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (rho : PartialAssignment n) :
    distribution n p atMostOne rho =
      (p : ENNReal) ^ rho.liveCount *
        (fixedWeight p : ENNReal) ^ rho.fixedCount := by
  rw [distribution_apply, weight_eq_live_fixed]

/-- Probability of a predicate under the finite random-restriction
distribution. -/
noncomputable def probability
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (event : PartialAssignment n -> Prop)
    [DecidablePred event] : ENNReal :=
  ∑ rho with event rho, distribution n p atMostOne rho

/-- The certain event has probability one. -/
@[simp] theorem probability_true
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne (fun _ => True) = 1 := by
  classical
  simpa [probability, distribution] using sum_weight n p atMostOne

/-- The impossible event has probability zero. -/
@[simp] theorem probability_false
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne (fun _ => False) = 0 := by
  classical
  simp [probability]

/-- An event and its complement have total probability one. -/
theorem probability_add_complement
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (event : PartialAssignment n -> Prop)
    [DecidablePred event] :
    probability n p atMostOne event +
      probability n p atMostOne (fun rho => ¬event rho) = 1 := by
  unfold probability
  rw [Finset.sum_filter_add_sum_filter_not]
  simpa [distribution] using sum_weight n p atMostOne

/-- Every event has probability at most one. -/
theorem probability_le_one
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (event : PartialAssignment n -> Prop)
    [DecidablePred event] :
    probability n p atMostOne event ≤ 1 := by
  calc
    probability n p atMostOne event ≤
        ∑ rho : PartialAssignment n, distribution n p atMostOne rho := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset event Finset.univ)
    _ = 1 := by
      simpa [distribution] using sum_weight n p atMostOne

/-- Extensionally equal events have equal probability. -/
theorem probability_congr
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    {left right : PartialAssignment n -> Prop}
    [DecidablePred left]
    [DecidablePred right]
    (equal : forall rho, left rho ↔ right rho) :
    probability n p atMostOne left = probability n p atMostOne right := by
  classical
  unfold probability
  apply Finset.sum_congr
  · ext rho
    simp [equal rho]
  · intro rho present
    rfl

/-- Inclusion of finite events implies monotonicity of their exact
probabilities. -/
theorem probability_mono
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    {left right : PartialAssignment n -> Prop}
    [DecidablePred left]
    [DecidablePred right]
    (included : forall rho, left rho -> right rho) :
    probability n p atMostOne left ≤
      probability n p atMostOne right := by
  unfold probability
  apply Finset.sum_le_sum_of_subset
  intro rho present
  rw [Finset.mem_filter] at present ⊢
  exact ⟨present.1, included rho present.2⟩

/-- The exact probability of a union of two finite events is at most the sum
of their probabilities. -/
theorem probability_or_le
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (left right : PartialAssignment n -> Prop)
    [DecidablePred left]
    [DecidablePred right] :
    probability n p atMostOne (fun rho => left rho ∨ right rho) ≤
      probability n p atMostOne left +
        probability n p atMostOne right := by
  classical
  unfold probability
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro rho _
  by_cases leftHolds : left rho <;>
    by_cases rightHolds : right rho <;>
      simp [leftHolds, rightHolds]

/-- Finite union bound for an indexed family of exact restriction events. -/
theorem probability_exists_mem_le_sum
    {indexType : Type*}
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (indices : Finset indexType)
    (events : indexType -> PartialAssignment n -> Prop)
    [(index : indexType) -> DecidablePred (events index)] :
    probability n p atMostOne
        (fun rho => ∃ index ∈ indices, events index rho) ≤
      ∑ index ∈ indices, probability n p atMostOne (events index) := by
  classical
  unfold probability
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro rho _
  by_cases anyEvent : ∃ index ∈ indices, events index rho
  · simp only [ite_eq_left anyEvent]
    obtain ⟨index, present, holds⟩ := anyEvent
    calc
      distribution n p atMostOne rho =
          ∑ current ∈ {index},
            if events current rho then
              distribution n p atMostOne rho else 0 := by
        simp [holds]
      _ ≤ ∑ current ∈ indices,
            if events current rho then
              distribution n p atMostOne rho else 0 :=
        Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.mpr present)
  · simp [anyEvent]

/-- A singleton event has the point mass specified by the product formula. -/
theorem probability_singleton
    (n : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (target : PartialAssignment n) :
    probability n p atMostOne (fun rho => rho = target) =
      distribution n p atMostOne target := by
  classical
  unfold probability
  apply Finset.sum_eq_single target
  · intro rho present different
    exact False.elim <| different (Finset.mem_filter.mp present).2
  · intro absent
    exact False.elim <| absent <|
      Finset.mem_filter.mpr ⟨Finset.mem_univ target, rfl⟩

end RandomRestriction
end AC0
end Algebraic
