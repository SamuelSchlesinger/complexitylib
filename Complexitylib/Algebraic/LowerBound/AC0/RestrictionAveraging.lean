/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.RandomRestriction

/-!
# Live-variable averaging for random restrictions

This module supplies the quantitative existence step needed to iterate the
switching lemma without appealing to sampling or finite search. A coordinate
is live under the independent `p`-restriction with probability exactly `p`.
Consequently, after refining a fixed restriction `rho`, the expected number
of surviving live variables is exactly `p * rho.liveCount`.

The final theorem turns an upper bound `delta` on any bad event into a good
restriction with many survivors. If `m = rho.liveCount` and

`delta * m + k < p * m`,

then some restriction outside the bad event leaves at least `k` variables
live below `rho`. This is a direct finite averaging argument. It introduces no
concentration theorem, optimizer, sampler, or circuit search.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace RandomRestriction

open scoped BigOperators ENNReal

/-- A designated coordinate is live with probability exactly `p`. -/
theorem probability_coordinate_live
    (n : Nat)
    (p : NNReal)
    (atMostOne : p <= 1)
    (selected : Fin n) :
    probability n p atMostOne (fun rho => rho selected = none) =
      (p : ENNReal) := by
  classical
  let selectedWeight : Fin n -> Option Bool -> ENNReal :=
    fun index state =>
      if index = selected then
        if state = none then (coordinateWeight p state : ENNReal) else 0
      else
        (coordinateWeight p state : ENNReal)
  calc
    probability n p atMostOne (fun rho => rho selected = none) =
        (∑ rho : PartialAssignment n,
          ∏ index, selectedWeight index (rho index)) := by
      unfold probability
      simp only [distribution_apply, weight, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro rho _
      by_cases live : rho selected = none
      · rw [ite_eq_left live]
        apply Finset.prod_congr rfl
        intro index _
        by_cases equal : index = selected
        · subst index
          simp [selectedWeight, live]
        · simp [selectedWeight, equal]
      · rw [ite_eq_right live]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ selected)
        simp [selectedWeight, live]
    _ = (∏ index : Fin n,
          ∑ state : Option Bool, selectedWeight index state) :=
      (Fintype.prod_sum selectedWeight).symm
    _ = (p : ENNReal) := by
      rw [Fintype.prod_eq_single selected]
      · simp [selectedWeight]
      · intro index different
        simpa [selectedWeight, different] using
          sum_coordinateWeight p atMostOne

/-- Expected live-variable count after independently refining `rho`. -/
noncomputable def expectedLiveCountAfter
    (n : Nat)
    (p : NNReal)
    (atMostOne : p <= 1)
    (rho : PartialAssignment n) : ENNReal :=
  ∑ extension : PartialAssignment n,
    distribution n p atMostOne extension *
      ((rho.refine extension).liveCount : ENNReal)

/-- The live count of a refinement is the sum of the survival indicators over
the coordinates currently live in the base restriction. -/
theorem liveCount_refine_eq_sum_indicators
    (rho extension : PartialAssignment n) :
    ((rho.refine extension).liveCount : ENNReal) =
      ∑ index ∈ rho.liveVariables,
        if extension index = none then (1 : ENNReal) else 0 := by
  rw [PartialAssignment.liveCount,
    PartialAssignment.liveVariables_refine]
  norm_cast
  rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro index _
  simp [PartialAssignment.mem_liveVariables]

/-- Exact first moment of the surviving live-variable count. -/
theorem expectedLiveCountAfter_eq
    (n : Nat)
    (p : NNReal)
    (atMostOne : p <= 1)
    (rho : PartialAssignment n) :
    expectedLiveCountAfter n p atMostOne rho =
      (p : ENNReal) * (rho.liveCount : ENNReal) := by
  unfold expectedLiveCountAfter
  simp_rw [liveCount_refine_eq_sum_indicators]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ index ∈ rho.liveVariables,
        ∑ extension,
          distribution n p atMostOne extension *
            if extension index = none then 1 else 0) =
        ∑ _index ∈ rho.liveVariables, (p : ENNReal) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← probability_coordinate_live n p atMostOne index]
      unfold probability
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro extension _
      by_cases live : extension index = none <;> simp [live]
    _ = (p : ENNReal) * (rho.liveCount : ENNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        PartialAssignment.liveCount]
      exact mul_comm _ _

/-- Finite averaging outside a bad event. If the bad mass can account for at
most `failureBound * rho.liveCount` of the first moment and the displayed
strict inequality leaves room for `retained`, some good refinement retains at
least that many live variables. -/
theorem exists_good_refinement_with_liveCount
    (n : Nat)
    (p : NNReal)
    (atMostOne : p <= 1)
    (rho : PartialAssignment n)
    (bad : PartialAssignment n -> Prop)
    [DecidablePred bad]
    (failureBound : ENNReal)
    (retained : Nat)
    (failure : probability n p atMostOne bad <= failureBound)
    (room :
      failureBound * (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    exists extension : PartialAssignment n,
      Not (bad extension) /\
        retained <= (rho.refine extension).liveCount := by
  classical
  by_contra noWitness
  have goodCountLe : forall extension : PartialAssignment n,
      Not (bad extension) ->
        (rho.refine extension).liveCount <= retained := by
    intro extension good
    have notRetained : Not (retained <=
        (rho.refine extension).liveCount) := by
      intro retainedBound
      exact noWitness <| Exists.intro extension
        (And.intro good retainedBound)
    exact (Nat.lt_of_not_ge notRetained).le
  have badSumLe :
      (∑ extension : PartialAssignment n with bad extension,
          distribution n p atMostOne extension *
            ((rho.refine extension).liveCount : ENNReal)) <=
        failureBound * (rho.liveCount : ENNReal) := by
    calc
      (∑ extension : PartialAssignment n with bad extension,
          distribution n p atMostOne extension *
            ((rho.refine extension).liveCount : ENNReal)) <=
          ∑ extension : PartialAssignment n with bad extension,
            distribution n p atMostOne extension *
              (rho.liveCount : ENNReal) := by
        apply Finset.sum_le_sum
        intro extension _
        gcongr
        exact PartialAssignment.liveCount_refine_le_left rho extension
      _ = probability n p atMostOne bad *
            (rho.liveCount : ENNReal) := by
        rw [← Finset.sum_mul]
        rfl
      _ <= failureBound * (rho.liveCount : ENNReal) := by
        gcongr
  have goodSumLe :
      (∑ extension : PartialAssignment n with Not (bad extension),
          distribution n p atMostOne extension *
            ((rho.refine extension).liveCount : ENNReal)) <=
        (retained : ENNReal) := by
    calc
      (∑ extension : PartialAssignment n with Not (bad extension),
          distribution n p atMostOne extension *
            ((rho.refine extension).liveCount : ENNReal)) <=
          ∑ extension : PartialAssignment n with Not (bad extension),
            distribution n p atMostOne extension *
              (retained : ENNReal) := by
        apply Finset.sum_le_sum
        intro extension present
        gcongr
        exact goodCountLe extension (Finset.mem_filter.mp present).2
      _ = probability n p atMostOne
            (fun extension => Not (bad extension)) *
              (retained : ENNReal) := by
        rw [← Finset.sum_mul]
        rfl
      _ <= 1 * (retained : ENNReal) := by
        gcongr
        exact probability_le_one n p atMostOne
          (fun extension => Not (bad extension))
      _ = (retained : ENNReal) := one_mul _
  have contradiction :
      (p : ENNReal) * (rho.liveCount : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal) := by
    calc
      (p : ENNReal) * (rho.liveCount : ENNReal) =
          expectedLiveCountAfter n p atMostOne rho :=
        (expectedLiveCountAfter_eq n p atMostOne rho).symm
      _ =
          (∑ extension : PartialAssignment n with bad extension,
              distribution n p atMostOne extension *
                ((rho.refine extension).liveCount : ENNReal)) +
            ∑ extension : PartialAssignment n with Not (bad extension),
              distribution n p atMostOne extension *
                ((rho.refine extension).liveCount : ENNReal) := by
        unfold expectedLiveCountAfter
        exact (Finset.sum_filter_add_sum_filter_not
          Finset.univ bad
          (fun extension => distribution n p atMostOne extension *
            ((rho.refine extension).liveCount : ENNReal))).symm
      _ <= failureBound * (rho.liveCount : ENNReal) +
            (retained : ENNReal) := add_le_add badSumLe goodSumLe
      _ < (p : ENNReal) * (rho.liveCount : ENNReal) := room
  exact lt_irrefl _ contradiction

end RandomRestriction
end AC0
end Algebraic
