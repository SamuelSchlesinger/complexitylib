/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerExistence

/-!
# Iterated semantic AC0 depth reduction

This module iterates the existential one-layer switching step. A schedule
`retained i` specifies a lower bound on the number of live variables after
logical layer `i`. It suffices to check, for every layer below the target
depth,

`delta * retained i + retained (i + 1) < p * retained i`,

where `delta` is the charged one-step failure bound, together with
`delta <= p`. A monotonicity lemma lifts this scheduled inequality to the
possibly larger live count produced at runtime. Finite induction then yields
one cumulative restriction satisfying the semantic shallow-tree invariant at
the target depth and the final survivor bound.

The theorem remains parametric in the numerical schedule. Choosing and
simplifying source-facing parameters is deliberately separated from the
structural iteration proof.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- The first-moment room inequality is monotone in the current live count
when the bad-event bound is at most the survival probability. -/
theorem layerRoom_mono
    {delta p : ENNReal}
    {minimum current next : Nat}
    (deltaFinite : delta ≠ ∞)
    (deltaLe : delta <= p)
    (minimumLe : minimum <= current)
    (room :
      delta * (minimum : ENNReal) + (next : ENNReal) <
        p * (minimum : ENNReal)) :
    delta * (current : ENNReal) + (next : ENNReal) <
      p * (current : ENNReal) := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le minimumLe
  push_cast
  rw [mul_add, mul_add]
  calc
    delta * (minimum : ENNReal) + delta * (difference : ENNReal) +
          (next : ENNReal) =
        (delta * (minimum : ENNReal) + (next : ENNReal)) +
          delta * (difference : ENNReal) := by ac_rfl
    _ < p * (minimum : ENNReal) + delta * (difference : ENNReal) := by
      exact ENNReal.add_lt_add_right
        (ENNReal.mul_ne_top deltaFinite
          (ENNReal.natCast_ne_top difference)) room
    _ <= p * (minimum : ENNReal) + p * (difference : ENNReal) := by
      gcongr
    _ = p * (minimum : ENNReal) + p * (difference : ENNReal) := rfl

/-- The explicit charged switching failure bound is finite. -/
theorem layerFailureBound_ne_top
    (program : Algebraic.Program signature n g)
    (p : NNReal)
    (bound : Nat) :
    layerFailureBound program p bound ≠ ∞ := by
  unfold layerFailureBound
  apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
  apply ENNReal.pow_ne_top
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.coe_ne_top
  · exact ENNReal.natCast_ne_top _

/-- Iterated semantic depth reduction along an explicit survivor schedule.
The result is one cumulative restriction, not a sampled or searched-for
witness. This raw form permits arbitrary internal NOT gates. -/
theorem exists_shallowUpTo_with_liveCount_raw
    (program : Algebraic.Program signature n g)
    (depth bound : Nat)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      layerFailureBound program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        layerFailureBound program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    exists rho : PartialAssignment n,
      ShallowUpTo program rho depth bound /\
        retained depth <= rho.liveCount := by
  induction depth with
  | zero =>
      refine ⟨PartialAssignment.empty, ?_, ?_⟩
      · exact (shallowUpTo_zero_raw program
          (PartialAssignment.empty : PartialAssignment n)).mono oneLeBound
      · simpa using initial
  | succ prior inductionHypothesis =>
      obtain ⟨rho, shallow, survivors⟩ := inductionHypothesis
        (fun level before =>
          room level (Nat.lt_succ_of_lt before))
      obtain ⟨extension, next, nextSurvivors⟩ :=
        shallow.exists_refine_succ_with_liveCount_raw p atMostOne
          (retained (prior + 1))
          (layerRoom_mono
            (layerFailureBound_ne_top program p bound)
            failureLe survivors
            (room prior (Nat.lt_succ_self prior)))
      exact ⟨rho.refine extension, next, nextSurvivors⟩

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem exists_shallowUpTo_with_liveCount
    (program : Algebraic.Program signature n g)
    (_normal : NegationsAtInputs program)
    (depth bound : Nat)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      layerFailureBound program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        layerFailureBound program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    exists rho : PartialAssignment n,
      ShallowUpTo program rho depth bound /\
        retained depth <= rho.liveCount :=
  exists_shallowUpTo_with_liveCount_raw program depth bound oneLeBound p
    atMostOne retained initial failureLe room

end Program
end AC0
end Algebraic
