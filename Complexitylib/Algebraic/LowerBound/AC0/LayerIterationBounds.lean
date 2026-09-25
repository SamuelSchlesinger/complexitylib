/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerExistenceBounds
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIteration

/-!
# Iterated AC0 depth reduction with variable parameters

The source-faithful parity argument uses a different first restriction from
its later restrictions: the first round starts from literal width one, while
subsequent rounds start from the chosen tree bound. This module iterates the
existential layer theorem with explicit schedules

* `treeBound i` for the invariant after `i` rounds,
* `p i` for the next random restriction, and
* `retained i` for the guaranteed live-variable count.

At each round the caller supplies the exact switching failure and first-moment
inequalities. The resulting theorem constructs one cumulative restriction by
finite induction. It is purely structural and does not choose asymptotic
parameters, enumerate circuits, or search for witnesses.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- The charged two-parameter switching failure bound is finite. -/
theorem layerFailureBoundOfBounds_ne_top
    (program : Algebraic.Program signature n g)
    (p : NNReal)
    (sourceBound targetBound : Nat) :
    layerFailureBoundOfBounds program p sourceBound targetBound ≠ ∞ := by
  unfold layerFailureBoundOfBounds
  apply ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
  apply ENNReal.pow_ne_top
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact ENNReal.coe_ne_top
  · exact ENNReal.natCast_ne_top _

/-- Iterated semantic depth reduction along explicit restriction, tree-bound,
and survivor schedules. The result is one cumulative restriction satisfying
the scheduled final invariant. This raw form permits arbitrary internal NOT
gates. -/
theorem exists_shallowUpTo_with_liveCount_bounds_raw
    (program : Algebraic.Program signature n g)
    (rounds : Nat)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      layerFailureBoundOfBounds program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      layerFailureBoundOfBounds program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount := by
  induction rounds with
  | zero =>
      refine ⟨PartialAssignment.empty, ?_, ?_⟩
      · exact (shallowUpTo_zero_raw program
          (PartialAssignment.empty : PartialAssignment n)).mono
            oneLeInitialBound
      · simpa using initial
  | succ prior inductionHypothesis =>
      obtain ⟨rho, shallow, survivors⟩ := inductionHypothesis
        (fun level before => atMostOne level (Nat.lt_succ_of_lt before))
        (fun level before =>
          boundMonotone level (Nat.lt_succ_of_lt before))
        (fun level before => failureLe level (Nat.lt_succ_of_lt before))
        (fun level before => room level (Nat.lt_succ_of_lt before))
      obtain ⟨extension, next, nextSurvivors⟩ :=
        shallow.exists_refine_succ_with_liveCount_bounds_raw
          (boundMonotone prior (Nat.lt_succ_self prior))
          (p prior) (atMostOne prior (Nat.lt_succ_self prior))
          (retained (prior + 1))
          (layerRoom_mono
            (layerFailureBoundOfBounds_ne_top program (p prior)
              (treeBound prior) (treeBound (prior + 1)))
            (failureLe prior (Nat.lt_succ_self prior)) survivors
            (room prior (Nat.lt_succ_self prior)))
      exact ⟨rho.refine extension, next, nextSurvivors⟩

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem exists_shallowUpTo_with_liveCount_bounds
    (program : Algebraic.Program signature n g)
    (_normal : NegationsAtInputs program)
    (rounds : Nat)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      layerFailureBoundOfBounds program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      layerFailureBoundOfBounds program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal)) :
    ∃ rho : PartialAssignment n,
      ShallowUpTo program rho rounds (treeBound rounds) ∧
        retained rounds ≤ rho.liveCount :=
  exists_shallowUpTo_with_liveCount_bounds_raw program rounds treeBound
    oneLeInitialBound p atMostOne boundMonotone retained initial failureLe room

end Program
end AC0
end Algebraic
