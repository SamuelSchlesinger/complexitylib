/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSwitching
public import Complexitylib.Algebraic.LowerBound.AC0.RestrictionAveraging

/-!
# Existential AC0 layer advancement with live variables

The probabilistic switching theorem is useful for depth reduction only after
one extracts a concrete refinement that both advances the semantic layer
invariant and keeps enough variables live. This module performs exactly that
averaging step.

For current live count `m`, requested survivor count `k`, and charged
switching failure bound `delta`, the sole numerical premise is

`delta * m + k < p * m`.

No restriction is computed or searched for: existence follows from the exact
first moment of the survivor count and the proved bad-event probability.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- Increasing the common tree-depth allowance preserves the semantic layer
invariant. -/
theorem ShallowUpTo.mono
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level smaller larger : Nat}
    (shallow : ShallowUpTo program rho level smaller)
    (le : smaller <= larger) :
    ShallowUpTo program rho level larger := by
  intro wire wireDepth
  exact (shallow wire wireDepth).mono le

/-- Charged-size failure bound for one semantic switching step. -/
noncomputable def layerFailureBound
    (program : Algebraic.Program signature n g)
    (p : NNReal)
    (bound : Nat) : ENNReal :=
  (program.cost andOrCost : ENNReal) *
    (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
      (bound + 1))

/-- A one-step switching estimate plus sufficient first-moment room produces
one refinement that advances the invariant and retains the requested number
of live variables. This raw form permits arbitrary internal NOT gates. -/
theorem ShallowUpTo.exists_refine_succ_with_liveCount_raw
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat)
    (room :
      layerFailureBound program p bound *
            (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    exists extension : PartialAssignment n,
      ShallowUpTo program (rho.refine extension) (level + 1) bound /\
        retained <= (rho.refine extension).liveCount := by
  classical
  obtain ⟨extension, succeeds, survivors⟩ :=
    RandomRestriction.exists_good_refinement_with_liveCount
      n p atMostOne rho
      (fun extension =>
        Not (ShallowUpTo program (rho.refine extension)
          (level + 1) bound))
      (layerFailureBound program p bound) retained
      (by
        simpa [layerFailureBound] using
          shallow.probability_not_succ_refine_le_five_raw p atMostOne)
      room
  exact ⟨extension, not_not.mp succeeds, survivors⟩

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem ShallowUpTo.exists_refine_succ_with_liveCount
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (_normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat)
    (room :
      layerFailureBound program p bound *
            (rho.liveCount : ENNReal) +
          (retained : ENNReal) <
        (p : ENNReal) * (rho.liveCount : ENNReal)) :
    exists extension : PartialAssignment n,
      ShallowUpTo program (rho.refine extension) (level + 1) bound /\
        retained <= (rho.refine extension).liveCount :=
  shallow.exists_refine_succ_with_liveCount_raw p atMostOne retained room

end Program
end AC0
end Algebraic
