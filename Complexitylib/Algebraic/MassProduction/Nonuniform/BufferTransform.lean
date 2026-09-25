/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.Nonuniform.BufferModel

/-!
# Composable buffer transformation contract

A buffer circuit preserves one original dataset and its geometric targets,
updates only the completed/pending state, and retains pairwise disjointness.
This property composes directly for circuits with successive buffer sizes.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.BufferModel

open BufferInput

/-- A circuit maps every valid encoded input state to a valid encoded output
state over the same original request dataset and targets. -/
def Transforms (positive : 0 < width) (targetProjection : Fin (dimension * width) → Fin requestWidth)
    (circuit : Circuit DeMorgan.signature
      (inputWidth completed pending requestWidth (2 ^ width) (dimension * width))
      (inputWidth nextCompleted nextPending requestWidth (2 ^ width) (dimension * width)))
    (total : Nat) : Prop :=
  ∀ (data : Fin total → Fin requestWidth → Bool)
    (targets : Fin total → Fin dimension → BinaryExtension width),
    Function.Injective data →
    (∀ request bit, data request (targetProjection bit) = binaryExtensionVectorBits positive (targets request) bit) →
    ∀ state : State total completed pending dimension width,
      WellScheduled state targets →
      ∃ next : State total nextCompleted nextPending dimension width,
        circuit.eval DeMorgan.interpretation (input positive state data targets) =
          input positive next data targets ∧ WellScheduled next targets

/-- Model-preserving buffer circuits compose with no change to their shared dataset. -/
theorem Transforms.comp (positive : 0 < width)
    (targetProjection : Fin (dimension * width) → Fin requestWidth)
    (first : Circuit DeMorgan.signature
      (inputWidth completed pending requestWidth (2 ^ width) (dimension * width))
      (inputWidth middleCompleted middlePending requestWidth (2 ^ width) (dimension * width)))
    (last : Circuit DeMorgan.signature
      (inputWidth middleCompleted middlePending requestWidth (2 ^ width) (dimension * width))
      (inputWidth nextCompleted nextPending requestWidth (2 ^ width) (dimension * width)))
    (firstCorrect : Transforms positive targetProjection first total)
    (lastCorrect : Transforms positive targetProjection last total) :
    Transforms positive targetProjection (last.comp first) total := by
  intro data targets distinct targetDataCorrect state previous
  obtain ⟨middle, firstOutput, middleValid⟩ := firstCorrect data targets distinct targetDataCorrect state previous
  obtain ⟨next, lastOutput, nextValid⟩ := lastCorrect data targets distinct targetDataCorrect middle middleValid
  refine ⟨next, ?_, nextValid⟩
  rw [Circuit.eval_comp, firstOutput, lastOutput]

end Algebraic.MassProduction.Nonuniform.BufferModel
