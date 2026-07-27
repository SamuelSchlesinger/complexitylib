/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.FormulaSpace
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Space.Packed

/-!
# Whole-step space bound for direct transition generation

This module composes the formula and delayed-copy certificates through the
seven exact register phases of `emitStep`.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem StepWidthEnvelope.updateGateBound_space
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    StepWidthEnvelope tm
      (Function.update values Work.gateBound (values Work.available)) width := by
  constructor
  · exact BinaryRoutine.values_update_le Work.gateBound henvelope.values_le
      (henvelope.values_le Work.available)
  · intro state headTape writtenTape symbol stateIndex tapeIndex
      symbolIndex position hstate htape hsymbol hposition
    simpa [Work.gateBound, Work.available, Work.horizon, Work.configBase] using
      henvelope.cap state headTape writtenTape symbol stateIndex tapeIndex
        symbolIndex position hstate htape hsymbol hposition

/-- One complete packed transition step stays within its shared numeric width
envelope at every machine prefix. -/
theorem emitStep_spaceBoundByWidth_internal (tm : TM k)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm.toNTM (values inputLength) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStep tm) initialSpace values width := by
  let saveBound := BinaryRoutine.binaryCopy Work.available Work.gateBound
    Work.copyCounter
  let formulas := emitStepFormulas tm.toNTM
  let saveBase := BinaryRoutine.binaryCopy Work.available Work.configBase
    Work.copyCounter
  let restoreCount := BinaryRoutine.binaryCopy Work.gateBound Work.gateCount
    Work.copyCounter
  let packed := emitStepPackedCopies tm.toNTM
  let clearBound := BinaryRoutine.clear Work.gateBound
  let clearCount := BinaryRoutine.clear Work.gateCount
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    saveBound.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    formulas.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    saveBase.effect (values₂ inputLength)
  let values₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    restoreCount.effect (values₃ inputLength)
  let values₅ : ℕ → BinaryValues WorkCount := fun inputLength =>
    packed.effect (values₄ inputLength)
  let values₆ : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearBound.effect (values₅ inputLength)
  have hclean₁ : ∀ inputLength, StepClean (values₁ inputLength) := by
    intro inputLength
    simpa [values₁, saveBound, BinaryRoutine.binaryCopy] using
      (hclean inputLength).updateOuter_forEffect_internal
        (values inputLength) Work.gateBound
        (values inputLength Work.available) (Or.inl rfl)
  have henvelope₁ : ∀ inputLength,
      StepWidthEnvelope tm.toNTM (values₁ inputLength)
        (width inputLength) := by
    intro inputLength
    simpa [values₁, saveBound, BinaryRoutine.binaryCopy] using
      (henvelope inputLength).updateGateBound_space
  have hhorizon₁ : ∀ inputLength,
      0 < values₁ inputLength Work.horizon := by
    intro inputLength
    simpa [values₁, saveBound, BinaryRoutine.binaryCopy,
      Work.gateBound, Work.horizon] using hhorizon inputLength
  have h₁ : BinaryRoutine.SpaceBoundByWidthAt saveBound initialSpace
      values width := by
    dsimp only [saveBound]
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength =>
        (henvelope inputLength).values_le Work.available
    · exact fun inputLength =>
        (henvelope inputLength).values_le Work.gateBound
  have h₂ : BinaryRoutine.SpaceBoundByWidthAt formulas initialSpace
      values₁ width := by
    dsimp only [formulas]
    exact emitStepFormulas_spaceBoundByWidth_internal tm.toNTM hclean₁
      hhorizon₁ henvelope₁
  have hvalues₂ : ∀ inputLength index,
      values₂ inputLength index ≤ width inputLength := by
    intro inputLength index
    have heffect := emitStepFormulas_effect_internal tm.toNTM
      (values₁ inputLength) (hclean₁ inputLength)
      (hhorizon₁ inputLength)
    dsimp only [values₂, formulas]
    rw [heffect]
    apply BinaryRoutine.values_update_le Work.available
    · exact (henvelope₁ inputLength).values_le
    · exact (henvelope₁ inputLength).formulaFrontier_le_internal
  have hclean₂ : ∀ inputLength, StepClean (values₂ inputLength) := by
    intro inputLength
    have heffect := emitStepFormulas_effect_internal tm.toNTM
      (values₁ inputLength) (hclean₁ inputLength)
      (hhorizon₁ inputLength)
    dsimp only [values₂, formulas]
    rw [heffect]
    exact update_available_preserves_stepClean_internal
      (hclean₁ inputLength) _
  have h₃ : BinaryRoutine.SpaceBoundByWidthAt saveBase initialSpace
      values₂ width := by
    dsimp only [saveBase]
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hvalues₂ inputLength Work.available
    · exact fun inputLength => hvalues₂ inputLength Work.configBase
  have hvalues₃ : ∀ inputLength index,
      values₃ inputLength index ≤ width inputLength := by
    intro inputLength index
    dsimp only [values₃, saveBase]
    exact BinaryRoutine.values_update_le Work.configBase
      (hvalues₂ inputLength) (hvalues₂ inputLength Work.available)
      index
  have hclean₃ : ∀ inputLength, StepClean (values₃ inputLength) := by
    intro inputLength
    dsimp only [values₃, saveBase]
    exact (hclean₂ inputLength).updateOuter_forEffect_internal
      (values₂ inputLength) Work.configBase
      (values₂ inputLength Work.available) (Or.inr (Or.inl rfl))
  have h₄ : BinaryRoutine.SpaceBoundByWidthAt restoreCount initialSpace
      values₃ width := by
    dsimp only [restoreCount]
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · exact fun inputLength => hvalues₃ inputLength Work.gateBound
    · exact fun inputLength => hvalues₃ inputLength Work.gateCount
  have hvalues₄ : ∀ inputLength index,
      values₄ inputLength index ≤ width inputLength := by
    intro inputLength index
    dsimp only [values₄, restoreCount]
    exact BinaryRoutine.values_update_le Work.gateCount
      (hvalues₃ inputLength) (hvalues₃ inputLength Work.gateBound)
      index
  have hclean₄ : ∀ inputLength, StepClean (values₄ inputLength) := by
    intro inputLength
    dsimp only [values₄, restoreCount]
    exact (hclean₃ inputLength).updateOuter_forEffect_internal
      (values₃ inputLength) Work.gateCount
      (values₃ inputLength Work.gateBound)
      (Or.inr (Or.inr (Or.inl rfl)))
  have hhorizonEq₄ : ∀ inputLength,
      values₄ inputLength Work.horizon =
        values₁ inputLength Work.horizon := by
    intro inputLength
    have heffect := emitStepFormulas_effect_internal tm.toNTM
      (values₁ inputLength) (hclean₁ inputLength) (hhorizon₁ inputLength)
    dsimp only [values₄, values₃, values₂, restoreCount, saveBase, formulas]
    rw [heffect]
    simp [BinaryRoutine.binaryCopy,
      Work.gateCount, Work.configBase, Work.available, Work.gateBound,
      Work.horizon]
  have hgateCount₄ : ∀ inputLength,
      values₄ inputLength Work.gateCount =
        values₁ inputLength Work.available := by
    intro inputLength
    have heffect := emitStepFormulas_effect_internal tm.toNTM
      (values₁ inputLength) (hclean₁ inputLength) (hhorizon₁ inputLength)
    dsimp only [values₄, values₃, values₂, restoreCount, saveBase, formulas]
    rw [heffect]
    simp [values₁, saveBound, BinaryRoutine.binaryCopy,
      Work.gateCount, Work.configBase, Work.available, Work.gateBound]
  have havailable₄ : ∀ inputLength,
      values₄ inputLength Work.available =
        values₁ inputLength Work.available +
          stepFormulasEffectSizeInternal tm.toNTM
            (values₁ inputLength Work.horizon) := by
    intro inputLength
    simp [values₄, values₃, values₂, restoreCount, saveBase,
      formulas, BinaryRoutine.binaryCopy,
      emitStepFormulas_effect_internal tm.toNTM _ (hclean₁ inputLength)
        (hhorizon₁ inputLength),
      Work.gateCount, Work.configBase, Work.available, Work.gateBound,
      Work.horizon]
  have h₅ : BinaryRoutine.SpaceBoundByWidthAt packed initialSpace
      values₄ width := by
    dsimp only [packed]
    exact emitStepPackedCopies_spaceBoundByWidth_internal tm.toNTM hclean₄
      hvalues₄ henvelope₁ hhorizonEq₄ hgateCount₄ havailable₄
  have hgateBound₅ : ∀ inputLength,
      values₅ inputLength Work.gateBound ≤ width inputLength := by
    intro inputLength
    have heffect := emitStepPackedCopies_effect_internal tm.toNTM
      (values₄ inputLength) (hclean₄ inputLength)
    dsimp only [values₅, packed]
    rw [heffect]
    simpa [Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃, Work.gateBound] using
        hvalues₄ inputLength Work.gateBound
  have hgateCount₅ : ∀ inputLength,
      values₅ inputLength Work.gateCount ≤ width inputLength := by
    intro inputLength
    have heffect := emitStepPackedCopies_effect_internal tm.toNTM
      (values₄ inputLength) (hclean₄ inputLength)
    have hfrontier :=
      (henvelope₁ inputLength).formulaFrontier_le_internal
    dsimp only [values₅, packed]
    rw [heffect]
    simp [Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
    change values₄ inputLength Work.gateCount +
        stepFormulasEffectSizeInternal tm.toNTM
          (values₄ inputLength Work.horizon) ≤ width inputLength
    rw [hgateCount₄ inputLength, hhorizonEq₄ inputLength]
    exact hfrontier
  have h₆ : BinaryRoutine.SpaceBoundByWidthAt clearBound initialSpace
      values₅ width := by
    dsimp only [clearBound]
    exact BinaryRoutine.SpaceBoundByWidthAt.clear Work.gateBound hgateBound₅
  have hgateCount₆ : ∀ inputLength,
      values₆ inputLength Work.gateCount ≤ width inputLength := by
    intro inputLength
    dsimp only [values₆, clearBound]
    simpa [BinaryRoutine.clear, Work.gateBound, Work.gateCount] using
      hgateCount₅ inputLength
  have h₇ : BinaryRoutine.SpaceBoundByWidthAt clearCount initialSpace
      values₆ width := by
    dsimp only [clearCount]
    exact BinaryRoutine.SpaceBoundByWidthAt.clear Work.gateCount hgateCount₆
  rw [emitStep]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨h₁, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt formulas initialSpace values₁ width ∧ _
  refine ⟨h₂, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt saveBase initialSpace values₂ width ∧ _
  refine ⟨h₃, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt restoreCount initialSpace values₃ width ∧ _
  refine ⟨h₄, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt packed initialSpace values₄ width ∧ _
  refine ⟨h₅, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt clearBound initialSpace values₅ width ∧ _
  refine ⟨h₆, ?_⟩
  change BinaryRoutine.SpaceBoundByWidthAt clearCount initialSpace values₆ width ∧ _
  exact ⟨h₇, trivial⟩

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
