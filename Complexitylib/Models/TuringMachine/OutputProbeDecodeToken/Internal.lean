/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Shared formula-token decoder layout -- internals
-/

namespace Complexity

namespace TM

theorem OutputProbeDecodeTokenLayout.tagLayout_cursorIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.cursorIdx = layout.natLayout.cursorIdx := by
  rfl

theorem OutputProbeDecodeTokenLayout.tagLayout_scratchIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.scratchIdx = layout.natLayout.scratchIdx := by
  rfl

theorem OutputProbeDecodeTokenLayout.tagLayout_tag₀Idx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₀Idx = layout.roles 2 := by
  rfl

theorem OutputProbeDecodeTokenLayout.tagLayout_tag₁Idx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₁Idx = layout.roles 3 := by
  rfl

theorem OutputProbeDecodeTokenLayout.tagLayout_tag₂Idx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₂Idx = layout.roles 4 := by
  rfl

theorem OutputProbeDecodeTokenLayout.natLayout_valueIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.valueIdx = layout.roles 5 := by
  rfl

theorem OutputProbeDecodeTokenLayout.natLayout_activeIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.activeIdx = layout.roles 6 := by
  rfl

theorem OutputProbeDecodeTokenLayout.natLayout_loopIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.loopIdx = layout.roles 7 := by
  rfl

theorem OutputProbeDecodeTokenLayout.natLayout_fuelIdx_internal
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.fuelIdx = layout.roles 8 := by
  rfl

theorem outputProbeDecodeTokenClearedTagExtras_eq_of_ne_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (idx : Fin (0 + outputProbeControllerTapes n + controllerTapes))
    (htag₀ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)
    (htag₁ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)
    (htag₂ : idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx) :
    outputProbeDecodeTokenClearedTagExtras n layout outerExtras idx =
      outerExtras idx := by
  simp [outputProbeDecodeTokenClearedTagExtras, htag₀, htag₁, htag₂]

/-- Every controller register other than the shared cursor and retained tag
bits is unchanged by complete tag probing and cleanup. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_other_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool) (idx : Fin controllerTapes)
    (hcursor : idx ≠ layout.tagLayout.cursorIdx)
    (htag₀ : idx ≠ layout.tagLayout.tag₀Idx)
    (htag₁ : idx ≠ layout.tagLayout.tag₁Idx)
    (htag₂ : idx ≠ layout.tagLayout.tag₂Idx) :
    outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor tag₀
        tag₁ tag₂ (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  rw [outputProbeDecodeTokenOuterExtrasAfter]
  rw [outputProbeDecodeTokenClearedTagExtras_eq_of_ne_internal n layout _ _
    (fun heq => htag₀ (outputProbeIndexedControllerIdx_injective n heq))
    (fun heq => htag₁ (outputProbeIndexedControllerIdx_injective n heq))
    (fun heq => htag₂ (outputProbeIndexedControllerIdx_injective n heq))]
  rw [outputProbeDecodeTagOuterExtrasAfter]
  rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n
    layout.tagLayout layout.tagLayout.tag₂Idx idx hcursor htag₂]
  rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n
    layout.tagLayout layout.tagLayout.tag₁Idx idx hcursor htag₁]
  rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n
    layout.tagLayout layout.tagLayout.tag₀Idx idx hcursor htag₀]

/-- Complete tag probing and cleanup leave the shared cursor canonically
advanced by three positions. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_cursor_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool) :
    (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor tag₀
      tag₁ tag₂ (outputProbeDecodeTagCursorIdx n layout.tagLayout))
        |>.HasBinaryNat (cursor + 3) := by
  have hcursorTag₀ :
      layout.tagLayout.cursorIdx ≠ layout.tagLayout.tag₀Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  have hcursorTag₁ :
      layout.tagLayout.cursorIdx ≠ layout.tagLayout.tag₁Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  have hcursorTag₂ :
      layout.tagLayout.cursorIdx ≠ layout.tagLayout.tag₂Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  rw [outputProbeDecodeTokenOuterExtrasAfter]
  change (outputProbeDecodeTokenClearedTagExtras n layout
    (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
      cursor tag₀ tag₁ tag₂)
    (outputProbeIndexedControllerIdx n layout.tagLayout.cursorIdx))
      |>.HasBinaryNat (cursor + 3)
  rw [outputProbeDecodeTokenClearedTagExtras_eq_of_ne_internal n layout _ _
    (fun heq => hcursorTag₀
      (outputProbeIndexedControllerIdx_injective n heq))
    (fun heq => hcursorTag₁
      (outputProbeIndexedControllerIdx_injective n heq))
    (fun heq => hcursorTag₂
      (outputProbeIndexedControllerIdx_injective n heq))]
  simpa [outputProbeDecodeTagOuterExtrasAfter, Nat.add_assoc] using
    outputProbeDecodeTagBitOuterExtrasAfter_cursor_internal n
      layout.tagLayout layout.tagLayout.tag₂Idx
      (outputProbeDecodeTagBitOuterExtrasAfter n layout.tagLayout
        layout.tagLayout.tag₁Idx
        (outputProbeDecodeTagBitOuterExtrasAfter n layout.tagLayout
          layout.tagLayout.tag₀Idx outerExtras cursor tag₀)
        (cursor + 1) tag₁)
      (cursor + 2) tag₂

/-- Complete tag probing followed by canonical cleanup preserves the parked
outer-frame invariant. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (htag₀Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
        cursor tag₀ tag₁ tag₂ i) := by
  have hzeroParked : Parked (outputProbeCounterTape 0) := by
    have hzero : (outputProbeCounterTape 0).HasBinaryNat 0 := by
      simpa [outputProbeCounterTape] using
        Tape.init_move_right_hasBinaryNat 0
    refine ⟨by rw [hzero.2.1], ?_⟩
    exact Tape.HasBinaryContent.cells_ne_start hzero.2.2
  have updateParked : ∀
      (base : Fin (0 + outputProbeControllerTapes n +
        controllerTapes) → Tape),
      (∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (base i)) →
      ∀ idx i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (Function.update base idx (outputProbeCounterTape 0) i) := by
    intro base hbase idx i hi
    by_cases heq : i = idx
    · subst i
      rw [Function.update_self]
      exact hzeroParked
    · rw [Function.update_of_ne heq]
      exact hbase i hi
  let after := outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout
    outerExtras cursor tag₀ tag₁ tag₂
  obtain ⟨hafter, _htag₀, _htag₁, _htag₂⟩ :=
    outputProbeDecodeTagOuterExtrasAfter_invariant_internal n
      layout.tagLayout outerExtras houter cursor tag₀ tag₁ tag₂
      htag₀Zero htag₁Zero htag₂Zero
  let idx₀ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx
  let idx₁ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx
  let idx₂ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx
  have houter₀ := updateParked after hafter idx₀
  have houter₁ := updateParked
    (Function.update after idx₀ (outputProbeCounterTape 0))
    houter₀ idx₁
  have houter₂ := updateParked
    (Function.update
      (Function.update after idx₀ (outputProbeCounterTape 0)) idx₁
      (outputProbeCounterTape 0))
    houter₁ idx₂
  simpa [outputProbeDecodeTokenOuterExtrasAfter,
    outputProbeDecodeTokenClearedTagExtras, after, idx₀, idx₁, idx₂]
    using houter₂

theorem outputProbeDecodeTokenClearedTagExtras_tag₀_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)).HasBinaryNat
        0 := by
  have h₀₁ : layout.tagLayout.tag₀Idx ≠ layout.tagLayout.tag₁Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  have h₀₂ : layout.tagLayout.tag₀Idx ≠ layout.tagLayout.tag₂Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  have hphysical₀₁ : outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx := by
    exact fun heq => h₀₁ (outputProbeIndexedControllerIdx_injective n heq)
  have hphysical₀₂ : outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx := by
    exact fun heq => h₀₂ (outputProbeIndexedControllerIdx_injective n heq)
  simpa [outputProbeDecodeTokenClearedTagExtras, hphysical₀₁,
    hphysical₀₂] using Tape.init_move_right_hasBinaryNat 0

theorem outputProbeDecodeTokenClearedTagExtras_tag₁_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)).HasBinaryNat
        0 := by
  have h₁₂ : layout.tagLayout.tag₁Idx ≠ layout.tagLayout.tag₂Idx :=
    layout.tagLayout.roles.injective.ne (by decide)
  have hphysical₁₂ : outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx ≠
      outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx := by
    exact fun heq => h₁₂ (outputProbeIndexedControllerIdx_injective n heq)
  simpa [outputProbeDecodeTokenClearedTagExtras, hphysical₁₂] using
    Tape.init_move_right_hasBinaryNat 0

theorem outputProbeDecodeTokenClearedTagExtras_tag₂_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx)).HasBinaryNat
        0 := by
  simpa [outputProbeDecodeTokenClearedTagExtras] using
    Tape.init_move_right_hasBinaryNat 0

private theorem outputProbeDecodeToken_hasBinaryNat_parked_internal
    {tape : Tape} {value : ℕ} (hvalue : tape.HasBinaryNat value) :
    Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

private theorem outputProbeDecodeToken_update_parked_internal
    (outerExtras : Fin controllerTapes → Tape)
    (eligible : Fin controllerTapes → Prop)
    (houter : ∀ i, eligible i → Parked (outerExtras i))
    (idx : Fin controllerTapes) :
    ∀ i, eligible i → Parked (Function.update outerExtras idx
      (outputProbeCounterTape 0) i) := by
  intro i hiEligible
  by_cases hi : i = idx
  · subst i
    rw [Function.update_self]
    exact outputProbeDecodeToken_hasBinaryNat_parked_internal
      (Tape.init_move_right_hasBinaryNat 0)
  · rw [Function.update_of_ne hi]
    exact houter i hiEligible

private theorem outputProbeDecodeTokenClear_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes) (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat
        value) :
    (clearWorkTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape 0))
        input output extras false)
      (clearWorkTimeBound value.bits.length) := by
  let physical := outputProbeIndexedControllerIdx n idx
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htargetNat : (work physical).HasBinaryNat value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hvalue
  have htarget : work physical =
      (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right :=
    htargetNat.eq_init_move_right
  have hclear := clearWorkTM_hoareTime_frame physical value.bits inp work out
    htarget hinput (fun i _ => hwork i) hout
  obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone, hworkDone,
      houtputDone⟩ := hclear inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, elapsed, ?_, hreach, hhalt, ?_⟩
  · simpa using helapsed
  · rw [hinputDone, hworkDone, houtputDone]
    simpa [physical, outputProbeCounterTape] using
      outputProbeLatchFramePost_updateController tm controllerTapes
        outerExtras input output extras false inp work out hpost idx
        (outputProbeCounterTape 0)

private theorem outputProbeDecodeTokenFramePost_to_pre_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) :
    ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false (transitionInput inp)
          (fun i => transitionTape (work i)) (transitionTape out) := by
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  rw [hinput.transitionInput_eq_self]
  have hworkTransition : (fun i => transitionTape (work i)) = work := by
    funext i
    exact (hwork i).transitionTape_eq_self
  rw [hworkTransition, hout.transitionTape_eq_self]
  exact hpost

theorem outputProbeDecodeTokenClearTagsTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (tag₀ tag₁ tag₂ : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0)) :
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (outputProbeDecodeTokenClearTagsTime tag₀ tag₁ tag₂) := by
  let idx₀ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx
  let idx₁ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx
  let idx₂ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx
  have hidx₀₁ : idx₀ ≠ idx₁ := by
    intro heq
    have hlogical := outputProbeIndexedControllerIdx_injective n heq
    exact (layout.tagLayout.roles.injective.ne (by decide)) hlogical
  have hidx₀₂ : idx₀ ≠ idx₂ := by
    intro heq
    have hlogical := outputProbeIndexedControllerIdx_injective n heq
    exact (layout.tagLayout.roles.injective.ne (by decide)) hlogical
  have hidx₁₂ : idx₁ ≠ idx₂ := by
    intro heq
    have hlogical := outputProbeIndexedControllerIdx_injective n heq
    exact (layout.tagLayout.roles.injective.ne (by decide)) hlogical
  let outer₁ := Function.update outerExtras idx₀ (outputProbeCounterTape 0)
  let outer₂ := Function.update outer₁ idx₁ (outputProbeCounterTape 0)
  have houter₁ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₁ i) :=
    outputProbeDecodeToken_update_parked_internal outerExtras
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter idx₀
  have houter₂ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₂ i) :=
    outputProbeDecodeToken_update_parked_internal outer₁
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter₁ idx₁
  have htag₁₁ : (outer₁ idx₁).HasBinaryNat
      (if tag₁ then 1 else 0) := by
    simpa [outer₁, Function.update_of_ne (Ne.symm hidx₀₁)] using htag₁
  have htag₂₁ : (outer₁ idx₂).HasBinaryNat
      (if tag₂ then 1 else 0) := by
    simpa [outer₁, Function.update_of_ne (Ne.symm hidx₀₂)] using
      htag₂
  have htag₂₂ : (outer₂ idx₂).HasBinaryNat
      (if tag₂ then 1 else 0) := by
    simpa [outer₂, Function.update_of_ne (Ne.symm hidx₁₂)] using
      htag₂₁
  have hclear₀ := outputProbeDecodeTokenClear_hoareTime_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    layout.tagLayout.tag₀Idx (if tag₀ then 1 else 0) htag₀
  have hclear₁ := outputProbeDecodeTokenClear_hoareTime_internal tm
    controllerTapes outer₁ input output extras hextras houter₁ houtput
    layout.tagLayout.tag₁Idx (if tag₁ then 1 else 0) htag₁₁
  have hclear₂ := outputProbeDecodeTokenClear_hoareTime_internal tm
    controllerTapes outer₂ input output extras hextras houter₂ houtput
    layout.tagLayout.tag₂Idx (if tag₂ then 1 else 0) htag₂₂
  have hseam₁ := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes outer₁ input output extras hextras houter₁ houtput
  have hseam₂ := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes outer₂ input output extras hextras houter₂ houtput
  have hclear₁₂ := seqTM_hoareTime
    (clearWorkTM idx₁) (clearWorkTM idx₂) hclear₁ hseam₂ hclear₂
  have hfull := seqTM_hoareTime
    (clearWorkTM idx₀) (seqTM (clearWorkTM idx₁) (clearWorkTM idx₂))
    hclear₀ hseam₁ hclear₁₂
  simpa [outputProbeDecodeTokenClearTagsTM,
    outputProbeDecodeTokenClearedTagExtras,
    outputProbeDecodeTokenClearTagsTime, outer₁, outer₂, idx₀, idx₁,
    idx₂] using hfull

theorem outputProbeDecodeTokenDispatchTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (tag₀ tag₁ tag₂ : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0))
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Option OutputProbeTokenTag →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {varTime truTime flsTime negTime conjTime disjTime invalidTime : ℕ}
    (hvar : onVar.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .var)) varTime)
    (htru : onTru.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .tru)) truTime)
    (hfls : onFls.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .fls)) flsTime)
    (hneg : onNeg.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .neg)) negTime)
    (hconj : onConj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .conj)) conjTime)
    (hdisj : onDisj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post (some .disj)) disjTime)
    (hinvalid : onInvalid.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
        input output extras false)
      (post none) invalidTime) :
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (post (outputProbeTokenTag? tag₀ tag₁ tag₂))
        (outputProbeDecodeTokenDispatchTime tag₀ tag₁ tag₂ varTime
          truTime flsTime negTime conjTime disjTime invalidTime) := by
  let cleared := outputProbeDecodeTokenClearedTagExtras n layout outerExtras
  let idx₀ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx
  let idx₁ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx
  let idx₂ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx
  let outer₁ := Function.update outerExtras idx₀ (outputProbeCounterTape 0)
  let outer₂ := Function.update outer₁ idx₁ (outputProbeCounterTape 0)
  have houter₁ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₁ i) :=
    outputProbeDecodeToken_update_parked_internal outerExtras
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter idx₀
  have houter₂ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₂ i) :=
    outputProbeDecodeToken_update_parked_internal outer₁
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter₁ idx₁
  have hcleared : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (cleared i) := by
    simpa [cleared, outputProbeDecodeTokenClearedTagExtras, outer₁, outer₂,
      idx₀, idx₁, idx₂] using
      outputProbeDecodeToken_update_parked_internal outer₂
        (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
        houter₂ idx₂
  have hclear := outputProbeDecodeTokenClearTagsTM_hoareTime_internal tm
    controllerTapes layout outerExtras input output extras tag₀ tag₁ tag₂
    hextras houter houtput htag₀ htag₁ htag₂
  have hseam := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes cleared input output extras hextras hcleared houtput
  have hvar' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onVar hclear
    hseam hvar
  have htru' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onTru hclear
    hseam htru
  have hfls' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onFls hclear
    hseam hfls
  have hneg' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onNeg hclear
    hseam hneg
  have hconj' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onConj hclear
    hseam hconj
  have hdisj' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onDisj hclear
    hseam hdisj
  have hinvalid' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onInvalid
    hclear hseam hinvalid
  have hdispatch := outputProbeDecodeTagDispatchTM_hoareTime_internal tm
    controllerTapes layout.tagLayout outerExtras input output extras tag₀ tag₁
    tag₂ hextras houter houtput htag₀ htag₁ htag₂
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onVar)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onTru)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onFls)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onNeg)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onConj)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onDisj)
    (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout)
      onInvalid)
    (post := post) (by simpa [cleared] using hvar')
      (by simpa [cleared] using htru') (by simpa [cleared] using hfls')
      (by simpa [cleared] using hneg') (by simpa [cleared] using hconj')
      (by simpa [cleared] using hdisj') (by simpa [cleared] using hinvalid')
  simpa [outputProbeDecodeTokenDispatchTM,
    outputProbeDecodeTokenDispatchTime] using hdispatch

private theorem outputProbeTokenContinuation_seqTM_internal
    (before : TM tapes)
    (tag : Option OutputProbeTokenTag)
    (onVar onTru onFls onNeg onConj onDisj onInvalid : TM tapes) :
    outputProbeTokenContinuation tag
        (seqTM before onVar) (seqTM before onTru) (seqTM before onFls)
        (seqTM before onNeg) (seqTM before onConj) (seqTM before onDisj)
        (seqTM before onInvalid) =
      seqTM before (outputProbeTokenContinuation tag onVar onTru onFls
        onNeg onConj onDisj onInvalid) := by
  cases tag with
  | none => rfl
  | some tag => cases tag <;> rfl

theorem outputProbeDecodeTokenDispatchTM_selected_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (tag₀ tag₁ tag₂ : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0))
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {selectedTime : ℕ}
    (hselected :
      (outputProbeTokenContinuation
        (outputProbeTokenTag? tag₀ tag₁ tag₂)
        onVar onTru onFls onNeg onConj onDisj onInvalid).HoareTime
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeTokenClearedTagExtras n layout outerExtras)
            input output extras false)
          post selectedTime) :
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        post (outputProbeDecodeTokenSelectedDispatchTime tag₀ tag₁ tag₂
          selectedTime) := by
  let cleared := outputProbeDecodeTokenClearedTagExtras n layout outerExtras
  let idx₀ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx
  let idx₁ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx
  let idx₂ := outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx
  let outer₁ := Function.update outerExtras idx₀ (outputProbeCounterTape 0)
  let outer₂ := Function.update outer₁ idx₁ (outputProbeCounterTape 0)
  have houter₁ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₁ i) :=
    outputProbeDecodeToken_update_parked_internal outerExtras
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter idx₀
  have houter₂ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₂ i) :=
    outputProbeDecodeToken_update_parked_internal outer₁
      (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
      houter₁ idx₁
  have hcleared : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (cleared i) := by
    simpa [cleared, outputProbeDecodeTokenClearedTagExtras, outer₁, outer₂,
      idx₀, idx₁, idx₂] using
      outputProbeDecodeToken_update_parked_internal outer₂
        (fun i => ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i)
        houter₂ idx₂
  have hclear := outputProbeDecodeTokenClearTagsTM_hoareTime_internal tm
    controllerTapes layout outerExtras input output extras tag₀ tag₁ tag₂
    hextras houter houtput htag₀ htag₁ htag₂
  have hseam := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes cleared input output extras hextras hcleared houtput
  have hselected' := seqTM_hoareTime
    (outputProbeDecodeTokenClearTagsTM n controllerTapes layout)
    (outputProbeTokenContinuation (outputProbeTokenTag? tag₀ tag₁ tag₂)
      onVar onTru onFls onNeg onConj onDisj onInvalid)
    hclear hseam (by simpa [cleared] using hselected)
  have hdispatch :=
    outputProbeDecodeTagDispatchTM_selected_hoareTime_internal tm
      controllerTapes layout.tagLayout outerExtras input output extras tag₀
      tag₁ tag₂ hextras houter houtput htag₀ htag₁ htag₂
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onVar)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onTru)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onFls)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onNeg)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onConj)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout) onDisj)
      (seqTM (outputProbeDecodeTokenClearTagsTM n controllerTapes layout)
        onInvalid)
      (post := post)
      (by
        rw [outputProbeTokenContinuation_seqTM_internal]
        exact hselected')
  simpa [outputProbeDecodeTokenDispatchTM,
    outputProbeDecodeTokenSelectedDispatchTime] using hdispatch

theorem ComputesInSpace.outputProbeDecodeTokenTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit₀ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (hlimit₁ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 2) ≤ cleanupLimit)
    (hlimit₂ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 3) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras
        (outputProbeDecodeTagCursorIdx n layout.tagLayout)).HasBinaryNat
          cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.tagLayout.scratchIdx))
        |>.HasBinaryNat 0)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0)
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Option OutputProbeTokenTag →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {varTime truTime flsTime negTime conjTime disjTime invalidTime : ℕ}
    (hvar : onVar.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .var)) varTime)
    (htru : onTru.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .tru)) truTime)
    (hfls : onFls.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .fls)) flsTime)
    (hneg : onNeg.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .neg)) negTime)
    (hconj : onConj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .conj)) conjTime)
    (hdisj : onDisj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post (some .disj)) disjTime)
    (hinvalid : onInvalid.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenClearedTagExtras n layout
          (outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout outerExtras
            cursor ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2])))
        input output extras false)
      (post none) invalidTime) :
    ∃ (bound₀ bound₁ bound₂ : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeTokenTM tm controllerTapes layout onVar onTru onFls
        onNeg onConj onDisj onInvalid).HoareTime pre
          (post (outputProbeTokenTag? ((f input)[cursor])
            ((f input)[cursor + 1]) ((f input)[cursor + 2])))
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) varTime
              truTime flsTime negTime conjTime disjTime invalidTime) := by
  have hbound₀ : cursor < (f input).length := by omega
  have hbound₁ : cursor + 1 < (f input).length := by omega
  have hbound₂ : cursor + 2 < (f input).length := hcursorBound
  let tag₀ := (f input)[cursor]'hbound₀
  let tag₁ := (f input)[cursor + 1]'hbound₁
  let tag₂ := (f input)[cursor + 2]'hbound₂
  let after := outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout
    outerExtras cursor tag₀ tag₁ tag₂
  obtain ⟨hafter, hafterTag₀, hafterTag₁, hafterTag₂⟩ :=
    outputProbeDecodeTagOuterExtrasAfter_invariant_internal n layout.tagLayout
      outerExtras houter cursor tag₀ tag₁ tag₂ htag₀ htag₁ htag₂
  obtain ⟨bound₀, bound₁, bound₂, pre, hpre, hdecode⟩ :=
    hcomp.outputProbeDecodeTagTM_hoareTime_internal input cursor hcursorBound
      output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout.tagLayout
      outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
  have hdispatch := outputProbeDecodeTokenDispatchTM_hoareTime_internal tm
    controllerTapes layout after input output extras tag₀ tag₁ tag₂ hextras
    hafter houtput hafterTag₀ hafterTag₁ hafterTag₂ onVar onTru onFls onNeg
    onConj onDisj onInvalid (post := post)
    (by simpa [after, tag₀, tag₁, tag₂] using hvar)
    (by simpa [after, tag₀, tag₁, tag₂] using htru)
    (by simpa [after, tag₀, tag₁, tag₂] using hfls)
    (by simpa [after, tag₀, tag₁, tag₂] using hneg)
    (by simpa [after, tag₀, tag₁, tag₂] using hconj)
    (by simpa [after, tag₀, tag₁, tag₂] using hdisj)
    (by simpa [after, tag₀, tag₁, tag₂] using hinvalid)
  have hseam := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes after input output extras hextras hafter houtput
  have hfull := seqTM_hoareTime
    (outputProbeDecodeTagTM tm controllerTapes layout.tagLayout)
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid)
    (by simpa [after, tag₀, tag₁, tag₂] using hdecode) hseam hdispatch
  refine ⟨bound₀, bound₁, bound₂, pre, hpre, ?_⟩
  simpa [outputProbeDecodeTokenTM, after, tag₀, tag₁, tag₂] using hfull

theorem ComputesInSpace.outputProbeDecodeTokenTM_selected_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit₀ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (hlimit₁ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 2) ≤ cleanupLimit)
    (hlimit₂ : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 3) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras
        (outputProbeDecodeTagCursorIdx n layout.tagLayout)).HasBinaryNat
          cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.tagLayout.scratchIdx))
        |>.HasBinaryNat 0)
    (htag₀ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0)
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {selectedTime : ℕ}
    (hselected :
      (outputProbeTokenContinuation
        (outputProbeTokenTag? ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        onVar onTru onFls onNeg onConj onDisj onInvalid).HoareTime
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
              cursor ((f input)[cursor]) ((f input)[cursor + 1])
              ((f input)[cursor + 2]))
            input output extras false)
          post selectedTime) :
    ∃ (bound₀ bound₁ bound₂ : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeTokenTM tm controllerTapes layout onVar onTru onFls
        onNeg onConj onDisj onInvalid).HoareTime pre post
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) selectedTime) := by
  have hbound₀ : cursor < (f input).length := by omega
  have hbound₁ : cursor + 1 < (f input).length := by omega
  have hbound₂ : cursor + 2 < (f input).length := hcursorBound
  let tag₀ := (f input)[cursor]'hbound₀
  let tag₁ := (f input)[cursor + 1]'hbound₁
  let tag₂ := (f input)[cursor + 2]'hbound₂
  let after := outputProbeDecodeTagOuterExtrasAfter n layout.tagLayout
    outerExtras cursor tag₀ tag₁ tag₂
  obtain ⟨hafter, hafterTag₀, hafterTag₁, hafterTag₂⟩ :=
    outputProbeDecodeTagOuterExtrasAfter_invariant_internal n layout.tagLayout
      outerExtras houter cursor tag₀ tag₁ tag₂ htag₀ htag₁ htag₂
  obtain ⟨bound₀, bound₁, bound₂, pre, hpre, hdecode⟩ :=
    hcomp.outputProbeDecodeTagTM_hoareTime_internal input cursor hcursorBound
      output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout.tagLayout
      outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
  have hdispatch :=
    outputProbeDecodeTokenDispatchTM_selected_hoareTime_internal tm
      controllerTapes layout after input output extras tag₀ tag₁ tag₂
      hextras hafter houtput hafterTag₀ hafterTag₁ hafterTag₂ onVar onTru
      onFls onNeg onConj onDisj onInvalid (post := post)
      (by simpa [after, tag₀, tag₁, tag₂] using hselected)
  have hseam := outputProbeDecodeTokenFramePost_to_pre_internal tm
    controllerTapes after input output extras hextras hafter houtput
  have hfull := seqTM_hoareTime
    (outputProbeDecodeTagTM tm controllerTapes layout.tagLayout)
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid)
    (by simpa [after, tag₀, tag₁, tag₂] using hdecode) hseam hdispatch
  refine ⟨bound₀, bound₁, bound₂, pre, hpre, ?_⟩
  simpa [outputProbeDecodeTokenTM, after, tag₀, tag₁, tag₂] using hfull

/-- Internal Hoare contract for the concrete variable continuation after a
complete tag probe and cleanup. -/
theorem ComputesInSpace.outputProbeDecodeTokenVar_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx))
        |>.HasBinaryNat 0)
    (htag₀Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0)
    (hvalue :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx))
        |>.HasBinaryNat 0)
    (hactive :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.activeIdx))
        |>.HasBinaryNat 1)
    (hloop :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.loopIdx))
        |>.HasBinaryNat 0)
    (fuelValue : ℕ)
    (hfuel :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.fuelIdx))
        |>.HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        { cursor := cursor + 3, value := 0, active := true } value).active =
          true →
      (outputProbeDecodeNatStateAt (f input)
        { cursor := cursor + 3, value := 0, active := true } value).cursor <
          (f input).length)
    (hqueryLimit : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        { cursor := cursor + 3, value := 0, active := true } value).active =
          true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input)
          { cursor := cursor + 3, value := 0, active := true } value).cursor +
            1) ≤ cleanupLimit) :
    ∃ bodyTime : ℕ → ℕ,
      (outputProbeDecodeNatTM tm controllerTapes layout.natLayout.cursorIdx
        layout.natLayout.scratchIdx layout.natLayout.valueIdx
        layout.natLayout.activeIdx layout.natLayout.loopIdx
        layout.natLayout.fuelIdx).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
            tag₀ tag₁ tag₂)
          input output extras false)
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatLoopOuterExtras n layout.natLayout.cursorIdx
            layout.natLayout.valueIdx layout.natLayout.activeIdx
            layout.natLayout.loopIdx
            (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
              tag₀ tag₁ tag₂)
            (outputProbeDecodeNatStateAt (f input)
              { cursor := cursor + 3, value := 0, active := true } fuelValue)
            fuelValue)
          input output extras false)
        (binaryForLoopTime bodyTime fuelValue 0 fuelValue) := by
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
    cursor tag₀ tag₁ tag₂
  let initial : OutputProbeDecodeNatState :=
    { cursor := cursor + 3, value := 0, active := true }
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    simpa [after] using outputProbeDecodeTokenOuterExtrasAfter_parked_internal
      n layout outerExtras houter cursor tag₀ tag₁ tag₂ htag₀Zero
      htag₁Zero htag₂Zero
  have hcursorAfter :
      (after (outputProbeDecodeNatCursorIdx n
        layout.natLayout.cursorIdx)).HasBinaryNat (cursor + 3) := by
    simpa [after] using
      outputProbeDecodeTokenOuterExtrasAfter_cursor_internal n layout
        outerExtras cursor tag₀ tag₁ tag₂
  have hscratchAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout
      outerExtras cursor tag₀ tag₁ tag₂ layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hscratch
  have hvalueAfter :
      (after (outputProbeDecodeNatValueIdx n
        layout.natLayout.valueIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.valueIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout
      outerExtras cursor tag₀ tag₁ tag₂ layout.natLayout.valueIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hvalue
  have hactiveAfter :
      (after (outputProbeDecodeNatActiveIdx n
        layout.natLayout.activeIdx)).HasBinaryNat 1 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.activeIdx)).HasBinaryNat 1
    rw [outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout
      outerExtras cursor tag₀ tag₁ tag₂ layout.natLayout.activeIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hactive
  have hloopAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.loopIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.loopIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout
      outerExtras cursor tag₀ tag₁ tag₂ layout.natLayout.loopIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hloop
  have hfuelAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.fuelIdx)).HasBinaryNat fuelValue := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.fuelIdx)).HasBinaryNat fuelValue
    rw [outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout
      outerExtras cursor tag₀ tag₁ tag₂ layout.natLayout.fuelIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hfuel
  have hinitial : outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after initial 0 =
        after :=
    outputProbeDecodeNatLoopOuterExtras_eq_self_internal n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after initial 0
      hcursorAfter hvalueAfter hactiveAfter hloopAfter
  obtain ⟨bodyTime, hdecode⟩ :=
    hcomp.outputProbeDecodeNatTM_hoareTime_internal input output houtput
      extras hextras hcleanupCounter cleanupLimit hcleanupLimit
      controllerTapes layout.natLayout after hafter initial hscratchAfter 0
      fuelValue (Nat.zero_le fuelValue) hfuelAfter
      (fun value _hzero hvalue => hqueryValid value hvalue)
      (fun value _hzero hvalue => hqueryLimit value hvalue)
  refine ⟨bodyTime, ?_⟩
  simpa [after, initial, outputProbeDecodeNatStateAt,
    outputProbeDecodeNatRun, hinitial] using hdecode

theorem outputProbeDecodeTokenClearTagsTM_isTransducer_internal
    (n controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenClearTagsTM n controllerTapes
      layout).IsTransducer := by
  apply IsTransducer.seqTM
  · exact clearWorkTM_isTransducer _
  · apply IsTransducer.seqTM <;> exact clearWorkTM_isTransducer _

theorem IsTransducer.outputProbeDecodeTokenDispatchTM_internal
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).IsTransducer := by
  let hclear := outputProbeDecodeTokenClearTagsTM_isTransducer_internal n
    controllerTapes layout
  apply IsTransducer.outputProbeDecodeTagDispatchTM_internal
  · exact hclear.seqTM hvar
  · exact hclear.seqTM htru
  · exact hclear.seqTM hfls
  · exact hclear.seqTM hneg
  · exact hclear.seqTM hconj
  · exact hclear.seqTM hdisj
  · exact hclear.seqTM hinvalid

theorem IsTransducer.outputProbeDecodeTokenTM_internal
    {tm : TM n}
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenTM tm controllerTapes layout onVar onTru onFls
      onNeg onConj onDisj onInvalid).IsTransducer := by
  apply IsTransducer.seqTM
  · exact outputProbeDecodeTagTM_isTransducer_internal tm controllerTapes
      layout.tagLayout
  · exact hvar.outputProbeDecodeTokenDispatchTM_internal htru hfls hneg
      hconj hdisj hinvalid layout

theorem IsTransducer.outputProbeDecodeTokenWithNatTM_internal
    {tm : TM n}
    {onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (htru : onTru.IsTransducer) (hfls : onFls.IsTransducer)
    (hneg : onNeg.IsTransducer) (hconj : onConj.IsTransducer)
    (hdisj : onDisj.IsTransducer) (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenWithNatTM tm controllerTapes layout onTru onFls
      onNeg onConj onDisj onInvalid).IsTransducer := by
  apply IsTransducer.outputProbeDecodeTokenTM_internal
  · exact outputProbeDecodeNatTM_isTransducer_internal tm controllerTapes
      layout.natLayout.cursorIdx layout.natLayout.scratchIdx
      layout.natLayout.valueIdx layout.natLayout.activeIdx
      layout.natLayout.loopIdx layout.natLayout.fuelIdx
  · exact htru
  · exact hfls
  · exact hneg
  · exact hconj
  · exact hdisj
  · exact hinvalid

end TM

end Complexity
