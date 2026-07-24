/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Decoding fixed formula-token tags through output probes -- internals
-/

namespace Complexity

namespace TM

private theorem outputProbeDecodeTagSkipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

private theorem OutputProbeDecodeTagLayout.roles_ne_internal
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    {i j : Fin 5} (hne : i ≠ j) : layout.roles i ≠ layout.roles j := by
  intro heq
  exact hne (layout.roles.injective heq)

theorem outputProbeDecodeTag?_ofList_internal (bits : List Bool)
    (cursor : ℕ) :
    outputProbeDecodeTag? (FormulaCode.BitOracle.ofList bits) cursor = (do
      let tag₀ ← bits[cursor]?
      let tag₁ ← bits[cursor + 1]?
      let tag₂ ← bits[cursor + 2]?
      let tag ← outputProbeTokenTag? tag₀ tag₁ tag₂
      some (tag, cursor + 3)) := by
  rfl

theorem outputProbeDecodeTag?_fixed_token_internal
    (query : FormulaCode.BitOracle) (cursor bitFuel : ℕ)
    (tag : OutputProbeTokenTag) (nextCursor : ℕ)
    (hdecode : outputProbeDecodeTag? query cursor =
      some (tag, nextCursor)) :
    match tag with
    | .var => True
    | .tru => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.tru, nextCursor)
    | .fls => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.fls, nextCursor)
    | .neg => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.neg, nextCursor)
    | .conj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.conj, nextCursor)
    | .disj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.disj, nextCursor) := by
  cases tag <;> simp only
  all_goals
    unfold outputProbeDecodeTag? at hdecode
    generalize htag₀ : query cursor = tag₀ at hdecode ⊢
    cases tag₀ with
    | none => simp at hdecode
    | some tag₀ =>
        generalize htag₁ : query (cursor + 1) = tag₁ at hdecode ⊢
        cases tag₁ with
        | none => simp at hdecode
        | some tag₁ =>
            generalize htag₂ : query (cursor + 2) = tag₂ at hdecode ⊢
            cases tag₂ with
            | none => simp at hdecode
            | some tag₂ =>
                cases tag₀ <;> cases tag₁ <;> cases tag₂ <;>
                  simp_all [outputProbeTokenTag?,
                    FormulaCode.BitOracle.decodeTokenAt?]

private theorem outputProbeDecodeTagCounterTape_parked_internal
    (value : ℕ) : Parked (outputProbeCounterTape value) := by
  have h : (outputProbeCounterTape value).HasBinaryNat value := by
    simpa [outputProbeCounterTape] using
      Tape.init_move_right_hasBinaryNat value
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem outputProbeDecodeTagUpdateOuter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (idx : Fin controllerTapes) (value : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (Function.update outerExtras
        (outputProbeIndexedControllerIdx n idx)
        (outputProbeCounterTape value) i) := by
  intro i hi
  by_cases heq : i = outputProbeIndexedControllerIdx n idx
  · subst i
    rw [Function.update_self]
    exact outputProbeDecodeTagCounterTape_parked_internal value
  · rw [Function.update_of_ne heq]
    exact houter i hi

theorem outputProbeDecodeTagBitOuterExtrasAfter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (bit : Bool) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx
        outerExtras cursor bit i) := by
  have hbitOuter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outputProbeCountOnesOuterExtrasAfter n bitIdx outerExtras 0
          bit i) := by
    by_cases hbit : bit
    · simpa [outputProbeCountOnesOuterExtrasAfter, hbit] using
        outputProbeDecodeTagUpdateOuter_parked_internal n outerExtras houter
          bitIdx 1
    · simpa [outputProbeCountOnesOuterExtrasAfter, hbit] using houter
  simpa [outputProbeDecodeTagBitOuterExtrasAfter,
    outputProbeDecodeTagCursorIdx] using
    outputProbeDecodeTagUpdateOuter_parked_internal n
      (outputProbeCountOnesOuterExtrasAfter n bitIdx outerExtras 0 bit)
      hbitOuter layout.cursorIdx (cursor + 1)

theorem outputProbeDecodeTagBitOuterExtrasAfter_cursor_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (bit : Bool) :
    (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
      cursor bit (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        (cursor + 1) := by
  simp only [outputProbeDecodeTagBitOuterExtrasAfter, Function.update_self]
  exact Tape.init_move_right_hasBinaryNat (cursor + 1)

theorem outputProbeDecodeTagBitOuterExtrasAfter_bit_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (hcursorBit : layout.cursorIdx ≠ bitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (hzero :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0)
    (cursor : ℕ) (bit : Bool) :
    (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
      cursor bit (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat
        (if bit then 1 else 0) := by
  have hphysical : outputProbeDecodeTagBitIdx n bitIdx ≠
      outputProbeDecodeTagCursorIdx n layout := by
    intro heq
    exact hcursorBit (outputProbeIndexedControllerIdx_injective n heq.symm)
  rw [outputProbeDecodeTagBitOuterExtrasAfter,
    Function.update_of_ne hphysical]
  by_cases hbit : bit
  · simp [outputProbeCountOnesOuterExtrasAfter, hbit,
      outputProbeDecodeTagBitIdx]
    exact Tape.init_move_right_hasBinaryNat 1
  · simpa [outputProbeCountOnesOuterExtrasAfter, hbit] using hzero

theorem outputProbeDecodeTagBitOuterExtrasAfter_other_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx idx : Fin controllerTapes)
    (hcursor : idx ≠ layout.cursorIdx) (hbit : idx ≠ bitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (bit : Bool) :
    outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
        cursor bit (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  have hcursorPhysical : outputProbeIndexedControllerIdx n idx ≠
      outputProbeDecodeTagCursorIdx n layout := by
    intro heq
    exact hcursor (outputProbeIndexedControllerIdx_injective n heq)
  have hbitPhysical : outputProbeIndexedControllerIdx n idx ≠
      outputProbeIndexedControllerIdx n bitIdx := by
    intro heq
    exact hbit (outputProbeIndexedControllerIdx_injective n heq)
  rw [outputProbeDecodeTagBitOuterExtrasAfter,
    Function.update_of_ne hcursorPhysical]
  by_cases hbitValue : bit
  · simp [outputProbeCountOnesOuterExtrasAfter, hbitValue, hbitPhysical]
  · simp [outputProbeCountOnesOuterExtrasAfter, hbitValue]

theorem outputProbeDecodeTagOuterExtrasAfter_invariant_internal
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (htag₀ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0) :
    let after := outputProbeDecodeTagOuterExtrasAfter n layout outerExtras
      cursor tag₀ tag₁ tag₂
    (∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (after i)) ∧
    (after (outputProbeDecodeTagBitIdx n layout.tag₀Idx)).HasBinaryNat
      (if tag₀ then 1 else 0) ∧
    (after (outputProbeDecodeTagBitIdx n layout.tag₁Idx)).HasBinaryNat
      (if tag₁ then 1 else 0) ∧
    (after (outputProbeDecodeTagBitIdx n layout.tag₂Idx)).HasBinaryNat
      (if tag₂ then 1 else 0) := by
  have hcursorTag₀ : layout.cursorIdx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have hcursorTag₁ : layout.cursorIdx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  have hcursorTag₂ : layout.cursorIdx ≠ layout.tag₂Idx :=
    layout.roles_ne_internal (by decide)
  have htag₀Tag₁ : layout.tag₀Idx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  have htag₀Tag₂ : layout.tag₀Idx ≠ layout.tag₂Idx :=
    layout.roles_ne_internal (by decide)
  have htag₁Tag₀ : layout.tag₁Idx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have htag₁Tag₂ : layout.tag₁Idx ≠ layout.tag₂Idx :=
    layout.roles_ne_internal (by decide)
  have htag₂Tag₀ : layout.tag₂Idx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have htag₂Tag₁ : layout.tag₂Idx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  let outer₁ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₀Idx outerExtras cursor tag₀
  let outer₂ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₁Idx outer₁ (cursor + 1) tag₁
  let outer₃ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₂Idx outer₂ (cursor + 2) tag₂
  have houter₁ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₁ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₀Idx outerExtras houter cursor tag₀
  have htag₀₁ := outputProbeDecodeTagBitOuterExtrasAfter_bit_internal n
    layout layout.tag₀Idx hcursorTag₀ outerExtras htag₀ cursor tag₀
  have htag₁₁ :
      (outer₁ (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₀Idx
      outerExtras cursor tag₀
      (outputProbeIndexedControllerIdx n layout.tag₁Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₀Idx layout.tag₁Idx (Ne.symm hcursorTag₁) htag₁Tag₀
      outerExtras cursor tag₀]
    exact htag₁
  have htag₂₁ :
      (outer₁ (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₀Idx
      outerExtras cursor tag₀
      (outputProbeIndexedControllerIdx n layout.tag₂Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₀Idx layout.tag₂Idx (Ne.symm hcursorTag₂) htag₂Tag₀
      outerExtras cursor tag₀]
    exact htag₂
  have houter₂ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₂ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₁Idx outer₁ houter₁ (cursor + 1) tag₁
  have htag₀₂ :
      (outer₂ (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0) := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₁Idx
      outer₁ (cursor + 1) tag₁
      (outputProbeIndexedControllerIdx n layout.tag₀Idx)).HasBinaryNat
        (if tag₀ then 1 else 0)
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₁Idx layout.tag₀Idx (Ne.symm hcursorTag₀) htag₀Tag₁
      outer₁ (cursor + 1) tag₁]
    exact htag₀₁
  have htag₁₂ := outputProbeDecodeTagBitOuterExtrasAfter_bit_internal n
    layout layout.tag₁Idx hcursorTag₁ outer₁ htag₁₁ (cursor + 1) tag₁
  have htag₂₂ :
      (outer₂ (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₁Idx
      outer₁ (cursor + 1) tag₁
      (outputProbeIndexedControllerIdx n layout.tag₂Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₁Idx layout.tag₂Idx (Ne.symm hcursorTag₂) htag₂Tag₁
      outer₁ (cursor + 1) tag₁]
    exact htag₂₁
  have houter₃ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₃ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₂Idx outer₂ houter₂ (cursor + 2) tag₂
  have htag₀₃ :
      (outer₃ (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0) := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₂Idx
      outer₂ (cursor + 2) tag₂
      (outputProbeIndexedControllerIdx n layout.tag₀Idx)).HasBinaryNat
        (if tag₀ then 1 else 0)
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₂Idx layout.tag₀Idx (Ne.symm hcursorTag₀) htag₀Tag₂
      outer₂ (cursor + 2) tag₂]
    exact htag₀₂
  have htag₁₃ :
      (outer₃ (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0) := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₂Idx
      outer₂ (cursor + 2) tag₂
      (outputProbeIndexedControllerIdx n layout.tag₁Idx)).HasBinaryNat
        (if tag₁ then 1 else 0)
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₂Idx layout.tag₁Idx (Ne.symm hcursorTag₁) htag₁Tag₂
      outer₂ (cursor + 2) tag₂]
    exact htag₁₂
  have htag₂₃ := outputProbeDecodeTagBitOuterExtrasAfter_bit_internal n
    layout layout.tag₂Idx hcursorTag₂ outer₂ htag₂₂ (cursor + 2) tag₂
  simpa [outputProbeDecodeTagOuterExtrasAfter, outer₁, outer₂, outer₃]
    using And.intro houter₃
      (And.intro htag₀₃ (And.intro htag₁₃ htag₂₃))

private theorem outputProbeDecodeTagSucc_hoareTime_internal
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
    (binarySuccTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape (value + 1)))
        input output extras false)
      (binarySuccTime value) := by
  let physical := outputProbeIndexedControllerIdx n idx
  let nextTape := outputProbeCounterTape (value + 1)
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htarget : (work physical).HasBinaryNat value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hvalue
  obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, htargetDone,
      houtputDone⟩ :=
    binarySuccTM_reachesIn_frame physical value inp work out htarget
      hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkDone : done.work = Function.update work physical nextTape := by
    funext i
    by_cases hi : i = physical
    · subst i
      rw [Function.update_self]
      exact htargetDone.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hotherDone i hi
  refine ⟨done, binarySuccTime value, le_rfl, hreach, hhalt, ?_⟩
  rw [hinputDone, hworkDone, houtputDone]
  simpa [physical, nextTape] using
    outputProbeLatchFramePost_updateController tm controllerTapes outerExtras
      input output extras false inp work out hpost idx nextTape

theorem ComputesInSpace.outputProbeDecodeTagBitTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (hcursorScratch : layout.cursorIdx ≠ layout.scratchIdx)
    (hcursorBit : layout.cursorIdx ≠ bitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (hbit :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeTagBitTM tm controllerTapes layout bitIdx).HoareTime
        pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
            cursor ((f input)[cursor]'hcursorBound))
          input output extras false)
        (bodyBound + 1 + binarySuccTime cursor) := by
  let bit := (f input)[cursor]'hcursorBound
  let afterBit := outputProbeCountOnesOuterExtrasAfter n bitIdx outerExtras 0
    bit
  obtain ⟨bodyBound, pre, hpre, hbody⟩ :=
    hcomp.outputProbeCountOnesBodyTM_hoareTime input cursor hcursorBound output
      houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit hlimit
      controllerTapes outerExtras houter layout.cursorIdx layout.scratchIdx
      bitIdx hcursorScratch hcursor hscratch 0 hbit
  have hafterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (afterBit i) := by
    by_cases hbitValue : bit
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        outputProbeDecodeTagUpdateOuter_parked_internal n outerExtras houter
          bitIdx 1
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        houter
  have hcursorAfter :
      (afterBit (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor := by
    have hphysical : outputProbeDecodeTagCursorIdx n layout ≠
        outputProbeIndexedControllerIdx n bitIdx := by
      intro heq
      exact hcursorBit (outputProbeIndexedControllerIdx_injective n heq)
    by_cases hbitValue : bit
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue,
        hphysical] using hcursor
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        hcursor
  have hsucc := outputProbeDecodeTagSucc_hoareTime_internal tm
    controllerTapes afterBit input output extras hextras hafterParked houtput
    layout.cursorIdx cursor hcursorAfter
  have htransition : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes afterBit input output
          extras false inp work out →
        outputProbeLatchFramePost tm controllerTapes afterBit input output
          extras false (transitionInput inp)
          (fun i => transitionTape (work i)) (transitionTape out) := by
    intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes afterBit input output extras false hextras hafterParked
      houtput inp work out hpost
    rw [hinp.transitionInput_eq_self]
    have hworkTransition : (fun i => transitionTape (work i)) = work := by
      funext i
      exact (hwork i).transitionTape_eq_self
    rw [hworkTransition, hout.transitionTape_eq_self]
    exact hpost
  refine ⟨bodyBound, pre, hpre, ?_⟩
  simpa [outputProbeDecodeTagBitTM,
    outputProbeDecodeTagBitOuterExtrasAfter, afterBit, bit,
    outputProbeDecodeTagCursorIdx] using
    seqTM_hoareTime
      (outputProbeCountOnesBodyTM tm controllerTapes layout.cursorIdx
        layout.scratchIdx bitIdx)
      (binarySuccTM (outputProbeDecodeTagCursorIdx n layout))
      hbody htransition hsucc

private theorem outputProbeDecodeTagFramePost_to_pre_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes))
    (hpre : pre
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).input
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).output) :
    ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        pre (transitionInput inp) (fun i => transitionTape (work i))
          (transitionTape out) := by
  intro inp work out hpost
  obtain ⟨hinputEq, hworkEq, houtputEq⟩ :=
    outputProbeLatchFramePost_eq_frameCfg tm controllerTapes outerExtras input
      output extras false inp work out hpost
  obtain ⟨hinputParked, hworkParked, houtputParked⟩ :=
    outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
      output extras false hextras houter houtput inp work out hpost
  rw [hinputParked.transitionInput_eq_self]
  have hworkTransition : (fun i => transitionTape (work i)) = work := by
    funext i
    exact (hworkParked i).transitionTape_eq_self
  rw [hworkTransition, houtputParked.transitionTape_eq_self, hinputEq,
    hworkEq, houtputEq]
  exact hpre

theorem ComputesInSpace.outputProbeDecodeTagTM_hoareTime_internal
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
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (htag₀ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0) :
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
      (outputProbeDecodeTagTM tm controllerTapes layout).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
            ((f input)[cursor]) ((f input)[cursor + 1])
            ((f input)[cursor + 2]))
          input output extras false)
        ((bound₀ + 1 + binarySuccTime cursor) + 1 +
          ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
            (bound₂ + 1 + binarySuccTime (cursor + 2)))) := by
  have hbound₀ : cursor < (f input).length := by omega
  have hbound₁ : cursor + 1 < (f input).length := by omega
  have hbound₂ : cursor + 2 < (f input).length := hcursorBound
  have hcursorScratch : layout.cursorIdx ≠ layout.scratchIdx :=
    layout.roles_ne_internal (by decide)
  have hcursorTag₀ : layout.cursorIdx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have hcursorTag₁ : layout.cursorIdx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  have hcursorTag₂ : layout.cursorIdx ≠ layout.tag₂Idx :=
    layout.roles_ne_internal (by decide)
  have hscratchTag₀ : layout.scratchIdx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have hscratchTag₁ : layout.scratchIdx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  have hscratchTag₂ : layout.scratchIdx ≠ layout.tag₂Idx :=
    layout.roles_ne_internal (by decide)
  have htag₁Tag₀ : layout.tag₁Idx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have htag₂Tag₀ : layout.tag₂Idx ≠ layout.tag₀Idx :=
    layout.roles_ne_internal (by decide)
  have htag₂Tag₁ : layout.tag₂Idx ≠ layout.tag₁Idx :=
    layout.roles_ne_internal (by decide)
  let bit₀ := (f input)[cursor]'hbound₀
  let bit₁ := (f input)[cursor + 1]'hbound₁
  let bit₂ := (f input)[cursor + 2]'hbound₂
  let outer₁ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₀Idx outerExtras cursor bit₀
  let outer₂ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₁Idx outer₁ (cursor + 1) bit₁
  let outer₃ := outputProbeDecodeTagBitOuterExtrasAfter n layout
    layout.tag₂Idx outer₂ (cursor + 2) bit₂
  have houter₁ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₁ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₀Idx outerExtras houter cursor bit₀
  have hcursor₁ :
      (outer₁ (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        (cursor + 1) :=
    outputProbeDecodeTagBitOuterExtrasAfter_cursor_internal n layout
      layout.tag₀Idx outerExtras cursor bit₀
  have hscratch₁ :
      (outer₁ (outputProbeIndexedControllerIdx n layout.scratchIdx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₀Idx
      outerExtras cursor bit₀
      (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₀Idx layout.scratchIdx (Ne.symm hcursorScratch)
      hscratchTag₀ outerExtras cursor bit₀]
    exact hscratch
  have htag₁₁ :
      (outer₁ (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₀Idx
      outerExtras cursor bit₀
      (outputProbeIndexedControllerIdx n layout.tag₁Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₀Idx layout.tag₁Idx (Ne.symm hcursorTag₁) htag₁Tag₀
      outerExtras cursor bit₀]
    exact htag₁
  have htag₂₁ :
      (outer₁ (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₀Idx
      outerExtras cursor bit₀
      (outputProbeIndexedControllerIdx n layout.tag₂Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₀Idx layout.tag₂Idx (Ne.symm hcursorTag₂) htag₂Tag₀
      outerExtras cursor bit₀]
    exact htag₂
  have houter₂ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₂ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₁Idx outer₁ houter₁ (cursor + 1) bit₁
  have hcursor₂ :
      (outer₂ (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        (cursor + 2) := by
    simpa [Nat.add_assoc] using
      outputProbeDecodeTagBitOuterExtrasAfter_cursor_internal n layout
        layout.tag₁Idx outer₁ (cursor + 1) bit₁
  have hscratch₂ :
      (outer₂ (outputProbeIndexedControllerIdx n layout.scratchIdx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₁Idx
      outer₁ (cursor + 1) bit₁
      (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₁Idx layout.scratchIdx (Ne.symm hcursorScratch)
      hscratchTag₁ outer₁ (cursor + 1) bit₁]
    exact hscratch₁
  have htag₂₂ :
      (outer₂ (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0 := by
    change (outputProbeDecodeTagBitOuterExtrasAfter n layout layout.tag₁Idx
      outer₁ (cursor + 1) bit₁
      (outputProbeIndexedControllerIdx n layout.tag₂Idx)).HasBinaryNat 0
    rw [outputProbeDecodeTagBitOuterExtrasAfter_other_internal n layout
      layout.tag₁Idx layout.tag₂Idx (Ne.symm hcursorTag₂) htag₂Tag₁ outer₁
      (cursor + 1) bit₁]
    exact htag₂₁
  have houter₃ : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outer₃ i) :=
    outputProbeDecodeTagBitOuterExtrasAfter_parked_internal n layout
      layout.tag₂Idx outer₂ houter₂ (cursor + 2) bit₂
  obtain ⟨bound₀, pre₀, hpre₀, hstep₀⟩ :=
    hcomp.outputProbeDecodeTagBitTM_hoareTime_internal input cursor hbound₀
      output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ controllerTapes layout layout.tag₀Idx
      hcursorScratch hcursorTag₀ outerExtras houter hcursor hscratch htag₀
  obtain ⟨bound₁, pre₁, hpre₁, hstep₁⟩ :=
    hcomp.outputProbeDecodeTagBitTM_hoareTime_internal input (cursor + 1)
      hbound₁ output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₁ controllerTapes layout layout.tag₁Idx
      hcursorScratch hcursorTag₁ outer₁ houter₁ hcursor₁ hscratch₁ htag₁₁
  obtain ⟨bound₂, pre₂, hpre₂, hstep₂⟩ :=
    hcomp.outputProbeDecodeTagBitTM_hoareTime_internal input (cursor + 2)
      hbound₂ output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₂ controllerTapes layout layout.tag₂Idx
      hcursorScratch hcursorTag₂ outer₂ houter₂ hcursor₂ hscratch₂ htag₂₂
  have hstep₀' :
      (outputProbeDecodeTagBitTM tm controllerTapes layout
        layout.tag₀Idx).HoareTime pre₀
        (outputProbeLatchFramePost tm controllerTapes outer₁ input output
          extras false)
        (bound₀ + 1 + binarySuccTime cursor) := by
    simpa [outer₁, bit₀] using hstep₀
  have hstep₁' :
      (outputProbeDecodeTagBitTM tm controllerTapes layout
        layout.tag₁Idx).HoareTime pre₁
        (outputProbeLatchFramePost tm controllerTapes outer₂ input output
          extras false)
        (bound₁ + 1 + binarySuccTime (cursor + 1)) := by
    simpa [outer₂, bit₁] using hstep₁
  have hstep₂' :
      (outputProbeDecodeTagBitTM tm controllerTapes layout
        layout.tag₂Idx).HoareTime pre₂
        (outputProbeLatchFramePost tm controllerTapes outer₃ input output
          extras false)
        (bound₂ + 1 + binarySuccTime (cursor + 2)) := by
    simpa [outer₃, bit₂] using hstep₂
  have hseam₁ := outputProbeDecodeTagFramePost_to_pre_internal tm
    controllerTapes outer₁ input output extras hextras houter₁ houtput pre₁
    hpre₁
  have hseam₂ := outputProbeDecodeTagFramePost_to_pre_internal tm
    controllerTapes outer₂ input output extras hextras houter₂ houtput pre₂
    hpre₂
  have hstep₁₂ := seqTM_hoareTime
    (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₁Idx)
    (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₂Idx)
    hstep₁' hseam₂ hstep₂'
  have hfull := seqTM_hoareTime
    (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₀Idx)
    (seqTM
      (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₁Idx)
      (outputProbeDecodeTagBitTM tm controllerTapes layout layout.tag₂Idx))
    hstep₀' hseam₁ hstep₁₂
  refine ⟨bound₀, bound₁, bound₂, pre₀, hpre₀, ?_⟩
  simpa [outputProbeDecodeTagTM, outputProbeDecodeTagOuterExtrasAfter,
    outer₁, outer₂, outer₃, bit₀, bit₁, bit₂] using hfull

private theorem outputProbeDecodeTagBitDispatchTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (bitIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hbit :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat
        (if bit then 1 else 0))
    (onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Bool →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {zeroTime oneTime : ℕ}
    (hzero : onZero.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post false) zeroTime)
    (hone : onOne.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post true) oneTime) :
    (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne
      onZero).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (post bit) ((if bit then oneTime else zeroTime) + 1) := by
  cases bit with
  | false =>
      have hzeroBit :
          (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0 :=
        by simpa using hbit
      have hzeroController :
          (outerExtras (outputProbeIndexedControllerIdx n bitIdx))
            |>.HasBinaryNat 0 := by
        simpa [outputProbeDecodeTagBitIdx] using hzeroBit
      have hbranch := branchWorkSymbolTM_hoareTime_different
        (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne onZero
        (fun inp work out hpost => by
          change (work (outputProbeIndexedControllerIdx n bitIdx)).read ≠
            Γ.one
          have hcontroller := outputProbeLatchFramePost_controller tm
            controllerTapes outerExtras input output extras false inp work out
            hpost bitIdx
          rw [hcontroller, hzeroController.eq_init_move_right]
          decide)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.2.read_ne_start)
        hzero
      simpa using hbranch
  | true =>
      have honeBit :
          (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 1 :=
        by simpa using hbit
      have honeController :
          (outerExtras (outputProbeIndexedControllerIdx n bitIdx))
            |>.HasBinaryNat 1 := by
        simpa [outputProbeDecodeTagBitIdx] using honeBit
      have hbranch := branchWorkSymbolTM_hoareTime_equal
        (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne onZero
        (fun inp work out hpost => by
          change (work (outputProbeIndexedControllerIdx n bitIdx)).read =
            Γ.one
          have hcontroller := outputProbeLatchFramePost_controller tm
            controllerTapes outerExtras input output extras false inp work out
            hpost bitIdx
          rw [hcontroller, honeController.eq_init_move_right]
          rfl)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.2.read_ne_start)
        hone
      simpa using hbranch

private theorem outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (bitIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hbit :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat
        (if bit then 1 else 0))
    (onZero onOne :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {selectedTime : ℕ}
    (hselected : (if bit then onOne else onZero).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      post selectedTime) :
    (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne
      onZero).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        post (selectedTime + 1) := by
  cases bit with
  | false =>
      have hzeroBit :
          (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0 :=
        by simpa using hbit
      have hzeroController :
          (outerExtras (outputProbeIndexedControllerIdx n bitIdx))
            |>.HasBinaryNat 0 := by
        simpa [outputProbeDecodeTagBitIdx] using hzeroBit
      have hbranch := branchWorkSymbolTM_hoareTime_different
        (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne onZero
        (fun inp work out hpost => by
          change (work (outputProbeIndexedControllerIdx n bitIdx)).read ≠
            Γ.one
          have hcontroller := outputProbeLatchFramePost_controller tm
            controllerTapes outerExtras input output extras false inp work out
            hpost bitIdx
          rw [hcontroller, hzeroController.eq_init_move_right]
          decide)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.2.read_ne_start)
        hselected
      simpa using hbranch
  | true =>
      have honeBit :
          (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 1 :=
        by simpa using hbit
      have honeController :
          (outerExtras (outputProbeIndexedControllerIdx n bitIdx))
            |>.HasBinaryNat 1 := by
        simpa [outputProbeDecodeTagBitIdx] using honeBit
      have hbranch := branchWorkSymbolTM_hoareTime_equal
        (outputProbeDecodeTagBitIdx n bitIdx) Γ.one onOne onZero
        (fun inp work out hpost => by
          change (work (outputProbeIndexedControllerIdx n bitIdx)).read =
            Γ.one
          have hcontroller := outputProbeLatchFramePost_controller tm
            controllerTapes outerExtras input output extras false inp work out
            hpost bitIdx
          rw [hcontroller, honeController.eq_init_move_right]
          rfl)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked tm controllerTapes outerExtras
            input output extras false hextras houter houtput inp work out
            hpost).2.2.read_ne_start)
        hselected
      simpa using hbranch

theorem outputProbeDecodeTagDispatchTM_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
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
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0))
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Option OutputProbeTokenTag →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {varTime truTime flsTime negTime conjTime disjTime invalidTime : ℕ}
    (hvar : onVar.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .var)) varTime)
    (htru : onTru.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .tru)) truTime)
    (hfls : onFls.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .fls)) flsTime)
    (hneg : onNeg.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .neg)) negTime)
    (hconj : onConj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .conj)) conjTime)
    (hdisj : onDisj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post (some .disj)) disjTime)
    (hinvalid : onInvalid.HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post none) invalidTime) :
    (outputProbeDecodeTagDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (post (outputProbeTokenTag? tag₀ tag₁ tag₂))
        (outputProbeDecodeTagDispatchTime tag₀ tag₁ tag₂ varTime
          truTime flsTime negTime conjTime disjTime invalidTime) := by
  let tag₂Physical := outputProbeDecodeTagBitIdx n layout.tag₂Idx
  let tag₀ZeroTM := branchWorkSymbolTM tag₂Physical Γ.one onTru onVar
  let tag₀OneTM := branchWorkSymbolTM tag₂Physical Γ.one onNeg onFls
  let tag₁ZeroTM := branchWorkSymbolTM tag₂Physical Γ.one onDisj onConj
  have htag₀Zero := outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm
    controllerTapes layout.tag₂Idx outerExtras input output extras tag₂ hextras
    houter houtput htag₂ onVar onTru
    (post := fun bit => post (if bit then some .tru else some .var))
    hvar htru
  have htag₀One := outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm
    controllerTapes layout.tag₂Idx outerExtras input output extras tag₂ hextras
    houter houtput htag₂ onFls onNeg
    (post := fun bit => post (if bit then some .neg else some .fls))
    hfls hneg
  have htag₁Zero := outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm
    controllerTapes layout.tag₂Idx outerExtras input output extras tag₂ hextras
    houter houtput htag₂ onConj onDisj
    (post := fun bit => post (if bit then some .disj else some .conj))
    hconj hdisj
  have htag₀Branch :=
    outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm controllerTapes
      layout.tag₁Idx outerExtras input output extras tag₁ hextras houter
      houtput htag₁ tag₀ZeroTM tag₀OneTM
      (post := fun bit => post (if bit then
        if tag₂ then some .neg else some .fls
      else if tag₂ then some .tru else some .var))
      htag₀Zero htag₀One
  have htag₁Branch :=
    outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm controllerTapes
      layout.tag₁Idx outerExtras input output extras tag₁ hextras houter
      houtput htag₁ tag₁ZeroTM onInvalid
      (post := fun bit => post (if bit then none
        else if tag₂ then some .disj else some .conj))
      htag₁Zero hinvalid
  have hroot := outputProbeDecodeTagBitDispatchTM_hoareTime_internal tm
    controllerTapes layout.tag₀Idx outerExtras input output extras tag₀ hextras
    houter houtput htag₀
    (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx) Γ.one
      tag₀OneTM tag₀ZeroTM)
    (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx) Γ.one
      onInvalid tag₁ZeroTM)
    (post := fun bit => post (if bit then
      if tag₁ then none
      else if tag₂ then some .disj else some .conj
    else if tag₁ then
      if tag₂ then some .neg else some .fls
    else if tag₂ then some .tru else some .var))
    htag₀Branch htag₁Branch
  cases tag₀ <;> cases tag₁ <;> cases tag₂ <;>
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchTime, outputProbeTokenTag?, tag₂Physical,
      tag₀ZeroTM, tag₀OneTM, tag₁ZeroTM, Nat.add_assoc] using hroot

theorem outputProbeDecodeTagDispatchTM_selected_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
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
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat (if tag₀ then 1 else 0))
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat (if tag₁ then 1 else 0))
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat (if tag₂ then 1 else 0))
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {selectedTime : ℕ}
    (hselected :
      (outputProbeTokenContinuation
        (outputProbeTokenTag? tag₀ tag₁ tag₂)
        onVar onTru onFls onNeg onConj onDisj onInvalid).HoareTime
          (outputProbeLatchFramePost tm controllerTapes outerExtras input output
            extras false)
          post selectedTime) :
    (outputProbeDecodeTagDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        post (selectedTime + outputProbeDecodeTagDispatchDepth tag₀ tag₁) := by
  let tag₂Physical := outputProbeDecodeTagBitIdx n layout.tag₂Idx
  let tag₀ZeroTM := branchWorkSymbolTM tag₂Physical Γ.one onTru onVar
  let tag₀OneTM := branchWorkSymbolTM tag₂Physical Γ.one onNeg onFls
  let tag₁ZeroTM := branchWorkSymbolTM tag₂Physical Γ.one onDisj onConj
  cases tag₀ <;> cases tag₁ <;> cases tag₂
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras false
      hextras houter houtput htag₂ onVar onTru hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras false
      hextras houter houtput htag₁ tag₀ZeroTM tag₀OneTM h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras false
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras true
      hextras houter houtput htag₂ onVar onTru hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras false
      hextras houter houtput htag₁ tag₀ZeroTM tag₀OneTM h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras false
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras false
      hextras houter houtput htag₂ onFls onNeg hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras true
      hextras houter houtput htag₁ tag₀ZeroTM tag₀OneTM h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras false
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras true
      hextras houter houtput htag₂ onFls onNeg hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras true
      hextras houter houtput htag₁ tag₀ZeroTM tag₀OneTM h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras false
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras false
      hextras houter houtput htag₂ onConj onDisj hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras false
      hextras houter houtput htag₁ tag₁ZeroTM onInvalid h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras true
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₂ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₂Idx outerExtras input output extras true
      hextras houter houtput htag₂ onConj onDisj hselected
    have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras false
      hextras houter houtput htag₁ tag₁ZeroTM onInvalid h₂
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras true
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras true
      hextras houter houtput htag₁ tag₁ZeroTM onInvalid hselected
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras true
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀
  · have h₁ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₁Idx outerExtras input output extras true
      hextras houter houtput htag₁ tag₁ZeroTM onInvalid hselected
    have h₀ := outputProbeDecodeTagBitDispatchTM_selected_hoareTime_internal
      tm controllerTapes layout.tag₀Idx outerExtras input output extras true
      hextras houter houtput htag₀
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one tag₀OneTM tag₀ZeroTM)
      (branchWorkSymbolTM (outputProbeDecodeTagBitIdx n layout.tag₁Idx)
        Γ.one onInvalid tag₁ZeroTM)
      h₁
    simpa [outputProbeDecodeTagDispatchTM,
      outputProbeDecodeTagDispatchDepth, tag₀ZeroTM, tag₀OneTM,
      tag₁ZeroTM, Nat.add_assoc] using h₀

theorem ComputesInSpace.outputProbeDecodeTagAndDispatchTM_hoareTime_internal
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
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (htag₀ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂ :
      (outerExtras (outputProbeDecodeTagBitIdx n layout.tag₂Idx))
        |>.HasBinaryNat 0)
    (onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Option OutputProbeTokenTag →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {varTime truTime flsTime negTime conjTime disjTime invalidTime : ℕ}
    (hvar : onVar.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .var)) varTime)
    (htru : onTru.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .tru)) truTime)
    (hfls : onFls.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .fls)) flsTime)
    (hneg : onNeg.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .neg)) negTime)
    (hconj : onConj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .conj)) conjTime)
    (hdisj : onDisj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .disj)) disjTime)
    (hinvalid : onInvalid.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTagOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
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
      (outputProbeDecodeTagAndDispatchTM tm controllerTapes layout onVar
        onTru onFls onNeg onConj onDisj onInvalid).HoareTime pre
          (post (outputProbeTokenTag? ((f input)[cursor])
            ((f input)[cursor + 1]) ((f input)[cursor + 2])))
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTagDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) varTime
              truTime flsTime negTime conjTime disjTime invalidTime) := by
  have hbound₀ : cursor < (f input).length := by omega
  have hbound₁ : cursor + 1 < (f input).length := by omega
  have hbound₂ : cursor + 2 < (f input).length := hcursorBound
  let bit₀ := (f input)[cursor]'hbound₀
  let bit₁ := (f input)[cursor + 1]'hbound₁
  let bit₂ := (f input)[cursor + 2]'hbound₂
  let after := outputProbeDecodeTagOuterExtrasAfter n layout outerExtras
    cursor bit₀ bit₁ bit₂
  obtain ⟨hafter, hafterTag₀, hafterTag₁, hafterTag₂⟩ :=
    outputProbeDecodeTagOuterExtrasAfter_invariant_internal n layout
      outerExtras houter cursor bit₀ bit₁ bit₂ htag₀ htag₁ htag₂
  obtain ⟨bound₀, bound₁, bound₂, pre, hpre, hdecode⟩ :=
    hcomp.outputProbeDecodeTagTM_hoareTime_internal input cursor hcursorBound
      output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras
      houter hcursor hscratch htag₀ htag₁ htag₂
  have hdispatch := outputProbeDecodeTagDispatchTM_hoareTime_internal tm
    controllerTapes layout after input output extras bit₀ bit₁ bit₂ hextras
    hafter houtput hafterTag₀ hafterTag₁ hafterTag₂ onVar onTru onFls onNeg
    onConj onDisj onInvalid (post := post) (by simpa [after, bit₀, bit₁, bit₂]
      using hvar) (by simpa [after, bit₀, bit₁, bit₂] using htru)
      (by simpa [after, bit₀, bit₁, bit₂] using hfls)
      (by simpa [after, bit₀, bit₁, bit₂] using hneg)
      (by simpa [after, bit₀, bit₁, bit₂] using hconj)
      (by simpa [after, bit₀, bit₁, bit₂] using hdisj)
      (by simpa [after, bit₀, bit₁, bit₂] using hinvalid)
  have hframePre := outputProbeLatchFrameCfg_post tm controllerTapes after
    input output extras false
  have hseam := outputProbeDecodeTagFramePost_to_pre_internal tm
    controllerTapes after input output extras hextras hafter houtput
    (outputProbeLatchFramePost tm controllerTapes after input output extras
      false)
    hframePre
  have hfull := seqTM_hoareTime
    (outputProbeDecodeTagTM tm controllerTapes layout)
    (outputProbeDecodeTagDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid)
    (by simpa [after, bit₀, bit₁, bit₂] using hdecode) hseam hdispatch
  refine ⟨bound₀, bound₁, bound₂, pre, hpre, ?_⟩
  simpa [outputProbeDecodeTagAndDispatchTM, after, bit₀, bit₁, bit₂]
    using hfull

theorem outputProbeDecodeTagBitTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes) :
    (outputProbeDecodeTagBitTM tm controllerTapes layout
      bitIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · apply IsTransducer.outputProbeIndexedResetDispatchTM
    · exact outputProbeDecodeTagSkipTM_isTransducer_internal
    · exact binarySuccTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeTagTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    (outputProbeDecodeTagTM tm controllerTapes layout).IsTransducer := by
  apply IsTransducer.seqTM
  · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
      layout layout.tag₀Idx
  · apply IsTransducer.seqTM
    · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
        layout layout.tag₁Idx
    · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
        layout layout.tag₂Idx

theorem IsTransducer.outputProbeDecodeTagDispatchTM_internal
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    (outputProbeDecodeTagDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).IsTransducer := by
  apply IsTransducer.branchWorkSymbolTM
  · apply IsTransducer.branchWorkSymbolTM
    · exact hinvalid
    · exact hdisj.branchWorkSymbolTM hconj
  · apply IsTransducer.branchWorkSymbolTM
    · exact hneg.branchWorkSymbolTM hfls
    · exact htru.branchWorkSymbolTM hvar

theorem IsTransducer.outputProbeDecodeTagAndDispatchTM_internal
    {tm : TM n}
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    (outputProbeDecodeTagAndDispatchTM tm controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).IsTransducer := by
  apply IsTransducer.seqTM
  · exact outputProbeDecodeTagTM_isTransducer_internal tm controllerTapes
      layout
  · exact hvar.outputProbeDecodeTagDispatchTM_internal htru hfls hneg hconj
      hdisj hinvalid layout

end TM

end Complexity
