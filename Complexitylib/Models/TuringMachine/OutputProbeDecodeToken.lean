/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Internal

/-!
# Shared formula-token decoder layout

This module exposes the structural bridge between fixed-width tag probing and
terminated-unary variable decoding. Both controllers use the same cursor and
query scratch, while every retained tag and unary-loop register stays distinct.
-/

namespace Complexity

namespace TM

/-- Fixed-tag and terminated-unary decoding share one source cursor. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_cursorIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.cursorIdx = layout.natLayout.cursorIdx :=
  layout.tagLayout_cursorIdx_internal

/-- Fixed-tag and terminated-unary decoding share one query scratch register. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_scratchIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.scratchIdx = layout.natLayout.scratchIdx :=
  layout.tagLayout_scratchIdx_internal

/-- The first retained tag bit occupies complete-layout role two. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₀Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₀Idx = layout.roles 2 :=
  layout.tagLayout_tag₀Idx_internal

/-- The second retained tag bit occupies complete-layout role three. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₁Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₁Idx = layout.roles 3 :=
  layout.tagLayout_tag₁Idx_internal

/-- The third retained tag bit occupies complete-layout role four. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.tagLayout_tag₂Idx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.tagLayout.tag₂Idx = layout.roles 4 :=
  layout.tagLayout_tag₂Idx_internal

/-- The unary accumulator occupies complete-layout role five. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_valueIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.valueIdx = layout.roles 5 :=
  layout.natLayout_valueIdx_internal

/-- The unary active flag occupies complete-layout role six. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_activeIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.activeIdx = layout.roles 6 :=
  layout.natLayout_activeIdx_internal

/-- The unary loop counter occupies complete-layout role seven. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_loopIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.loopIdx = layout.roles 7 :=
  layout.natLayout_loopIdx_internal

/-- The preserved unary fuel occupies complete-layout role eight. -/
@[simp]
theorem OutputProbeDecodeTokenLayout.natLayout_fuelIdx
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    layout.natLayout.fuelIdx = layout.roles 8 :=
  layout.natLayout_fuelIdx_internal

/-- Complete tag probing and cleanup leave every unrelated controller register
literally unchanged. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_other
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
      outerExtras (outputProbeIndexedControllerIdx n idx) :=
  outputProbeDecodeTokenOuterExtrasAfter_other_internal n layout outerExtras
    cursor tag₀ tag₁ tag₂ idx hcursor htag₀ htag₁ htag₂

/-- Complete tag probing and cleanup advance the shared cursor by exactly
three positions. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_cursor
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool) :
    (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor tag₀
      tag₁ tag₂ (outputProbeDecodeTagCursorIdx n layout.tagLayout))
        |>.HasBinaryNat (cursor + 3) :=
  outputProbeDecodeTokenOuterExtrasAfter_cursor_internal n layout outerExtras
    cursor tag₀ tag₁ tag₂

/-- Complete tag probing and cleanup preserve the parked outer-frame
invariant. -/
theorem outputProbeDecodeTokenOuterExtrasAfter_parked
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
        cursor tag₀ tag₁ tag₂ i) :=
  outputProbeDecodeTokenOuterExtrasAfter_parked_internal n layout outerExtras
    houter cursor tag₀ tag₁ tag₂ htag₀Zero htag₁Zero htag₂Zero

/-- Clearing retained tags preserves every other physical controller tape. -/
theorem outputProbeDecodeTokenClearedTagExtras_eq_of_ne
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
      outerExtras idx :=
  outputProbeDecodeTokenClearedTagExtras_eq_of_ne_internal n layout
    outerExtras idx htag₀ htag₁ htag₂

/-- Clearing retained tags restores the first tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₀
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₀_internal n layout outerExtras

/-- Clearing retained tags restores the second tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₁
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₁_internal n layout outerExtras

/-- Clearing retained tags restores the third tag register to canonical zero. -/
theorem outputProbeDecodeTokenClearedTagExtras_tag₂
    (n : ℕ) {controllerTapes : ℕ}
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeDecodeTokenClearedTagExtras n layout outerExtras
      (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx)).HasBinaryNat
        0 :=
  outputProbeDecodeTokenClearedTagExtras_tag₂_internal n layout outerExtras

/-- Clear all three retained tag registers from a literal restored probe
frame, preserving every other tape and exposing the exact cleanup time. -/
theorem outputProbeDecodeTokenClearTagsTM_hoareTime
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
      (outputProbeDecodeTokenClearTagsTime tag₀ tag₁ tag₂) :=
  outputProbeDecodeTokenClearTagsTM_hoareTime_internal tm controllerTapes
    layout outerExtras input output extras tag₀ tag₁ tag₂ hextras houter
    houtput htag₀ htag₁ htag₂

/-- Dispatch a retained tag after restoring the same canonical zero-tag frame
for every legal and invalid continuation. -/
theorem outputProbeDecodeTokenDispatchTM_hoareTime
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
          truTime flsTime negTime conjTime disjTime invalidTime) :=
  outputProbeDecodeTokenDispatchTM_hoareTime_internal tm controllerTapes
    layout outerExtras input output extras tag₀ tag₁ tag₂ hextras houter
    houtput htag₀ htag₁ htag₂ onVar onTru onFls onNeg onConj onDisj
    onInvalid hvar htru hfls hneg hconj hdisj hinvalid

/-- Dispatch and normalize a retained tag while requiring a contract only for
the selected continuation. -/
theorem outputProbeDecodeTokenDispatchTM_selected_hoareTime
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
          selectedTime) :=
  outputProbeDecodeTokenDispatchTM_selected_hoareTime_internal tm
    controllerTapes layout outerExtras input output extras tag₀ tag₁ tag₂
    hextras houter houtput htag₀ htag₁ htag₂ onVar onTru onFls onNeg
    onConj onDisj onInvalid hselected

/-- Probe a complete source tag, restore the canonical zero-tag invariant, and
run the selected continuation in one exact source-derived machine contract. -/
theorem ComputesInSpace.outputProbeDecodeTokenTM_hoareTime
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
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .var)) varTime)
    (htru : onTru.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .tru)) truTime)
    (hfls : onFls.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .fls)) flsTime)
    (hneg : onNeg.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .neg)) negTime)
    (hconj : onConj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .conj)) conjTime)
    (hdisj : onDisj.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
          ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        input output extras false)
      (post (some .disj)) disjTime)
    (hinvalid : onInvalid.HoareTime
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
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
      (outputProbeDecodeTokenTM tm controllerTapes layout onVar onTru onFls
        onNeg onConj onDisj onInvalid).HoareTime pre
          (post (outputProbeTokenTag? ((f input)[cursor])
            ((f input)[cursor + 1]) ((f input)[cursor + 2])))
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) varTime
              truTime flsTime negTime conjTime disjTime invalidTime) :=
  hcomp.outputProbeDecodeTokenTM_hoareTime_internal input cursor hcursorBound
    output houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras houter
    hcursor hscratch htag₀ htag₁ htag₂ onVar onTru onFls onNeg onConj
    onDisj onInvalid hvar htru hfls hneg hconj hdisj hinvalid

/-- Probe, normalize, and dispatch a complete token using only the contract of
the continuation selected by the source tag. -/
theorem ComputesInSpace.outputProbeDecodeTokenTM_selected_hoareTime
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
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) selectedTime) :=
  hcomp.outputProbeDecodeTokenTM_selected_hoareTime_internal input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras
    houter hcursor hscratch htag₀ htag₁ htag₂ onVar onTru onFls onNeg
    onConj onDisj onInvalid hselected

/-- The concrete variable continuation starts from the normalized post-tag
frame, decodes the following terminated-unary field, and ends in the exact
fuel-bounded semantic decoder frame. -/
theorem ComputesInSpace.outputProbeDecodeTokenVar_hoareTime
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
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).cursor <
          (f input).length)
    (hqueryLimit : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input)
          (outputProbeDecodeTokenVarInitial cursor) value).cursor + 1) ≤
            cleanupLimit) :
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
              (outputProbeDecodeTokenVarInitial cursor) fuelValue)
            fuelValue)
          input output extras false)
        (binaryForLoopTime bodyTime fuelValue 0 fuelValue) := by
  simpa [outputProbeDecodeTokenVarInitial] using
    hcomp.outputProbeDecodeTokenVar_hoareTime_internal input output houtput
      extras hextras hcleanupCounter cleanupLimit hcleanupLimit
      controllerTapes layout outerExtras houter cursor tag₀ tag₁ tag₂
      hscratch htag₀Zero htag₁Zero htag₂Zero hvalue hactive hloop
      fuelValue hfuel
      (by simpa [outputProbeDecodeTokenVarInitial] using hqueryValid)
      (by simpa [outputProbeDecodeTokenVarInitial] using hqueryLimit)

/-- Retained-tag cleanup preserves the append-only output discipline. -/
theorem outputProbeDecodeTokenClearTagsTM_isTransducer
    (n controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenClearTagsTM n controllerTapes
      layout).IsTransducer :=
  outputProbeDecodeTokenClearTagsTM_isTransducer_internal n controllerTapes
    layout

/-- Invariant-restoring token dispatch preserves append-only output whenever
all selected continuations do. -/
theorem IsTransducer.outputProbeDecodeTokenDispatchTM
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenDispatchTM n controllerTapes layout onVar onTru
      onFls onNeg onConj onDisj onInvalid).IsTransducer :=
  hvar.outputProbeDecodeTokenDispatchTM_internal htru hfls hneg hconj hdisj
    hinvalid layout

/-- Complete normalized token probing preserves append-only output whenever
every selected continuation does. -/
theorem IsTransducer.outputProbeDecodeTokenTM
    {tm : TM n}
    {onVar onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hvar : onVar.IsTransducer) (htru : onTru.IsTransducer)
    (hfls : onFls.IsTransducer) (hneg : onNeg.IsTransducer)
    (hconj : onConj.IsTransducer) (hdisj : onDisj.IsTransducer)
    (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenTM tm controllerTapes layout onVar onTru onFls
      onNeg onConj onDisj onInvalid).IsTransducer :=
  hvar.outputProbeDecodeTokenTM_internal htru hfls hneg hconj hdisj hinvalid
    layout

/-- The token controller with concrete terminated-unary variable decoding is
append-only whenever all fixed-token and invalid continuations are. -/
theorem IsTransducer.outputProbeDecodeTokenWithNatTM
    {tm : TM n}
    {onTru onFls onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (htru : onTru.IsTransducer) (hfls : onFls.IsTransducer)
    (hneg : onNeg.IsTransducer) (hconj : onConj.IsTransducer)
    (hdisj : onDisj.IsTransducer) (hinvalid : onInvalid.IsTransducer)
    (layout : OutputProbeDecodeTokenLayout controllerTapes) :
    (outputProbeDecodeTokenWithNatTM tm controllerTapes layout onTru onFls
      onNeg onConj onDisj onInvalid).IsTransducer :=
  htru.outputProbeDecodeTokenWithNatTM_internal hfls hneg hconj hdisj
    hinvalid layout

end TM

end Complexity
