/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Defs
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Internal

/-!
# Barrington leaf emission after output-probe token decoding

This module exposes the concrete variable-token continuation: it decodes the
terminated-unary payload, preserves the restartable query frame, and appends
the exact canonical Barrington variable instruction.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- Decode a variable payload from the normalized post-tag frame and append
the resulting canonical Barrington instruction. -/
theorem outputProbeDecodeVarInstrTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (ys : List Bool)
    (houtput : OutAcc ys output)
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
            cleanupLimit)
    (target : Equiv.Perm (Fin 5)) :
    let finalState := outputProbeDecodeNatStateAt (f input)
      (outputProbeDecodeTokenVarInitial cursor) fuelValue
    let finalOuter := outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
        tag₀ tag₁ tag₂)
      finalState fuelValue
    ∃ bodyTime : ℕ → ℕ,
      (outputProbeDecodeVarInstrTM tm controllerTapes layout target).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
            tag₀ tag₁ tag₂)
          input output extras false)
        (EmitPred
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).input
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).work
          (ys ++ Instr.encode ⟨finalState.value, 1, target⟩))
        (outputProbeDecodeVarInstrTime bodyTime fuelValue finalState.value) :=
  outputProbeDecodeVarInstrTM_hoareTime_internal hcomp input output ys
    houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    controllerTapes layout outerExtras houter cursor tag₀ tag₁ tag₂ hscratch
    htag₀Zero htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel
    hqueryValid hqueryLimit target

/-- Probe a complete source token and enter only its selected concrete leaf or
caller-supplied recursive continuation. -/
theorem outputProbeDecodeLeafInstrTM_selected_hoareTime
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
    (target : Equiv.Perm (Fin 5))
    (onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {selectedTime : ℕ}
    (hselected :
      (outputProbeTokenContinuation
        (outputProbeTokenTag? ((f input)[cursor]) ((f input)[cursor + 1])
          ((f input)[cursor + 2]))
        (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
        (emitConstInstrTM
          (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
          (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx)
          target)
        skipTM onNeg onConj onDisj onInvalid).HoareTime
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
      (outputProbeDecodeLeafInstrTM tm controllerTapes layout target onNeg
        onConj onDisj onInvalid).HoareTime pre post
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) selectedTime) :=
  outputProbeDecodeLeafInstrTM_selected_hoareTime_internal hcomp input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras
    houter hcursor hscratch htag₀ htag₁ htag₂ target onNeg onConj onDisj
    onInvalid hselected

/-- Decode a complete `true` leaf from the source and append exactly its
canonical Barrington constant instruction. -/
theorem outputProbeDecodeLeafInstrTM_true_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (hsource₀ : (f input)[cursor] = false)
    (hsource₁ : (f input)[cursor + 1] = false)
    (hsource₂ : (f input)[cursor + 2] = true)
    (output : Tape) (ys : List Bool) (houtput : OutAcc ys output)
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
    (hvalue :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx))
        |>.HasBinaryNat 0)
    (target : Equiv.Perm (Fin 5))
    (onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
      cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2])
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
      (outputProbeDecodeLeafInstrTM tm controllerTapes layout target onNeg
        onConj onDisj onInvalid).HoareTime pre
          (EmitPred
            (outputProbeLatchFrameCfg tm controllerTapes after input output
              extras false).input
            (outputProbeLatchFrameCfg tm controllerTapes after input output
              extras false).work
            (ys ++ Instr.encode (BPInstr.const target)))
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2])
              (emitInstrTime 0)) :=
  outputProbeDecodeLeafInstrTM_true_hoareTime_internal hcomp input cursor
    hcursorBound hsource₀ hsource₁ hsource₂ output ys houtput extras hextras
    hcleanupCounter cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂
    controllerTapes layout outerExtras houter hcursor hscratch htag₀ htag₁
    htag₂ hvalue target onNeg onConj onDisj onInvalid

/-- Decode a complete variable leaf and append exactly the instruction named
by its terminated-unary payload. Payload validity is required only here. -/
theorem outputProbeDecodeLeafInstrTM_var_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (hsource₀ : (f input)[cursor] = false)
    (hsource₁ : (f input)[cursor + 1] = false)
    (hsource₂ : (f input)[cursor + 2] = false)
    (output : Tape) (ys : List Bool) (houtput : OutAcc ys output)
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
            cleanupLimit)
    (target : Equiv.Perm (Fin 5))
    (onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    let finalState := outputProbeDecodeNatStateAt (f input)
      (outputProbeDecodeTokenVarInitial cursor) fuelValue
    let finalOuter := outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
        ((f input)[cursor]) ((f input)[cursor + 1])
        ((f input)[cursor + 2]))
      finalState fuelValue
    ∃ (bodyTime : ℕ → ℕ) (bound₀ bound₁ bound₂ : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeLeafInstrTM tm controllerTapes layout target onNeg
        onConj onDisj onInvalid).HoareTime pre
          (EmitPred
            (outputProbeLatchFrameCfg tm controllerTapes finalOuter input
              output extras false).input
            (outputProbeLatchFrameCfg tm controllerTapes finalOuter input
              output extras false).work
            (ys ++ Instr.encode ⟨finalState.value, 1, target⟩))
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2])
              (outputProbeDecodeVarInstrTime bodyTime fuelValue
                finalState.value)) :=
  outputProbeDecodeLeafInstrTM_var_hoareTime_internal hcomp input cursor
    hcursorBound hsource₀ hsource₁ hsource₂ output ys houtput extras hextras
    hcleanupCounter cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂
    controllerTapes layout outerExtras houter hcursor hscratch htag₀ htag₁
    htag₂ hvalue hactive hloop fuelValue hfuel hqueryValid hqueryLimit target
    onNeg onConj onDisj onInvalid

/-- Decode a complete `false` leaf while leaving the serialized instruction
accumulator unchanged. -/
theorem outputProbeDecodeLeafInstrTM_false_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor + 2 < (f input).length)
    (hsource₀ : (f input)[cursor] = false)
    (hsource₁ : (f input)[cursor + 1] = true)
    (hsource₂ : (f input)[cursor + 2] = false)
    (output : Tape) (ys : List Bool) (houtput : OutAcc ys output)
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
    (target : Equiv.Perm (Fin 5))
    (onNeg onConj onDisj onInvalid :
      TM (0 + outputProbeControllerTapes n + controllerTapes)) :
    let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
      cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2])
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
      (outputProbeDecodeLeafInstrTM tm controllerTapes layout target onNeg
        onConj onDisj onInvalid).HoareTime pre
          (EmitPred
            (outputProbeLatchFrameCfg tm controllerTapes after input output
              extras false).input
            (outputProbeLatchFrameCfg tm controllerTapes after input output
              extras false).work ys)
          (((bound₀ + 1 + binarySuccTime cursor) + 1 +
            ((bound₁ + 1 + binarySuccTime (cursor + 1)) + 1 +
              (bound₂ + 1 + binarySuccTime (cursor + 2)))) + 1 +
            outputProbeDecodeTokenSelectedDispatchTime ((f input)[cursor])
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) 1) :=
  outputProbeDecodeLeafInstrTM_false_hoareTime_internal hcomp input cursor
    hcursorBound hsource₀ hsource₁ hsource₂ output ys houtput extras hextras
    hcleanupCounter cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂
    controllerTapes layout outerExtras houter hcursor hscratch htag₀ htag₁
    htag₂ target onNeg onConj onDisj onInvalid

end Machine

end BPCode

end Complexity
