/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken

/-!
# Barrington leaf emission after output-probe token decoding -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem latchFramePost_transition
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

theorem outputProbeDecodeVarInstrTM_hoareTime_internal
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
        (outputProbeDecodeVarInstrTime bodyTime fuelValue finalState.value) := by
  dsimp only
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
    cursor tag₀ tag₁ tag₂
  let finalState := outputProbeDecodeNatStateAt (f input)
    (outputProbeDecodeTokenVarInitial cursor) fuelValue
  let finalOuter := outputProbeDecodeNatLoopOuterExtras n
    layout.natLayout.cursorIdx layout.natLayout.valueIdx
    layout.natLayout.activeIdx layout.natLayout.loopIdx after finalState
    fuelValue
  obtain ⟨bodyTime, hdecode⟩ :=
    hcomp.outputProbeDecodeTokenVar_hoareTime input output houtput.parked extras
      hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes layout
      outerExtras houter cursor tag₀ tag₁ tag₂ hscratch htag₀Zero
      htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel
      hqueryValid hqueryLimit
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n layout outerExtras
      houter cursor tag₀ tag₁ tag₂ htag₀Zero htag₁Zero htag₂Zero
  have hfinal : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (finalOuter i) := by
    exact outputProbeDecodeNatLoopOuterExtras_parked n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after hafter
      finalState fuelValue
  have hscratchAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other n layout outerExtras
      cursor tag₀ tag₁ tag₂ layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hscratch
  have hscratchFinal :
      (finalOuter (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after finalState
      fuelValue (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeNatLoopOuterExtras_other n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide)) after finalState fuelValue]
    exact hscratchAfter
  have hvalueFinal :
      (finalOuter (outputProbeIndexedControllerIdx n
        layout.natLayout.valueIdx)).HasBinaryNat finalState.value := by
    simpa [finalOuter, outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatValueIdx] using
      outputProbeDecodeNatStateOuterExtras_value n
        layout.natLayout.cursorIdx layout.natLayout.valueIdx
        layout.natLayout.activeIdx
        (layout.roles.injective.ne (by decide))
        (Function.update after
          (outputProbeIndexedControllerIdx n layout.natLayout.loopIdx)
          (outputProbeCounterTape fuelValue)) finalState
  have hemit := emitInstrTM_latchFrame_hoareTime tm controllerTapes
    layout.natLayout.scratchIdx layout.natLayout.valueIdx
    (layout.roles.injective.ne (by decide)) finalState.value 1 target
    finalOuter input output extras ys hextras hfinal houtput hscratchFinal
    hvalueFinal
  have htransition := latchFramePost_transition tm controllerTapes finalOuter
    input output extras hextras hfinal houtput.parked
  have hrun := seqTM_hoareTime
    (outputProbeDecodeNatTM tm controllerTapes layout.natLayout.cursorIdx
      layout.natLayout.scratchIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      layout.natLayout.fuelIdx)
    (emitInstrTM
      (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) 1 target)
    hdecode htransition hemit
  refine ⟨bodyTime, ?_⟩
  simpa [outputProbeDecodeVarInstrTM, emitVarInstrTM,
    outputProbeDecodeVarInstrTime, after, finalState, finalOuter] using hrun

theorem outputProbeDecodeLeafInstrTM_selected_hoareTime_internal
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
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) selectedTime) := by
  simpa [outputProbeDecodeLeafInstrTM] using
    hcomp.outputProbeDecodeTokenTM_selected_hoareTime input cursor
      hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes layout outerExtras
      houter hcursor hscratch htag₀ htag₁ htag₂
      (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
      (emitConstInstrTM
        (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) target)
      skipTM onNeg onConj onDisj onInvalid hselected

theorem outputProbeDecodeLeafInstrTM_true_hoareTime_internal
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
              (emitInstrTime 0)) := by
  dsimp only
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
    cursor ((f input)[cursor]) ((f input)[cursor + 1])
    ((f input)[cursor + 2])
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n layout outerExtras
      houter cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2]) htag₀ htag₁ htag₂
  have hscratchAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      ((f input)[cursor]) ((f input)[cursor + 1]) ((f input)[cursor + 2])
      (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other n layout outerExtras
      cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2]) layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hscratch
  have hvalueAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.valueIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      ((f input)[cursor]) ((f input)[cursor + 1]) ((f input)[cursor + 2])
      (outputProbeIndexedControllerIdx n
        layout.natLayout.valueIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other n layout outerExtras
      cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2]) layout.natLayout.valueIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hvalue
  have hemit := emitConstInstrTM_latchFrame_hoareTime tm controllerTapes
    layout.natLayout.scratchIdx layout.natLayout.valueIdx
    (layout.roles.injective.ne (by decide)) target after input output extras ys
    hextras hafter houtput hscratchAfter hvalueAfter
  have hrun := hcomp.outputProbeDecodeTokenTM_selected_hoareTime input cursor
    hcursorBound output houtput.parked extras hextras hcleanupCounter
    cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes
    layout outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
    (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
    (emitConstInstrTM
      (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) target)
    skipTM onNeg onConj onDisj onInvalid
    (post := EmitPred
      (outputProbeLatchFrameCfg tm controllerTapes after input output extras
        false).input
      (outputProbeLatchFrameCfg tm controllerTapes after input output extras
        false).work
      (ys ++ Instr.encode (BPInstr.const target)))
    (selectedTime := emitInstrTime 0)
    (by
      simpa [after, hsource₀, hsource₁, hsource₂,
        outputProbeTokenContinuation, outputProbeTokenTag?] using hemit)
  simpa [outputProbeDecodeLeafInstrTM, after] using hrun

theorem outputProbeDecodeLeafInstrTM_var_hoareTime_internal
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
                finalState.value)) := by
  dsimp only
  let finalState := outputProbeDecodeNatStateAt (f input)
    (outputProbeDecodeTokenVarInitial cursor) fuelValue
  let finalOuter := outputProbeDecodeNatLoopOuterExtras n
    layout.natLayout.cursorIdx layout.natLayout.valueIdx
    layout.natLayout.activeIdx layout.natLayout.loopIdx
    (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      ((f input)[cursor]) ((f input)[cursor + 1]) ((f input)[cursor + 2]))
    finalState fuelValue
  obtain ⟨bodyTime, hvar⟩ := outputProbeDecodeVarInstrTM_hoareTime_internal
    hcomp input output ys houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit controllerTapes layout outerExtras houter cursor
    ((f input)[cursor]) ((f input)[cursor + 1]) ((f input)[cursor + 2])
    hscratch htag₀ htag₁ htag₂ hvalue hactive hloop fuelValue hfuel
    hqueryValid hqueryLimit target
  obtain ⟨bound₀, bound₁, bound₂, pre, hpre, hrun⟩ :=
    hcomp.outputProbeDecodeTokenTM_selected_hoareTime input cursor
      hcursorBound output houtput.parked extras hextras hcleanupCounter
      cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes
      layout outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
      (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
      (emitConstInstrTM
        (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) target)
      skipTM onNeg onConj onDisj onInvalid
      (post := EmitPred
        (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
          extras false).work
        (ys ++ Instr.encode ⟨finalState.value, 1, target⟩))
      (selectedTime := outputProbeDecodeVarInstrTime bodyTime fuelValue
        finalState.value)
      (by
        simpa [finalState, finalOuter, hsource₀, hsource₁, hsource₂,
          outputProbeTokenContinuation, outputProbeTokenTag?] using hvar)
  exact ⟨bodyTime, bound₀, bound₁, bound₂, pre, hpre,
    by simpa [outputProbeDecodeLeafInstrTM] using hrun⟩

theorem outputProbeDecodeLeafInstrTM_false_hoareTime_internal
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
              ((f input)[cursor + 1]) ((f input)[cursor + 2]) 1) := by
  dsimp only
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
    cursor ((f input)[cursor]) ((f input)[cursor + 1])
    ((f input)[cursor + 2])
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n layout outerExtras
      houter cursor ((f input)[cursor]) ((f input)[cursor + 1])
      ((f input)[cursor + 2]) htag₀ htag₁ htag₂
  have hskip := skipTM_latchFrame_hoareTime tm controllerTapes after input
    output extras ys hextras hafter houtput
  have hrun := hcomp.outputProbeDecodeTokenTM_selected_hoareTime input cursor
    hcursorBound output houtput.parked extras hextras hcleanupCounter
    cleanupLimit hcleanupLimit hlimit₀ hlimit₁ hlimit₂ controllerTapes
    layout outerExtras houter hcursor hscratch htag₀ htag₁ htag₂
    (outputProbeDecodeVarInstrTM tm controllerTapes layout target)
    (emitConstInstrTM
      (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) target)
    skipTM onNeg onConj onDisj onInvalid
    (post := EmitPred
      (outputProbeLatchFrameCfg tm controllerTapes after input output extras
        false).input
      (outputProbeLatchFrameCfg tm controllerTapes after input output extras
        false).work ys)
    (selectedTime := 1)
    (by
      simpa [after, hsource₀, hsource₁, hsource₂,
        outputProbeTokenContinuation, outputProbeTokenTag?] using hskip)
  simpa [outputProbeDecodeLeafInstrTM, after] using hrun

end Machine

end BPCode

end Complexity
