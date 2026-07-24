/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeIndexed.Defs
import Complexitylib.Models.TuringMachine.OutputProbeLatch
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy

/-!
# Dynamically indexed restartable output probes -- proof internals
-/

namespace Complexity

namespace TM

private theorem outputProbeIndexed_hasBinaryNat_parked {tape : Tape}
    {value : ℕ} (hvalue : tape.HasBinaryNat value) : Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

theorem outputProbeLatchFrameCfg_work_eq_queryUpdate_internal
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (controllerTapes value : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work =
      Function.update
        (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (value + 1)) output extras)).work
        (outputProbeIndexedCountdownIdx n controllerTapes)
        (outputProbeCounterTape 0) := by
  have hcleanupCounterEq : extras (outputProbeCleanupCounterIdx n) =
      outputProbeCounterTape 0 := by
    simpa [outputProbeCounterTape] using hcleanupCounter.eq_init_move_right
  funext i
  by_cases houterMiddle :
      placeWorkInMiddle 0 (outputProbeControllerTapes n) i
  · generalize hcoord :
      placeWorkCoord 0 (outputProbeControllerTapes n) i houterMiddle = coord
    have hphysical : placeWorkIdx 0 controllerTapes coord = i := by
      rw [← hcoord]
      exact placeWorkIdx_placeWorkCoord i houterMiddle
    rw [← hphysical]
    rw [outputProbeLatchFrameCfg, placeWorkCfg_work_middle,
      outputProbeIndexedCountdownIdx]
    change
      (outputProbeLatchInnerFrameCfg tm input output extras false).work coord =
        Function.update
          (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
            (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (value + 1)) output extras)).work
          (placeWorkIdx 0 controllerTapes
            (outputProbeCleanupCountdownIdx n))
          (outputProbeCounterTape 0) (placeWorkIdx 0 controllerTapes coord)
    by_cases hcountdown : coord = outputProbeCleanupCountdownIdx n
    · try rw [hcoord]
      rw [hcountdown]
      rw [Function.update_self]
      simp only [outputProbeLatchInnerFrameCfg, Bool.false_eq_true, if_false]
      rw [Function.update_of_ne]
      · let countdownIdx : Fin (n + 2) := ⟨n, by omega⟩
        have hcountdownPhysical : outputProbeCleanupCountdownIdx n =
            placeWorkIdx 0 2 countdownIdx := by
          apply Fin.ext
          simp [outputProbeCleanupCountdownIdx, countdownIdx]
        rw [hcountdownPhysical, outputProbePlacedFrameCfg,
          placeWorkCfg_work_middle]
        rw [retargetCfgFrame_work_lt _ _ _ countdownIdx (by
          dsimp only [countdownIdx]
          omega)]
        simp [outputProbeStartedCfg, countdownIdx, outputProbeCounterTape]
      · intro heq
        have hval := congrArg Fin.val heq
        simp [outputProbeCleanupCountdownIdx, outputProbeCleanupCounterIdx]
          at hval
    · rw [Function.update_of_ne]
      · rw [placeWorkCfg_work_middle]
        simp only [outputProbeLatchInnerFrameCfg, Bool.false_eq_true, if_false]
        by_cases hcounter : coord = outputProbeCleanupCounterIdx n
        · try rw [hcoord]
          rw [hcounter]
          rw [Function.update_self]
          rw [outputProbePlacedFrameCfg, placeWorkCfg_work_extra]
          · exact hcleanupCounterEq.symm
          · simp [placeWorkInMiddle, outputProbeCleanupCounterIdx]
        · rw [Function.update_of_ne hcounter]
          rw [outputProbePlacedFrameCfg, outputProbePlacedFrameCfg]
          by_cases hinnerMiddle : placeWorkInMiddle 0 (n + 2) coord
          · generalize hsourceCoord :
              placeWorkCoord 0 (n + 2) coord hinnerMiddle = source
            have hsourcePhysical : placeWorkIdx 0 2 source = coord := by
              rw [← hsourceCoord]
              exact placeWorkIdx_placeWorkCoord coord hinnerMiddle
            rw [← hsourcePhysical, placeWorkCfg_work_middle,
              placeWorkCfg_work_middle]
            by_cases hsource : source.val < n + 1
            · rw [retargetCfgFrame_work_lt _ _ _ source hsource,
                retargetCfgFrame_work_lt _ _ _ source hsource]
              have hsourceWork : source.val < n := by
                by_contra hnot
                have hsourceEq : source.val = n := by omega
                apply hcountdown
                apply Fin.ext
                rw [← hsourcePhysical]
                simpa [outputProbeCleanupCountdownIdx, placeWorkIdx] using
                  hsourceEq
              simp [outputProbeStartedCfg, hsourceWork]
            · have hlast : source = Fin.last (n + 1) := by
                apply Fin.ext
                simp only [Fin.last]
                omega
              rw [hlast, retargetCfgFrame_work_last,
                retargetCfgFrame_work_last]
              simp [outputProbeStartedCfg]
          · rw [placeWorkCfg_work_extra _ _ _ extras _ coord hinnerMiddle,
              placeWorkCfg_work_extra _ _ _ extras _ coord hinnerMiddle]
      · intro heq
        exact hcountdown (placeWorkIdx_injective 0 controllerTapes heq)
  · rw [outputProbeLatchFrameCfg,
      placeWorkCfg_work_extra _ _ _ outerExtras _ i houterMiddle]
    rw [Function.update_of_ne]
    · rw [placeWorkCfg_work_extra _ _ _ outerExtras _ i houterMiddle]
    · intro heq
      subst i
      apply houterMiddle
      simp [outputProbeIndexedCountdownIdx, placeWorkInMiddle, placeWorkIdx,
        outputProbeCleanupCountdownIdx]
      dsimp only [outputProbeControllerTapes]
      omega

theorem outputProbeIndexedControllerIdx_injective_internal
    (n : ℕ) {controllerTapes : ℕ} :
    Function.Injective
      (@outputProbeIndexedControllerIdx n controllerTapes) := by
  intro left right heq
  apply Fin.ext
  apply congrArg Fin.val at heq
  simp only [outputProbeIndexedControllerIdx] at heq
  omega

theorem outputProbeIndexedControllerIdx_not_middle_internal
    (n : ℕ) {controllerTapes : ℕ} (idx : Fin controllerTapes) :
    ¬placeWorkInMiddle 0 (outputProbeControllerTapes n)
      (outputProbeIndexedControllerIdx n idx) := by
  simp [placeWorkInMiddle, outputProbeIndexedControllerIdx]

theorem outputProbeIndexedCountdownIdx_middle_internal
    (n controllerTapes : ℕ) :
    placeWorkInMiddle 0 (outputProbeControllerTapes n)
      (outputProbeIndexedCountdownIdx n controllerTapes) := by
  simp [outputProbeIndexedCountdownIdx, placeWorkInMiddle, placeWorkIdx,
    outputProbeCleanupCountdownIdx]
  dsimp only [outputProbeControllerTapes]
  omega

theorem outputProbeIndexedControllerIdx_ne_countdown_internal
    (n : ℕ) {controllerTapes : ℕ} (idx : Fin controllerTapes) :
    outputProbeIndexedControllerIdx n idx ≠
      outputProbeIndexedCountdownIdx n controllerTapes := by
  intro heq
  have hmiddle := outputProbeIndexedCountdownIdx_middle_internal n
    controllerTapes
  rw [← heq] at hmiddle
  exact outputProbeIndexedControllerIdx_not_middle_internal n idx hmiddle

theorem outputProbeLatchFramePost_controller_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out)
    (idx : Fin controllerTapes) :
    work (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  obtain ⟨sourceWork, _hsource, hwork⟩ := hpost
  rw [hwork, placeWorkCfg_work_extra]
  exact outputProbeIndexedControllerIdx_not_middle_internal n idx

theorem outputProbeLatchFramePost_updateController_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out)
    (idx : Fin controllerTapes) (tape : Tape) :
    outputProbeLatchFramePost tm controllerTapes
      (Function.update outerExtras
        (outputProbeIndexedControllerIdx n idx) tape)
      input output extras bit inp
      (Function.update work
        (outputProbeIndexedControllerIdx n idx) tape)
      out := by
  obtain ⟨sourceWork, hsource, hwork⟩ := hpost
  refine ⟨sourceWork, hsource, ?_⟩
  rw [hwork]
  funext i
  by_cases hi : i = outputProbeIndexedControllerIdx n idx
  · subst i
    rw [Function.update_self, placeWorkCfg_work_extra]
    · simp only [Function.update_self]
    · exact outputProbeIndexedControllerIdx_not_middle_internal n idx
  · rw [Function.update_of_ne hi]
    by_cases hmiddle : placeWorkInMiddle 0 (outputProbeControllerTapes n) i
    · simp only [placeWorkCfg, hmiddle, dite_true]
    · rw [placeWorkCfg_work_extra _ _ _ outerExtras _ i hmiddle]
      rw [placeWorkCfg_work_extra _ _ _
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx) tape) _ i hmiddle]
      rw [Function.update_of_ne hi]

theorem outputProbeIndexedFrameCountdown_internal
    (tm : TM n) (controllerTapes value : ℕ)
    (input : List Bool) (output : Tape)
    (innerExtras : Fin (outputProbeControllerTapes n) → Tape)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape) :
    let innerCfg := outputProbePlacedFrameCfg tm input
      (outputProbeCounterTape value) output innerExtras
    let framedCfg := placeWorkCfg (outputProbePlacedTM tm) 0
      controllerTapes outerExtras innerCfg
    (framedCfg.work
      (outputProbeIndexedCountdownIdx n controllerTapes)).HasBinaryNat value := by
  dsimp only
  rw [outputProbeIndexedCountdownIdx, placeWorkCfg_work_middle]
  let countdownIdx : Fin (n + 2) := ⟨n, by omega⟩
  have hphysical : outputProbeCleanupCountdownIdx n =
      placeWorkIdx 0 2 countdownIdx := by
    apply Fin.ext
    simp [outputProbeCleanupCountdownIdx, countdownIdx]
  rw [outputProbePlacedFrameCfg, hphysical, placeWorkCfg_work_middle]
  rw [retargetCfgFrame_work_lt _ _ _ countdownIdx (by
    dsimp only [countdownIdx]
    omega)]
  simpa [outputProbeStartedCfg, countdownIdx, outputProbeCounterTape] using
    Tape.init_move_right_hasBinaryNat value

theorem outputProbeIndexedPrepareTM_hoareTimeSpace_internal
    (n controllerTapes : ℕ) (sourceIdx scratchIdx : Fin controllerTapes)
    (hdistinct : sourceIdx ≠ scratchIdx)
    (index inputLength initialSpace : ℕ)
    (inp₀ : Tape)
    (work₀ : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out₀ : Tape)
    (hsource :
      (work₀ (outputProbeIndexedControllerIdx n sourceIdx)).HasBinaryNat
        index)
    (hcountdown :
      (work₀ (outputProbeIndexedCountdownIdx n controllerTapes)).HasBinaryNat 0)
    (hscratch :
      (work₀ (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat 0)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    let countdown := outputProbeIndexedCountdownIdx n controllerTapes
    (outputProbeIndexedPrepareTM n controllerTapes
      sourceIdx scratchIdx).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          (∀ i, i ≠ countdown → work i = work₀ i) ∧
          (work countdown).HasBinaryNat (index + 1) ∧
          out = out₀)
        (outputProbeIndexedPrepareTime index) inputLength
        (outputProbeIndexedPrepareSpace initialSpace index) := by
  dsimp only
  let source := outputProbeIndexedControllerIdx n sourceIdx
  let countdown := outputProbeIndexedCountdownIdx n controllerTapes
  let scratch := outputProbeIndexedControllerIdx n scratchIdx
  have hsourceCountdown : source ≠ countdown := by
    exact outputProbeIndexedControllerIdx_ne_countdown_internal n sourceIdx
  have hscratchCountdown : scratch ≠ countdown := by
    exact outputProbeIndexedControllerIdx_ne_countdown_internal n scratchIdx
  have hsourceScratch : source ≠ scratch := by
    exact (outputProbeIndexedControllerIdx_injective_internal n).ne hdistinct
  let copiedWork := Function.update work₀ countdown
    ((Tape.init (index.bits.map Γ.ofBool)).move Dir3.right)
  have hcopy := binaryCopyIntoTM_hoareTimeSpace_frame
    source countdown scratch hsourceCountdown hsourceScratch
    hscratchCountdown.symm index 0 inputLength initialSpace inp₀ work₀ out₀
    hsource hcountdown hscratch hinput (fun i _ _ _ => hwork i) houtput
    hworkSpace hinputSpace
  have hcopiedCountdown :
      (copiedWork countdown).HasBinaryNat index := by
    simpa [copiedWork] using Tape.init_move_right_hasBinaryNat index
  have hcopiedParked : ∀ i, Parked (copiedWork i) := by
    intro i
    by_cases hi : i = countdown
    · subst i
      exact outputProbeIndexed_hasBinaryNat_parked hcopiedCountdown
    · dsimp only [copiedWork]
      simpa [hi] using hwork i
  have hinitialOne : 1 ≤ initialSpace := by
    rw [← hcountdown.2.1]
    exact hworkSpace countdown
  have hcopiedWithin :
      (⟨(binarySuccTM countdown).qstart, inp₀, copiedWork, out₀⟩ :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (binarySuccTM countdown).Q).WithinAuxSpace inputLength
        (binaryCopySpace initialSpace index 0) := by
    constructor
    · intro i
      by_cases hi : i = countdown
      · subst i
        rw [hcopiedCountdown.2.1]
        simp [binaryCopySpace]
        omega
      · dsimp only [copiedWork]
        simpa [hi] using (hworkSpace i).trans (by simp [binaryCopySpace])
    · exact hinputSpace.trans (by simp [binaryCopySpace])
  have hsucc := binarySuccTM_hoareTimeSpace_frame countdown index
    inputLength (binaryCopySpace initialSpace index 0) inp₀ copiedWork out₀
    hcopiedCountdown hinput.read_ne_start
    (fun i _ => (hcopiedParked i).read_ne_start) houtput.read_ne_start
    hcopiedWithin
  have hseq := seqTM_hoareTimeSpace
    (binaryCopyIntoTM source countdown scratch) (binarySuccTM countdown)
    hcopy (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      exact ⟨hinput.transitionInput_eq_self,
        funext fun i => (hcopiedParked i).transitionTape_eq_self,
        houtput.transitionTape_eq_self⟩) hsucc
  have hseq' :
      (seqTM (binaryCopyIntoTM source countdown scratch)
        (binarySuccTM countdown)).HoareTimeSpace
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out =>
          inp = inp₀ ∧
          (∀ i, i ≠ countdown → work i = work₀ i) ∧
          (work countdown).HasBinaryNat (index + 1) ∧
          out = out₀)
        (binaryCopyTime index 0 + 1 + binarySuccTime index) inputLength
        (max (binaryCopySpace initialSpace index 0)
          (binaryCopySpace initialSpace index 0 + binarySuccTime index)) := by
    apply hseq.consequence (fun _ _ _ h => h) _ le_rfl le_rfl le_rfl
    rintro inp work out ⟨hinputEq, hother, hvalue, houtputEq⟩
    refine ⟨hinputEq, ?_, hvalue, houtputEq⟩
    intro i hi
    rw [hother i hi]
    simp [copiedWork, hi]
  simpa [outputProbeIndexedPrepareTM, outputProbeIndexedPrepareTime,
    outputProbeIndexedPrepareSpace, source, countdown, scratch, copiedWork,
    max_eq_right (Nat.le_add_right _ _)] using hseq'

private theorem outputProbeIndexedLatchTM_compose_internal
    (tm : TM n) (input : List Bool) (index : ℕ)
    (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (hdistinct : sourceIdx ≠ scratchIdx)
    (initialSpace : ℕ)
    (work₀ : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (hsource :
      (work₀ (outputProbeIndexedControllerIdx n sourceIdx)).HasBinaryNat
        index)
    (hcountdown :
      (work₀ (outputProbeIndexedCountdownIdx n
        controllerTapes)).HasBinaryNat 0)
    (hscratch :
      (work₀ (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat 0)
    (hinput : Parked
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input)
    (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked output)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace :
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input.head ≤
        input.length + initialSpace + 1)
    (hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      work₀ i =
        (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras)).work i)
    {post : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace : ℕ}
    (hlatch : (outputProbeLatchTM tm controllerTapes).HoareTimeSpace
      (placeWorkPred (outputProbeLatchInnerTM tm) 0 controllerTapes
        outerExtras
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output))
      post latchTime input.length latchSpace) :
    (outputProbeIndexedLatchTM tm controllerTapes sourceIdx
      scratchIdx).HoareTimeSpace
        (fun inp work out =>
          inp =
              (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
                outerExtras
                (outputProbePlacedFrameCfg tm input
                  (outputProbeCounterTape (index + 1)) output extras)).input ∧
          work = work₀ ∧ out = output)
        post
        (outputProbeIndexedPrepareTime index + 1 + latchTime)
        input.length
        (max (outputProbeIndexedPrepareSpace initialSpace index)
          latchSpace) := by
  let innerCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape (index + 1)) output extras
  let queryCfg := placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
    outerExtras innerCfg
  let countdown := outputProbeIndexedCountdownIdx n controllerTapes
  have hqueryCountdown :
      (queryCfg.work countdown).HasBinaryNat (index + 1) := by
    simpa [queryCfg, innerCfg, countdown] using
      outputProbeIndexedFrameCountdown_internal tm controllerTapes
        (index + 1) input output extras outerExtras
  have hprepare :=
    outputProbeIndexedPrepareTM_hoareTimeSpace_internal n controllerTapes
      sourceIdx scratchIdx hdistinct index input.length initialSpace
      queryCfg.input work₀ output hsource hcountdown hscratch (by
        simpa [queryCfg, innerCfg] using hinput) hwork houtput hworkSpace (by
        simpa [queryCfg, innerCfg] using hinputSpace)
  have hseq := seqTM_hoareTimeSpace
    (outputProbeIndexedPrepareTM n controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchTM tm controllerTapes) hprepare (by
      rintro inp work out ⟨hinp, hother, hvalue, hout⟩
      have hworkEq : work = queryCfg.work := by
        funext i
        by_cases hi : i = countdown
        · subst i
          exact hvalue.eq_init_move_right.trans
            hqueryCountdown.eq_init_move_right.symm
        · exact (hother i hi).trans (hqueryWork i (by
            simpa [countdown] using hi))
      have hworkParked : ∀ i, Parked (work i) := by
        intro i
        by_cases hi : i = countdown
        · subst i
          exact outputProbeIndexed_hasBinaryNat_parked hvalue
        · rw [hother i hi]
          exact hwork i
      have htransitionWork :
          (fun i => transitionTape (work i)) = work := by
        funext i
        exact (hworkParked i).transitionTape_eq_self
      rw [(show Parked inp by rw [hinp]; simpa [queryCfg, innerCfg] using
        hinput).transitionInput_eq_self, htransitionWork,
        (show Parked out by rw [hout]; exact houtput).transitionTape_eq_self,
        hinp, hworkEq, hout]
      refine ⟨innerCfg.work, ?_, ?_⟩
      · exact ⟨by simp [queryCfg, innerCfg], rfl, rfl⟩
      · rfl) hlatch
  simpa [outputProbeIndexedLatchTM, queryCfg, innerCfg, countdown] using hseq

theorem ComputesInSpace.outputProbeIndexedLatchTM_hoareTimeSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace limit : ℕ)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace)
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat limit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (index + 1) ≤ limit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (outerFrameSpace : ℕ)
    (houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start)
    (houterFrame : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (hdistinct : sourceIdx ≠ scratchIdx)
    (initialSpace : ℕ)
    (work₀ : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (hsource :
      (work₀ (outputProbeIndexedControllerIdx n sourceIdx)).HasBinaryNat
        index)
    (hcountdown :
      (work₀ (outputProbeIndexedCountdownIdx n
        controllerTapes)).HasBinaryNat 0)
    (hscratch :
      (work₀ (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat 0)
    (hinput : Parked
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input)
    (hwork : ∀ i, Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace :
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input.head ≤
        input.length + initialSpace + 1)
    (hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      work₀ i =
        (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras)).work i) :
    ∃ latchTime,
      (outputProbeIndexedLatchTM tm controllerTapes sourceIdx
        scratchIdx).HoareTimeSpace
          (fun inp work out =>
            inp =
                (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
                  outerExtras
                  (outputProbePlacedFrameCfg tm input
                    (outputProbeCounterTape (index + 1)) output extras)).input ∧
            work = work₀ ∧ out = output)
          (outputProbeLatchFramePost tm controllerTapes outerExtras input
            output extras ((f input)[index]'hindex))
          (outputProbeIndexedPrepareTime index + 1 + latchTime)
          input.length
          (max (outputProbeIndexedPrepareSpace initialSpace index)
            (max
              (outputProbeConsumeSpace n (max 1 (space input.length)) index
                frameSpace limit
                (outputProbeLatchContinuationSpace
                  ((f input)[index]'hindex) frameSpace))
              outerFrameSpace)) := by
  obtain ⟨latchTime, hlatch⟩ :=
    hcomp.outputProbeLatchTM_hoareTimeSpace input index hindex output houtput
      extras frameSpace limit hextras hframe hcleanupCounter hcleanupLimit
      hlimit controllerTapes outerExtras outerFrameSpace houterRead houterFrame
  refine ⟨latchTime, ?_⟩
  exact outputProbeIndexedLatchTM_compose_internal tm input index output
    extras controllerTapes outerExtras sourceIdx scratchIdx hdistinct
    initialSpace work₀ hsource hcountdown hscratch hinput hwork houtput
    hworkSpace hinputSpace hqueryWork hlatch

theorem
    ComputesInSpace.outputProbeIndexedLatchTM_index_halts_hoareTimeSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (index : ℕ)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace limit : ℕ)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace)
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat limit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (index + 1) ≤ limit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (outerFrameSpace : ℕ)
    (houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start)
    (houterFrame : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (hdistinct : sourceIdx ≠ scratchIdx)
    (initialSpace : ℕ)
    (work₀ : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (hsource :
      (work₀ (outputProbeIndexedControllerIdx n sourceIdx)).HasBinaryNat
        index)
    (hcountdown :
      (work₀ (outputProbeIndexedCountdownIdx n
        controllerTapes)).HasBinaryNat 0)
    (hscratch :
      (work₀ (outputProbeIndexedControllerIdx n scratchIdx)).HasBinaryNat 0)
    (hinput : Parked
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input)
    (hwork : ∀ i, Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace :
      (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras)).input.head ≤
        input.length + initialSpace + 1)
    (hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      work₀ i =
        (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes outerExtras
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras)).work i) :
    ∃ bit latchTime,
      (outputProbeIndexedLatchTM tm controllerTapes sourceIdx
        scratchIdx).HoareTimeSpace
          (fun inp work out =>
            inp =
                (placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
                  outerExtras
                  (outputProbePlacedFrameCfg tm input
                    (outputProbeCounterTape (index + 1)) output extras)).input ∧
            work = work₀ ∧ out = output)
          (outputProbeLatchFramePost tm controllerTapes outerExtras input
            output extras bit)
          (outputProbeIndexedPrepareTime index + 1 + latchTime)
          input.length
          (max (outputProbeIndexedPrepareSpace initialSpace index)
            (max
              (outputProbeConsumeSpace n (max 1 (space input.length)) index
                frameSpace limit
                (outputProbeLatchContinuationSpace bit frameSpace))
              outerFrameSpace)) := by
  obtain ⟨bit, latchTime, hlatch⟩ :=
    hcomp.outputProbeLatchTM_index_halts_hoareTimeSpace input index output
      houtput extras frameSpace limit hextras hframe hcleanupCounter
      hcleanupLimit hlimit controllerTapes outerExtras outerFrameSpace
      houterRead houterFrame
  refine ⟨bit, latchTime, ?_⟩
  exact outputProbeIndexedLatchTM_compose_internal tm input index output
    extras controllerTapes outerExtras sourceIdx scratchIdx hdistinct
    initialSpace work₀ hsource hcountdown hscratch hinput hwork houtput
    hworkSpace hinputSpace hqueryWork hlatch

theorem outputProbeIndexedPrepareTM_isTransducer_internal
    (n controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    (outputProbeIndexedPrepareTM n controllerTapes
      sourceIdx scratchIdx).IsTransducer := by
  unfold outputProbeIndexedPrepareTM
  exact (binaryCopyIntoTM_isTransducer _ _ _).seqTM
    (binarySuccTM_isTransducer _)

theorem outputProbeIndexedLatchTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    (outputProbeIndexedLatchTM tm controllerTapes
      sourceIdx scratchIdx).IsTransducer := by
  unfold outputProbeIndexedLatchTM
  exact (outputProbeIndexedPrepareTM_isTransducer_internal n controllerTapes
    sourceIdx scratchIdx).seqTM
      (outputProbeLatchTM_isTransducer tm controllerTapes)

end TM

end Complexity
