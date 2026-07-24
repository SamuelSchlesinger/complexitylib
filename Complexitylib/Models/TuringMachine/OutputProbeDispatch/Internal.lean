/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Defs
import Complexitylib.Models.TuringMachine.OutputProbeIndexed
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Dynamically indexed output-probe dispatch -- proof internals
-/

namespace Complexity

namespace TM

private theorem outputProbeDispatch_hasBinaryNat_parked {tape : Tape}
    {value : ℕ} (hvalue : tape.HasBinaryNat value) : Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

private theorem outputProbeDispatch_cleanInput_parked
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) :
    Parked (outputProbePlacedFrameCfg tm input (outputProbeCounterTape 0)
      output extras).input := by
  simp only [outputProbePlacedFrameCfg, placeWorkCfg_input,
    retargetCfgFrame_input, outputProbeStartedCfg]
  simpa [Tape.move] using parked_init_input input

private theorem outputProbeDispatch_cleanWork_parked
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i)) :
    ∀ i, Parked ((outputProbePlacedFrameCfg tm input
      (outputProbeCounterTape 0) output extras).work i) := by
  intro i
  rw [outputProbePlacedFrameCfg]
  by_cases hi : placeWorkInMiddle 0 (n + 2) i
  · simp only [placeWorkCfg, hi, dite_true]
    let coord := placeWorkCoord 0 (n + 2) i hi
    by_cases hsource : coord.val < n + 1
    · rw [retargetCfgFrame_work_lt _ _ _ coord (by omega)]
      by_cases hsourceWork : coord.val < n
      · simp [outputProbeStartedCfg, hsourceWork]
        simpa [Tape.move] using parked_init_input ([] : List Bool)
      · simp [outputProbeStartedCfg, hsourceWork]
        exact outputProbeDispatch_hasBinaryNat_parked
          (Tape.init_move_right_hasBinaryNat 0)
    · have hvirtualOutput : coord = Fin.last (n + 1) := by
        apply Fin.ext
        simp only [Fin.last, coord]
        have hcoord : coord.val < n + 2 := coord.isLt
        omega
      change Parked
        ((tm.outputProbeStartedTM.retargetCfgFrame
          (tm.outputProbeStartedCfg input (outputProbeCounterTape 0))
          output).work coord)
      rw [hvirtualOutput, retargetCfgFrame_work_last]
      simp [outputProbeStartedCfg]
      simpa [Tape.move] using parked_init_input ([] : List Bool)
  · rw [placeWorkCfg_work_extra]
    exact hextras i hi
    exact hi

theorem outputProbeLatchFramePost_parked_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out) :
    Parked inp ∧ (∀ i, Parked (work i)) ∧ Parked out := by
  rcases hpost with ⟨sourceWork, hsource, hworkEq⟩
  rcases hsource with ⟨hinputEq, hother, hlatch, houtputEq⟩
  have hsourceWorkParked : ∀ i, Parked (sourceWork i) := by
    intro i
    by_cases hi : i = outputProbeCleanupCounterIdx n
    · subst i
      exact outputProbeDispatch_hasBinaryNat_parked hlatch
    · rw [hother i hi]
      exact outputProbeDispatch_cleanWork_parked tm input output extras
        hextras i
  refine ⟨?_, ?_, ?_⟩
  · rw [hinputEq]
    exact outputProbeDispatch_cleanInput_parked tm input output extras
  · intro i
    rw [hworkEq]
    by_cases hi : placeWorkInMiddle 0 (outputProbeControllerTapes n) i
    · simp only [placeWorkCfg, hi, dite_true]
      exact hsourceWorkParked _
    · rw [placeWorkCfg_work_extra]
      exact houter i hi
      exact hi
  · rw [houtputEq]
    exact houtput

theorem outputProbeLatch_clear_hoareTimeSpace_internal
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
    (inputLength initialSpace : ℕ)
    (hinitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
        ({ state :=
              (clearWorkTM
                (outputProbeLatchIdx n controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).Q).WithinAuxSpace
            inputLength initialSpace) :
    (clearWorkTM
      (outputProbeLatchIdx n controllerTapes)).HoareTimeSpace
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true)
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (clearWorkTimeBound 1) inputLength
        (initialSpace + clearWorkTimeBound 1) := by
  have htime :
      (clearWorkTM
        (outputProbeLatchIdx n controllerTapes)).HoareTime
          (outputProbeLatchFramePost tm controllerTapes outerExtras input output
            extras true)
          (outputProbeLatchFramePost tm controllerTapes outerExtras input output
            extras false)
          (clearWorkTimeBound 1) := by
    intro inp work out hpost
    obtain ⟨hinpParked, hworkParked, houtParked⟩ :=
      outputProbeLatchFramePost_parked_internal tm controllerTapes
        outerExtras input output extras true hextras houter houtput inp work
        out hpost
    have hlatch := outputProbeLatchFramePost_latch tm controllerTapes
      outerExtras input output extras true inp work out hpost
    have htarget : work (outputProbeLatchIdx n controllerTapes) =
        (Tape.init ([true].map Γ.ofBool)).move Dir3.right := by
      simpa using hlatch.eq_init_move_right
    have hbase := clearWorkTM_hoareTime_frame
      (outputProbeLatchIdx n controllerTapes) [true] inp work out htarget
      hinpParked (fun i _ => hworkParked i) houtParked
    obtain ⟨done, elapsed, helapsed, hreach, hhalt, hdone⟩ :=
      hbase inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
    rcases hdone with ⟨hinputDone, hworkDone, houtputDone⟩
    rw [hinputDone, hworkDone, houtputDone]
    rcases hpost with ⟨sourceWork, hsource, hplaced⟩
    rcases hsource with ⟨hinputSource, hotherSource, _hlatchSource,
      houtputSource⟩
    let blank := (Tape.init []).move Dir3.right
    refine ⟨Function.update sourceWork (outputProbeCleanupCounterIdx n)
      blank, ?_, ?_⟩
    · refine ⟨hinputSource, ?_, ?_, houtputSource⟩
      · intro i hi
        simp only [Function.update_of_ne hi]
        exact hotherSource i hi
      · simpa [blank] using Tape.init_move_right_hasBinaryNat 0
    · rw [hplaced]
      simpa [outputProbeLatchIdx, blank] using
        placeWorkCfg_work_update (outputProbeLatchInnerTM tm) 0
          controllerTapes outerExtras
          { state := (outputProbeLatchInnerTM tm).qstart
            input := inp
            work := sourceWork
            output := out }
          (outputProbeCleanupCounterIdx n) blank
  exact htime.toHoareTimeSpace hinitial

theorem outputProbeLatchDispatchTM_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Bool →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {zeroTime oneTime inputLength zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post false) zeroTime inputLength zeroSpace)
    (hone : onOne.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras true)
      (post true) oneTime inputLength oneSpace) :
    (outputProbeLatchDispatchTM n controllerTapes onZero
      onOne).HoareTimeSpace
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        (post bit)
        (outputProbeLatchDispatchTime bit zeroTime oneTime)
        inputLength (if bit then oneSpace else zeroSpace) := by
  cases bit with
  | false =>
      have hbranch := branchWorkSymbolTM_hoareTimeSpace_different
        (outputProbeLatchIdx n controllerTapes) Γ.one onOne onZero
        (fun inp work out hpost => by
          have hlatch := outputProbeLatchFramePost_latch tm controllerTapes
            outerExtras input output extras false inp work out hpost
          rw [hlatch.eq_init_move_right]
          simp [Tape.read, Tape.move, Tape.init])
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras false hextras houter houtput inp
            work out hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras false hextras houter houtput inp
            work out hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras false hextras houter houtput inp
            work out hpost).2.2.read_ne_start)
        hzero
      simpa [outputProbeLatchDispatchTM, outputProbeLatchDispatchTime] using
        hbranch
  | true =>
      have hbranch := branchWorkSymbolTM_hoareTimeSpace_equal
        (outputProbeLatchIdx n controllerTapes) Γ.one onOne onZero
        (fun inp work out hpost => by
          have hlatch := outputProbeLatchFramePost_latch tm controllerTapes
            outerExtras input output extras true inp work out hpost
          rw [hlatch.eq_init_move_right]
          simp [Tape.read, Tape.move, Tape.init, Γ.ofBool])
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras true hextras houter houtput inp
            work out hpost).1.read_ne_start)
        (fun inp work out hpost i =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras true hextras houter houtput inp
            work out hpost).2.1 i |>.read_ne_start)
        (fun inp work out hpost =>
          (outputProbeLatchFramePost_parked_internal tm controllerTapes
            outerExtras input output extras true hextras houter houtput inp
            work out hpost).2.2.read_ne_start)
        hone
      simpa [outputProbeLatchDispatchTM, outputProbeLatchDispatchTime] using
        hbranch

theorem outputProbeLatchResetDispatchTM_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes))
    {post : Bool →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {zeroTime oneTime inputLength zeroSpace oneSpace clearInitialSpace : ℕ}
    (hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
        ({ state :=
              (clearWorkTM
                (outputProbeLatchIdx n controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).Q).WithinAuxSpace
            inputLength clearInitialSpace)
    (hzero : onZero.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post false) zeroTime inputLength zeroSpace)
    (hone : onOne.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post true) oneTime inputLength oneSpace) :
    (outputProbeLatchResetDispatchTM n controllerTapes onZero
      onOne).HoareTimeSpace
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        (post bit)
        (outputProbeLatchDispatchTime bit zeroTime
          (clearWorkTimeBound 1 + 1 + oneTime))
        inputLength
        (if bit then
          max (clearInitialSpace + clearWorkTimeBound 1) oneSpace
        else zeroSpace) := by
  have hclear := outputProbeLatch_clear_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    inputLength clearInitialSpace hclearInitial
  have htrue := seqTM_hoareTimeSpace
    (clearWorkTM (outputProbeLatchIdx n controllerTapes)) onOne hclear (by
      intro inp work out hpost
      obtain ⟨hinp, hwork, hout⟩ :=
        outputProbeLatchFramePost_parked_internal tm controllerTapes
          outerExtras input output extras false hextras houter houtput inp work
          out hpost
      have htransitionWork :
          (fun i => transitionTape (work i)) = work := by
        funext i
        exact (hwork i).transitionTape_eq_self
      rw [hinp.transitionInput_eq_self, htransitionWork,
        hout.transitionTape_eq_self]
      exact hpost) hone
  have hdispatch := outputProbeLatchDispatchTM_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras bit hextras houter houtput
    onZero
    (seqTM (clearWorkTM (outputProbeLatchIdx n controllerTapes)) onOne)
    hzero htrue
  simpa [outputProbeLatchResetDispatchTM] using hdispatch

theorem outputProbeIndexedDispatchTM_of_latch_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes))
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {post : Bool →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace zeroTime oneTime inputLength zeroSpace oneSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes sourceIdx
      scratchIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        latchTime inputLength latchSpace)
    (hzero : onZero.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post false) zeroTime inputLength zeroSpace)
    (hone : onOne.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras true)
      (post true) oneTime inputLength oneSpace) :
    (outputProbeIndexedDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).HoareTimeSpace pre (post bit)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit zeroTime oneTime)
        inputLength
        (max latchSpace (if bit then oneSpace else zeroSpace)) := by
  have hdispatch := outputProbeLatchDispatchTM_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras bit hextras houter houtput
    onZero onOne hzero hone
  have hseq := seqTM_hoareTimeSpace
    (outputProbeIndexedLatchTM tm controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchDispatchTM n controllerTapes onZero onOne) hlatch (by
      intro inp work out hpost
      obtain ⟨hinp, hwork, hout⟩ :=
        outputProbeLatchFramePost_parked_internal tm controllerTapes
          outerExtras input output extras bit hextras houter houtput inp work
          out hpost
      have htransitionWork :
          (fun i => transitionTape (work i)) = work := by
        funext i
        exact (hwork i).transitionTape_eq_self
      rw [hinp.transitionInput_eq_self, htransitionWork,
        hout.transitionTape_eq_self]
      exact hpost) hdispatch
  simpa [outputProbeIndexedDispatchTM] using hseq

theorem outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace_internal
    (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes))
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {post : Bool →
      TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace zeroTime oneTime inputLength zeroSpace oneSpace
      clearInitialSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes sourceIdx
      scratchIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit)
        latchTime inputLength latchSpace)
    (hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
        ({ state :=
              (clearWorkTM
                (outputProbeLatchIdx n controllerTapes)).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).Q).WithinAuxSpace
            inputLength clearInitialSpace)
    (hzero : onZero.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post false) zeroTime inputLength zeroSpace)
    (hone : onOne.HoareTimeSpace
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (post true) oneTime inputLength oneSpace) :
    (outputProbeIndexedResetDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).HoareTimeSpace pre (post bit)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit zeroTime
            (clearWorkTimeBound 1 + 1 + oneTime))
        inputLength
        (max latchSpace
          (if bit then
            max (clearInitialSpace + clearWorkTimeBound 1) oneSpace
          else zeroSpace)) := by
  have hdispatch := outputProbeLatchResetDispatchTM_hoareTimeSpace_internal tm
    controllerTapes outerExtras input output extras bit hextras houter houtput
    onZero onOne hclearInitial hzero hone
  have hseq := seqTM_hoareTimeSpace
    (outputProbeIndexedLatchTM tm controllerTapes sourceIdx scratchIdx)
    (outputProbeLatchResetDispatchTM n controllerTapes onZero onOne) hlatch (by
      intro inp work out hpost
      obtain ⟨hinp, hwork, hout⟩ :=
        outputProbeLatchFramePost_parked_internal tm controllerTapes
          outerExtras input output extras bit hextras houter houtput inp work
          out hpost
      have htransitionWork :
          (fun i => transitionTape (work i)) = work := by
        funext i
        exact (hwork i).transitionTape_eq_self
      rw [hinp.transitionInput_eq_self, htransitionWork,
        hout.transitionTape_eq_self]
      exact hpost) hdispatch
  simpa [outputProbeIndexedResetDispatchTM] using hseq

theorem IsTransducer.outputProbeLatchDispatchTM_internal
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeLatchDispatchTM n controllerTapes onZero onOne).IsTransducer := by
  unfold outputProbeLatchDispatchTM
  exact hone.branchWorkSymbolTM hzero

theorem IsTransducer.outputProbeIndexedDispatchTM_internal
    {tm : TM n} {controllerTapes : ℕ}
    {sourceIdx scratchIdx : Fin controllerTapes}
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeIndexedDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).IsTransducer := by
  unfold outputProbeIndexedDispatchTM
  exact (outputProbeIndexedLatchTM_isTransducer tm controllerTapes sourceIdx
    scratchIdx).seqTM
      (hzero.outputProbeLatchDispatchTM_internal hone)

theorem IsTransducer.outputProbeLatchResetDispatchTM_internal
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeLatchResetDispatchTM n controllerTapes onZero
      onOne).IsTransducer := by
  unfold outputProbeLatchResetDispatchTM
  exact hzero.outputProbeLatchDispatchTM_internal
    ((clearWorkTM_isTransducer
      (outputProbeLatchIdx n controllerTapes)).seqTM hone)

theorem IsTransducer.outputProbeIndexedResetDispatchTM_internal
    {tm : TM n} {controllerTapes : ℕ}
    {sourceIdx scratchIdx : Fin controllerTapes}
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeIndexedResetDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).IsTransducer := by
  unfold outputProbeIndexedResetDispatchTM
  exact (outputProbeIndexedLatchTM_isTransducer tm controllerTapes sourceIdx
    scratchIdx).seqTM
      (hzero.outputProbeLatchResetDispatchTM_internal hone)

end TM

end Complexity
