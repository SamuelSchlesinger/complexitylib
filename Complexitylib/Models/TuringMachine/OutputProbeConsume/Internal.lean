/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.OutputProbeConsume.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCleanup
import Complexitylib.Models.TuringMachine.OutputProbeFrame
import Complexitylib.Models.TuringMachine.Placement
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Restartable output-probe consumption -- proof internals
-/

namespace Complexity

namespace TM

@[simp] theorem outputProbeCaptureRewoundWork_capture_internal
    {n : ℕ} (work : Fin (outputProbeControllerTapes n) → Tape) :
    outputProbeCaptureRewoundWork work (outputProbeCleanupCaptureIdx n) =
      { head := 1,
        cells := (work (outputProbeCleanupCaptureIdx n)).cells } := by
  simp [outputProbeCaptureRewoundWork]

theorem outputProbeCaptureRewoundWork_ne_internal
    {n : ℕ} (work : Fin (outputProbeControllerTapes n) → Tape)
    (idx : Fin (outputProbeControllerTapes n))
    (hne : idx ≠ outputProbeCleanupCaptureIdx n) :
    outputProbeCaptureRewoundWork work idx = work idx := by
  simp [outputProbeCaptureRewoundWork, hne]

private theorem hasBinaryNat_parked {tape : Tape} {value : ℕ}
    (hvalue : tape.HasBinaryNat value) : Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

private theorem outputProbeCaptureRewoundWork_parked {n : ℕ}
    (work : Fin (outputProbeControllerTapes n) → Tape)
    (hwork : ∀ i, Parked (work i)) :
    ∀ i, Parked (outputProbeCaptureRewoundWork work i) := by
  intro i
  by_cases hi : i = outputProbeCleanupCaptureIdx n
  · subst i
    rw [outputProbeCaptureRewoundWork_capture_internal]
    exact ⟨le_rfl, (hwork (outputProbeCleanupCaptureIdx n)).2⟩
  · rw [outputProbeCaptureRewoundWork_ne_internal work i hi]
    exact hwork i

private theorem outputProbeCaptureRewoundWork_startInvariant {n : ℕ}
    (work : Fin (outputProbeControllerTapes n) → Tape)
    (hwork : ∀ i, (work i).StartInvariant) :
    ∀ i, (outputProbeCaptureRewoundWork work i).StartInvariant := by
  intro i
  by_cases hi : i = outputProbeCleanupCaptureIdx n
  · subst i
    rw [outputProbeCaptureRewoundWork_capture_internal]
    exact hwork (outputProbeCleanupCaptureIdx n)
  · rw [outputProbeCaptureRewoundWork_ne_internal work i hi]
    exact hwork i

private theorem outputProbeCaptureRewoundWork_blankAfter {n : ℕ}
    (work : Fin (outputProbeControllerTapes n) → Tape)
    (bound : ℕ) (hwork : ∀ i, (work i).BlankAfter bound) :
    ∀ i, (outputProbeCaptureRewoundWork work i).BlankAfter bound := by
  intro i index hindex
  by_cases hi : i = outputProbeCleanupCaptureIdx n
  · subst i
    simpa only [outputProbeCaptureRewoundWork_capture_internal] using
      hwork (outputProbeCleanupCaptureIdx n) index hindex
  · rw [outputProbeCaptureRewoundWork_ne_internal work i hi]
    exact hwork i index hindex

private theorem parked_rewoundInput (tape : Tape)
    (hinvariant : tape.StartInvariant) :
    Parked (outputProbeRewoundInput tape) := by
  exact ⟨le_rfl, hinvariant.2⟩

private theorem outputProbeCleanupTarget_middle {n : ℕ}
    (idx : Fin (outputProbeControllerTapes n))
    (hidx : idx ∈ outputProbeCleanupTargets n) :
    placeWorkInMiddle 0 (n + 2) idx := by
  rw [outputProbeCleanupTargets, List.mem_append] at hidx
  rcases hidx with hsource | htail
  · obtain ⟨source, rfl⟩ := List.mem_ofFn.mp hsource
    simp [placeWorkInMiddle, outputProbeCleanupSourceIdx]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
    rcases htail with rfl | rfl <;>
      simp [placeWorkInMiddle, outputProbeCleanupCountdownIdx,
        outputProbeCleanupCaptureIdx]

theorem outputProbeCleanupResult_eq_frame_internal
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (queryDone : Cfg (n + 2) ((outputProbeStartedTM tm).retargetOutput).Q)
    (hinvariant : ∀ i, i ∈ outputProbeCleanupTargets n →
      (outputProbeCaptureRewoundWork
        (placeWorkCfg ((outputProbeStartedTM tm).retargetOutput) 0 2
          extras queryDone).work i).StartInvariant)
    (hblank : ∀ i, i ∈ outputProbeCleanupTargets n →
      (outputProbeCaptureRewoundWork
        (placeWorkCfg ((outputProbeStartedTM tm).retargetOutput) 0 2
          extras queryDone).work i).BlankAfter limit) :
    rewindBlankWorkPrefixManyResult limit
        (outputProbeCaptureRewoundWork
          (placeWorkCfg ((outputProbeStartedTM tm).retargetOutput) 0 2
            extras queryDone).work)
        (outputProbeCleanupTargets n) =
      (outputProbePlacedFrameCfg tm input (outputProbeCounterTape 0)
        output extras).work := by
  let queryTM := (outputProbeStartedTM tm).retargetOutput
  let queriedWork :=
    (placeWorkCfg queryTM 0 2 extras queryDone).work
  let rewoundWork := outputProbeCaptureRewoundWork queriedWork
  funext idx
  by_cases htarget : idx ∈ outputProbeCleanupTargets n
  · rw [rewindBlankWorkPrefixManyResult_eq_parkedBlank_of_mem limit
      rewoundWork (outputProbeCleanupTargets n)
      (outputProbeCleanupTargets_nodup n) hinvariant hblank idx htarget]
    rw [outputProbeCleanupTargets, List.mem_append] at htarget
    rcases htarget with hsource | htail
    · obtain ⟨source, hidx⟩ := List.mem_ofFn.mp hsource
      subst idx
      let sourceIdx : Fin (n + 2) := ⟨source.val, by omega⟩
      have hphysical : outputProbeCleanupSourceIdx source =
          placeWorkIdx 0 2 sourceIdx := by
        apply Fin.ext
        simp [outputProbeCleanupSourceIdx, sourceIdx]
      rw [show (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape 0) output extras).work
          (outputProbeCleanupSourceIdx source) =
          (Tape.init []).move Dir3.right by
        rw [hphysical, outputProbePlacedFrameCfg,
          placeWorkCfg_work_middle]
        rw [retargetCfgFrame_work_lt _ _ _ sourceIdx (by
          dsimp only [sourceIdx]
          omega)]
        simp [outputProbeStartedCfg, sourceIdx]]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
      rcases htail with hcountdown | hcapture
      · subst idx
        let countdownIdx : Fin (n + 2) := ⟨n, by omega⟩
        have hphysical : outputProbeCleanupCountdownIdx n =
            placeWorkIdx 0 2 countdownIdx := by
          apply Fin.ext
          simp [outputProbeCleanupCountdownIdx, countdownIdx]
        rw [show (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape 0) output extras).work
            (outputProbeCleanupCountdownIdx n) =
            (Tape.init []).move Dir3.right by
          rw [hphysical, outputProbePlacedFrameCfg,
            placeWorkCfg_work_middle]
          rw [retargetCfgFrame_work_lt _ _ _ countdownIdx (by
            dsimp only [countdownIdx]
            omega)]
          simp [outputProbeStartedCfg, countdownIdx,
            outputProbeCounterTape]]
      · subst idx
        have hphysical : outputProbeCleanupCaptureIdx n =
            placeWorkIdx 0 2 (Fin.last (n + 1)) := by
          apply Fin.ext
          simp [outputProbeCleanupCaptureIdx]
        rw [show (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape 0) output extras).work
            (outputProbeCleanupCaptureIdx n) =
            (Tape.init []).move Dir3.right by
          rw [hphysical, outputProbePlacedFrameCfg,
            placeWorkCfg_work_middle]
          rw [retargetCfgFrame_work_last]
          simp [outputProbeStartedCfg]]
  · rw [rewindBlankWorkPrefixManyResult_eq_of_not_mem limit rewoundWork
      (outputProbeCleanupTargets n) idx htarget]
    by_cases hmiddle : placeWorkInMiddle 0 (n + 2) idx
    · have hcountdownIdx : idx = outputProbeCleanupCountdownIdx n := by
        have hnotSource : ¬idx.val < n := by
          intro hlt
          apply htarget
          rw [outputProbeCleanupTargets, List.mem_append]
          left
          apply List.mem_ofFn.mpr
          refine ⟨⟨idx.val, hlt⟩, ?_⟩
          apply Fin.ext
          simp [outputProbeCleanupSourceIdx]
        have hnotCapture : idx.val ≠ n + 1 := by
          intro heq
          apply htarget
          rw [outputProbeCleanupTargets, List.mem_append]
          right
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          right
          apply Fin.ext
          simp [outputProbeCleanupCaptureIdx, heq]
        apply Fin.ext
        simp only [outputProbeCleanupCountdownIdx]
        simp [placeWorkInMiddle] at hmiddle
        omega
      subst idx
      exact (htarget (outputProbeCleanupCountdownIdx_mem_internal n)).elim
    · have hrewound : rewoundWork idx = queriedWork idx := by
        apply outputProbeCaptureRewoundWork_ne_internal
        intro heq
        subst idx
        exact hmiddle (by
          simp [placeWorkInMiddle, outputProbeCleanupCaptureIdx])
      rw [hrewound]
      dsimp only [queriedWork]
      rw [placeWorkCfg_work_extra queryTM 0 2 extras queryDone idx hmiddle]
      rw [show (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape 0) output extras).work idx = extras idx by
        rw [outputProbePlacedFrameCfg]
        exact placeWorkCfg_work_extra
          ((outputProbeStartedTM tm).retargetOutput) 0 2 extras
          ((outputProbeStartedTM tm).retargetCfgFrame
            (outputProbeStartedCfg tm input (outputProbeCounterTape 0))
            output) idx hmiddle]

theorem ComputesInSpace.outputProbePlacedTM_hoareTimeSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (index : ℕ) (hindex : index < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace : ℕ)
    (hextra : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let querySpace := outputProbeConsumeQuerySpace
      (max 1 (space input.length)) index frameSpace
    ∃ probeSteps done,
      (outputProbePlacedTM tm).HoareTimeSpace
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output)
        (fun inp work out =>
          inp = (placeWorkCfg queryTM 0 2 extras done).input ∧
          work = (placeWorkCfg queryTM 0 2 extras done).work ∧
          out = output)
        probeSteps input.length querySpace ∧
      ((placeWorkCfg queryTM 0 2 extras done).work
        (outputProbeCleanupCaptureIdx n)).HasOutput
          [(f input)[index]'hindex] ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      done.output = output ∧
      (placeWorkCfg queryTM 0 2 extras done).input.cells =
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras).input.cells := by
  dsimp only
  let queryTM := (outputProbeStartedTM tm).retargetOutput
  let querySpace := outputProbeConsumeQuerySpace
    (max 1 (space input.length)) index frameSpace
  obtain ⟨probeSteps, done, hreach, hhalt, hcaptured, _hcountdown,
      hblank, houtputDone, hinputParked, hinputInvariant, hworkParked,
      hworkInvariant, hprefix⟩ :=
    hcomp.placeOutputProbeStartedRetargetTM_getElem_withinAuxSpace_frame
      0 2 input index hindex output houtput extras hextra hframe
  let placedDone := placeWorkCfg queryTM 0 2 extras done
  have hreach' : (outputProbePlacedTM tm).reachesIn probeSteps
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras) placedDone := by
    simpa [outputProbePlacedTM, outputProbePlacedFrameCfg, queryTM] using
      hreach
  have hhalt' : (outputProbePlacedTM tm).halted placedDone := by
    simpa [placedDone, outputProbePlacedTM, queryTM] using hhalt
  have hblankDone : ∀ i, (done.work i).BlankAfter
      (outputProbeCaptureSpace (max 1 (space input.length))
        (index + 1)) := by
    intro i
    simpa [placedDone] using hblank i
  have hquery : (outputProbePlacedTM tm).HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).work ∧
        out = output)
      (fun inp work out =>
        inp = placedDone.input ∧ work = placedDone.work ∧ out = output)
      probeSteps input.length querySpace := by
    constructor
    · rintro inp work out ⟨rfl, rfl, rfl⟩
      exact ⟨placedDone, probeSteps, le_rfl, hreach', hhalt', rfl, rfl,
        by simpa [placedDone] using houtputDone⟩
    · rintro inp work out ⟨rfl, rfl, rfl⟩ current hcurrent
      obtain ⟨elapsed, hcurrentRun⟩ :=
        (outputProbePlacedTM tm).reaches_to_reachesIn hcurrent
      have helapsed : elapsed ≤ probeSteps :=
        (outputProbePlacedTM tm).reachesIn_le_halt hcurrentRun hreach'
          hhalt'
      simpa [outputProbePlacedTM, outputProbePlacedFrameCfg, queryTM,
        querySpace, outputProbeConsumeQuerySpace] using
        hprefix elapsed current helapsed hcurrentRun
  refine ⟨probeSteps, done, ?_, ?_, hblankDone, hinputParked,
    hinputInvariant, hworkParked, hworkInvariant, ?_, ?_⟩
  · simpa only [placedDone] using hquery
  · have hphysical : outputProbeCleanupCaptureIdx n =
        placeWorkIdx 0 2 (Fin.last (n + 1)) := by
      apply Fin.ext
      simp [outputProbeCleanupCaptureIdx]
    rw [hphysical]
    exact hcaptured
  · simpa using houtputDone
  · exact input_cells_eq_of_reachesIn hreach'

theorem
    ComputesInSpace.outputProbePlacedTM_index_halts_hoareTimeSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (index : ℕ)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace : ℕ)
    (hextra : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).read ≠ Γ.start)
    (hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace) :
    let queryTM := (outputProbeStartedTM tm).retargetOutput
    let querySpace := outputProbeConsumeQuerySpace
      (max 1 (space input.length)) index frameSpace
    ∃ probeSteps done bit,
      (outputProbePlacedTM tm).HoareTimeSpace
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output)
        (fun inp work out =>
          inp = (placeWorkCfg queryTM 0 2 extras done).input ∧
          work = (placeWorkCfg queryTM 0 2 extras done).work ∧
          out = output)
        probeSteps input.length querySpace ∧
      ((placeWorkCfg queryTM 0 2 extras done).work
        (outputProbeCleanupCaptureIdx n)).HasOutput [bit] ∧
      (∀ i, (done.work i).BlankAfter
        (outputProbeCaptureSpace (max 1 (space input.length))
          (index + 1))) ∧
      Parked done.input ∧
      done.input.StartInvariant ∧
      (∀ i, Parked (done.work i)) ∧
      (∀ i, (done.work i).StartInvariant) ∧
      done.output = output ∧
      (placeWorkCfg queryTM 0 2 extras done).input.cells =
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape (index + 1)) output extras).input.cells := by
  dsimp only
  let queryTM := (outputProbeStartedTM tm).retargetOutput
  let querySpace := outputProbeConsumeQuerySpace
    (max 1 (space input.length)) index frameSpace
  obtain ⟨probeSteps, done, hreach, hhalt, hcaptured, hblank,
      houtputDone, hinputParked, hinputInvariant, hworkParked,
      hworkInvariant, hprefix⟩ :=
    hcomp.placeOutputProbeStartedRetargetTM_index_halts_withinAuxSpace_frame
      0 2 input index output houtput extras hextra hframe
  obtain ⟨bit, hbit⟩ := hcaptured
  let placedDone := placeWorkCfg queryTM 0 2 extras done
  have hreach' : (outputProbePlacedTM tm).reachesIn probeSteps
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras) placedDone := by
    simpa [outputProbePlacedTM, outputProbePlacedFrameCfg, queryTM] using
      hreach
  have hhalt' : (outputProbePlacedTM tm).halted placedDone := by
    simpa [placedDone, outputProbePlacedTM, queryTM] using hhalt
  have hblankDone : ∀ i, (done.work i).BlankAfter
      (outputProbeCaptureSpace (max 1 (space input.length))
        (index + 1)) := by
    intro i
    simpa [placedDone] using hblank i
  have hquery : (outputProbePlacedTM tm).HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).work ∧
        out = output)
      (fun inp work out =>
        inp = placedDone.input ∧ work = placedDone.work ∧ out = output)
      probeSteps input.length querySpace := by
    constructor
    · rintro inp work out ⟨rfl, rfl, rfl⟩
      exact ⟨placedDone, probeSteps, le_rfl, hreach', hhalt', rfl, rfl,
        by simpa [placedDone] using houtputDone⟩
    · rintro inp work out ⟨rfl, rfl, rfl⟩ current hcurrent
      obtain ⟨elapsed, hcurrentRun⟩ :=
        (outputProbePlacedTM tm).reaches_to_reachesIn hcurrent
      have helapsed : elapsed ≤ probeSteps :=
        (outputProbePlacedTM tm).reachesIn_le_halt hcurrentRun hreach'
          hhalt'
      simpa [outputProbePlacedTM, outputProbePlacedFrameCfg, queryTM,
        querySpace, outputProbeConsumeQuerySpace] using
        hprefix elapsed current helapsed hcurrentRun
  refine ⟨probeSteps, done, bit, ?_, ?_, hblankDone, hinputParked,
    hinputInvariant, hworkParked, hworkInvariant, ?_, ?_⟩
  · simpa only [placedDone] using hquery
  · have hphysical : outputProbeCleanupCaptureIdx n =
        placeWorkIdx 0 2 (Fin.last (n + 1)) := by
      apply Fin.ext
      simp [outputProbeCleanupCaptureIdx]
    rw [hphysical]
    exact hbit
  · simpa using houtputDone
  · exact input_cells_eq_of_reachesIn hreach'

theorem ComputesInSpace.outputProbeConsumeTM_hoareTimeSpace_bit_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (_hcomp : tm.ComputesInSpace f space)
    (onZero onOne : TM (outputProbeControllerTapes n))
    (input : List Bool) (index : ℕ) (bit : Bool)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace limit : ℕ)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (_hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace)
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat limit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (index + 1) ≤ limit)
    (hqueryResult :
      let queryTM := (outputProbeStartedTM tm).retargetOutput
      let querySpace := outputProbeConsumeQuerySpace
        (max 1 (space input.length)) index frameSpace
      ∃ probeSteps done,
        (outputProbePlacedTM tm).HoareTimeSpace
          (fun inp work out =>
            inp = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).input ∧
            work = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).work ∧
            out = output)
          (fun inp work out =>
            inp = (placeWorkCfg queryTM 0 2 extras done).input ∧
            work = (placeWorkCfg queryTM 0 2 extras done).work ∧
            out = output)
          probeSteps input.length querySpace ∧
        ((placeWorkCfg queryTM 0 2 extras done).work
          (outputProbeCleanupCaptureIdx n)).HasOutput [bit] ∧
        (∀ i, (done.work i).BlankAfter
          (outputProbeCaptureSpace (max 1 (space input.length))
            (index + 1))) ∧
        Parked done.input ∧
        done.input.StartInvariant ∧
        (∀ i, Parked (done.work i)) ∧
        (∀ i, (done.work i).StartInvariant) ∧
        done.output = output ∧
        (placeWorkCfg queryTM 0 2 extras done).input.cells =
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).input.cells)
    {post : Bool → TapePred (outputProbeControllerTapes n)}
    {zeroTime oneTime zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post false) zeroTime input.length zeroSpace)
    (hone : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post true) oneTime input.length oneSpace) :
    ∃ consumeTime,
      (outputProbeConsumeTM tm onZero onOne).HoareTimeSpace
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output)
        (post bit) consumeTime input.length
          (outputProbeConsumeSpace n (max 1 (space input.length)) index
            frameSpace limit
            (if bit then oneSpace else zeroSpace)) := by
  let sourceSpace := max 1 (space input.length)
  let budget := outputProbeCaptureSpace sourceSpace (index + 1)
  let querySpace := outputProbeConsumeQuerySpace sourceSpace index frameSpace
  let rewindSpace := outputProbeConsumeRewindSpace sourceSpace index frameSpace
  let cleanupSpace := outputProbeConsumeCleanupSpace n sourceSpace index
    frameSpace limit
  let continuationSpace := if bit then oneSpace else zeroSpace
  let queryTM := (outputProbeStartedTM tm).retargetOutput
  have hextraRead : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).read ≠ Γ.start := by
    intro i hi
    exact (hextras i hi).read_ne_start
  dsimp only at hqueryResult
  obtain ⟨probeSteps, done, hquery, hcaptured, hblank,
      hinputParked, hinputInvariant, hworkParked, hworkInvariant,
      hdoneOutput, hinputCells⟩ :=
    hqueryResult
  let placedDone := placeWorkCfg queryTM 0 2 extras done
  let readyWork := outputProbeCaptureRewoundWork placedDone.work
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  have hquerySpaceOne : 1 ≤ querySpace := by
    dsimp only [querySpace, outputProbeConsumeQuerySpace, budget,
      sourceSpace, outputProbeCaptureSpace, outputProbeReplaySpace,
      outputProbePositiveSpace, binaryPredSpace]
    omega
  have hplacedInputParked : Parked placedDone.input := by
    simpa only [placedDone, placeWorkCfg_input] using hinputParked
  have hplacedInputInvariant : placedDone.input.StartInvariant := by
    simpa only [placedDone, placeWorkCfg_input] using hinputInvariant
  have hplacedOutput : placedDone.output = output := by
    simpa [placedDone] using hdoneOutput
  have hplacedWorkParked : ∀ i, Parked (placedDone.work i) := by
    intro i
    dsimp only [placedDone]
    by_cases hi : placeWorkInMiddle 0 (n + 2) i
    · rw [placeWorkCfg]
      simp only [hi, dite_true]
      exact hworkParked (placeWorkCoord 0 (n + 2) i hi)
    · rw [placeWorkCfg_work_extra queryTM 0 2 extras done i hi]
      exact hextras i hi
  have hplacedDoneSpace : placedDone.WithinAuxSpace input.length
      querySpace := by
    obtain ⟨queryEnd, querySteps, _hquerySteps, hqueryRun, _hqueryHalt,
        hqueryEnd⟩ := hquery.1
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras).input
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras).work
      output ⟨rfl, rfl, rfl⟩
    have hqueryEndSpace := hquery.2
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras).input
      (outputProbePlacedFrameCfg tm input
        (outputProbeCounterTape (index + 1)) output extras).work
      output ⟨rfl, rfl, rfl⟩ queryEnd (reaches_of_reachesIn hqueryRun)
    obtain ⟨hqueryInput, hqueryWork, _hqueryOutput⟩ := hqueryEnd
    constructor
    · intro i
      dsimp only [placedDone]
      rw [← hqueryWork]
      exact hqueryEndSpace.1 i
    · dsimp only [placedDone]
      rw [← hqueryInput]
      exact hqueryEndSpace.2
  have hcapturePhysical : outputProbeCleanupCaptureIdx n =
      placeWorkIdx 0 2 (Fin.last (n + 1)) := by
    apply Fin.ext
    simp [outputProbeCleanupCaptureIdx]
  have hplacedCaptureInvariant :
      (placedDone.work (outputProbeCleanupCaptureIdx n)).StartInvariant := by
    rw [hcapturePhysical]
    dsimp only [placedDone]
    rw [placeWorkCfg_work_middle]
    exact hworkInvariant (Fin.last (n + 1))
  have hrewindBase := rewindWorkTM_hoareTime_frame
    (outputProbeCleanupCaptureIdx n) querySpace
    (P := fun inp work out =>
      inp = placedDone.input ∧
      (work (outputProbeCleanupCaptureIdx n)).cells =
        (placedDone.work (outputProbeCleanupCaptureIdx n)).cells ∧
      (∀ i, i ≠ outputProbeCleanupCaptureIdx n →
        work i = placedDone.work i) ∧
      out = output)
    (by
      rintro inp work out inp' work' out'
        ⟨hinputEq, htargetEq, hotherEq, houtputEq⟩
        htargetCells _htargetHead hother hinput' houtputCells houtputHead
      refine ⟨hinput'.trans hinputEq, htargetCells.trans htargetEq, ?_, ?_⟩
      · intro i hi
        exact (hother i hi).trans (hotherEq i hi)
      · apply Tape.ext
        · exact houtputHead.trans (congrArg Tape.head houtputEq)
        · exact houtputCells.trans (congrArg Tape.cells houtputEq))
  have hrewindTime :
      (rewindWorkTM (outputProbeCleanupCaptureIdx n)).HoareTime
        (fun inp work out =>
          inp = placedDone.input ∧ work = placedDone.work ∧ out = output)
        (fun inp work out =>
          inp = placedDone.input ∧ work = readyWork ∧ out = output)
        (querySpace + 2) := by
    apply hrewindBase.consequence
    · rintro inp work out ⟨rfl, rfl, rfl⟩
      refine ⟨hplacedCaptureInvariant.1,
        hplacedCaptureInvariant.2, hplacedDoneSpace.1 _,
        hplacedInputParked.read_ne_start, houtput.read_ne_start, houtput.1,
        ?_, rfl, rfl, (fun _ _ => rfl), rfl⟩
      intro i hi
      exact ⟨(hplacedWorkParked i).read_ne_start,
        (hplacedWorkParked i).1⟩
    · rintro inp work out ⟨htargetHead, hinputEq, htargetCells,
        hotherEq, houtputEq⟩
      refine ⟨hinputEq, ?_, houtputEq⟩
      funext i
      by_cases hi : i = outputProbeCleanupCaptureIdx n
      · subst i
        dsimp only [readyWork]
        rw [outputProbeCaptureRewoundWork_capture_internal]
        apply Tape.ext
        · exact htargetHead
        · exact htargetCells
      · dsimp only [readyWork]
        rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work i hi]
        exact hotherEq i hi
    · exact le_rfl
  have hrewind :
      (rewindWorkTM (outputProbeCleanupCaptureIdx n)).HoareTimeSpace
        (fun inp work out =>
          inp = placedDone.input ∧ work = placedDone.work ∧ out = output)
        (fun inp work out =>
          inp = placedDone.input ∧ work = readyWork ∧ out = output)
        (querySpace + 2) input.length rewindSpace := by
    have hrewind' := hrewindTime.toHoareTimeSpace (inputLength := input.length)
      (initialSpace := querySpace) (by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact hplacedDoneSpace)
    simpa [rewindSpace, outputProbeConsumeRewindSpace] using hrewind'
  have hqueryLeRewind : querySpace ≤ rewindSpace := by
    dsimp only [rewindSpace, outputProbeConsumeRewindSpace]
    omega
  have hreadyWorkParked : ∀ i, Parked (readyWork i) := by
    exact outputProbeCaptureRewoundWork_parked placedDone.work
      hplacedWorkParked
  have hplacedTargetInvariant : ∀ i, i ∈ outputProbeCleanupTargets n →
      (placedDone.work i).StartInvariant := by
    intro i hi
    have hmiddle := outputProbeCleanupTarget_middle i hi
    simp only [placedDone, placeWorkCfg, hmiddle, dite_true]
    exact hworkInvariant (placeWorkCoord 0 (n + 2) i hmiddle)
  have hplacedTargetBlank : ∀ i, i ∈ outputProbeCleanupTargets n →
      (placedDone.work i).BlankAfter budget := by
    intro i hi
    have hmiddle := outputProbeCleanupTarget_middle i hi
    simp only [placedDone, placeWorkCfg, hmiddle, dite_true]
    simpa only [budget, sourceSpace] using
      hblank (placeWorkCoord 0 (n + 2) i hmiddle)
  have hreadyTargetInvariant : ∀ i, i ∈ outputProbeCleanupTargets n →
      (readyWork i).StartInvariant := by
    intro i hi
    by_cases hicapture : i = outputProbeCleanupCaptureIdx n
    · subst i
      dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_capture_internal]
      exact hplacedTargetInvariant _ hi
    · dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work i
        hicapture]
      exact hplacedTargetInvariant i hi
  have hreadyTargetBlank : ∀ i, i ∈ outputProbeCleanupTargets n →
      (readyWork i).BlankAfter limit := by
    intro i hi cell hcell
    have hblankBudget : (readyWork i).BlankAfter budget := by
      by_cases hicapture : i = outputProbeCleanupCaptureIdx n
      · subst i
        dsimp only [readyWork]
        rw [outputProbeCaptureRewoundWork_capture_internal]
        exact hplacedTargetBlank _ hi
      · dsimp only [readyWork]
        rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work i
          hicapture]
        exact hplacedTargetBlank i hi
    exact hblankBudget cell (lt_of_le_of_lt (by
      simpa only [budget, sourceSpace] using hlimit) hcell)
  have hcounterExtra : ¬placeWorkInMiddle 0 (n + 2)
      (outputProbeCleanupCounterIdx n) := by
    simp [placeWorkInMiddle, outputProbeCleanupCounterIdx]
  have hlimitExtra : ¬placeWorkInMiddle 0 (n + 2)
      (outputProbeCleanupLimitIdx n) := by
    simp [placeWorkInMiddle, outputProbeCleanupLimitIdx]
  have hcounterCapture : outputProbeCleanupCounterIdx n ≠
      outputProbeCleanupCaptureIdx n := by
    intro heq
    apply congrArg Fin.val at heq
    simp [outputProbeCleanupCounterIdx, outputProbeCleanupCaptureIdx] at heq
  have hlimitCapture : outputProbeCleanupLimitIdx n ≠
      outputProbeCleanupCaptureIdx n := by
    intro heq
    apply congrArg Fin.val at heq
    simp [outputProbeCleanupLimitIdx, outputProbeCleanupCaptureIdx] at heq
  have hreadyCounter :
      (readyWork (outputProbeCleanupCounterIdx n)).HasBinaryNat 0 := by
    dsimp only [readyWork]
    rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work _
      hcounterCapture]
    dsimp only [placedDone]
    rw [placeWorkCfg_work_extra queryTM 0 2 extras done _ hcounterExtra]
    exact hcleanupCounter
  have hreadyLimit :
      (readyWork (outputProbeCleanupLimitIdx n)).HasBinaryNat limit := by
    dsimp only [readyWork]
    rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work _
      hlimitCapture]
    dsimp only [placedDone]
    rw [placeWorkCfg_work_extra queryTM 0 2 extras done _ hlimitExtra]
    exact hcleanupLimit
  have hreadyWorkSpace : ∀ i, (readyWork i).head ≤ rewindSpace := by
    intro i
    by_cases hicapture : i = outputProbeCleanupCaptureIdx n
    · subst i
      dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_capture_internal]
      exact le_trans hquerySpaceOne hqueryLeRewind
    · dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work i
        hicapture]
      exact (hplacedDoneSpace.1 i).trans hqueryLeRewind
  have hreadyTargetHead : ∀ i, i ∈ outputProbeCleanupTargets n →
      (readyWork i).head ≤ querySpace := by
    intro i _hi
    by_cases hicapture : i = outputProbeCleanupCaptureIdx n
    · subst i
      dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_capture_internal]
      exact hquerySpaceOne
    · dsimp only [readyWork]
      rw [outputProbeCaptureRewoundWork_ne_internal placedDone.work i
        hicapture]
      exact hplacedDoneSpace.1 i
  have hcleanInput : outputProbeRewoundInput placedDone.input =
      cleanCfg.input := by
    apply Tape.ext
    · simp [outputProbeRewoundInput, cleanCfg, outputProbePlacedFrameCfg,
        outputProbeStartedCfg, Tape.move]
    · simp only [outputProbeRewoundInput]
      have hcells : placedDone.input.cells =
          (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape (index + 1)) output extras).input.cells := by
        simpa [placedDone, queryTM] using hinputCells
      simpa [cleanCfg, outputProbePlacedFrameCfg, outputProbeStartedCfg] using
        hcells
  have hcleanWork : rewindBlankWorkPrefixManyResult limit readyWork
      (outputProbeCleanupTargets n) = cleanCfg.work := by
    have hresult := outputProbeCleanupResult_eq_frame_internal tm input
      output extras done hreadyTargetInvariant hreadyTargetBlank
    simpa [readyWork, placedDone, queryTM, cleanCfg] using hresult
  have hcleanupRaw := outputProbeCleanupTM_hoareTimeSpace_frame n
    (input.length + querySpace + 1) limit input.length rewindSpace
    (fun _ => querySpace) placedDone.input readyWork output
    hplacedInputInvariant hplacedInputParked hplacedDoneSpace.2
    hreadyWorkParked hreadyTargetInvariant hreadyTargetHead hreadyCounter
    hreadyLimit houtput hreadyWorkSpace
    (hplacedDoneSpace.2.trans (by omega))
  have hcleanup : (outputProbeCleanupTM n).HoareTimeSpace
      (fun inp work out =>
        inp = placedDone.input ∧ work = readyWork ∧ out = output)
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (outputProbeCleanupTime n (input.length + querySpace + 1) limit
        (fun _ => querySpace)) input.length cleanupSpace := by
    apply hcleanupRaw.consequence
    · intro inp work out hpre
      exact hpre
    · rintro inp work out ⟨hinputEq, hworkEq, houtputEq⟩
      exact ⟨hinputEq.trans hcleanInput, hworkEq.trans hcleanWork,
        houtputEq⟩
    · exact le_rfl
    · exact le_rfl
    · simp [cleanupSpace, rewindSpace, querySpace,
        outputProbeConsumeCleanupSpace]
  have hcleanInputParked : Parked cleanCfg.input := by
    rw [← hcleanInput]
    exact parked_rewoundInput placedDone.input hplacedInputInvariant
  have hcleanWorkParked : ∀ i, Parked (cleanCfg.work i) := by
    rw [← hcleanWork]
    exact rewindBlankWorkPrefixManyResult_parked limit readyWork
      (outputProbeCleanupTargets n) hreadyWorkParked
  have hcleanupTransition : ∀ inp work out,
      (inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output) →
      transitionInput inp = cleanCfg.input ∧
        (fun i => transitionTape (work i)) = cleanCfg.work ∧
        transitionTape out = output := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hcleanInputParked.transitionInput_eq_self,
      funext fun i => (hcleanWorkParked i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have hzeroClean : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (post false) zeroTime input.length zeroSpace := by
    simpa only [cleanCfg] using hzero
  have honeClean : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (post true) oneTime input.length oneSpace := by
    simpa only [cleanCfg] using hone
  have hcleanupZero := seqTM_hoareTimeSpace (outputProbeCleanupTM n)
    onZero hcleanup hcleanupTransition hzeroClean
  have hcleanupOne := seqTM_hoareTimeSpace (outputProbeCleanupTM n)
    onOne hcleanup hcleanupTransition honeClean
  have hreadyRead :
      (readyWork (outputProbeCleanupCaptureIdx n)).read = Γ.ofBool bit := by
    have hcell := hcaptured.1 0 (by simp)
    dsimp only [readyWork]
    rw [outputProbeCaptureRewoundWork_capture_internal]
    simpa [Tape.read] using hcell
  have hreadyTransition : ∀ inp work out,
      (inp = placedDone.input ∧ work = readyWork ∧ out = output) →
      transitionInput inp = placedDone.input ∧
        (fun i => transitionTape (work i)) = readyWork ∧
        transitionTape out = output := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hplacedInputParked.transitionInput_eq_self,
      funext fun i => (hreadyWorkParked i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have hqueryTransition : ∀ inp work out,
      (inp = placedDone.input ∧ work = placedDone.work ∧
        out = output) →
      transitionInput inp = placedDone.input ∧
        (fun i => transitionTape (work i)) = placedDone.work ∧
        transitionTape out = output := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨hplacedInputParked.transitionInput_eq_self,
      funext fun i => (hplacedWorkParked i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  cases hbit : bit with
  | false =>
      have hdifferent : ∀ inp work out,
          (inp = placedDone.input ∧ work = readyWork ∧ out = output) →
          (work (outputProbeCleanupCaptureIdx n)).read ≠ Γ.one := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        rw [hbit] at hreadyRead
        intro heq
        rw [heq] at hreadyRead
        simp [Γ.ofBool] at hreadyRead
      have hbranch := branchWorkSymbolTM_hoareTimeSpace_different
        (outputProbeCleanupCaptureIdx n) Γ.one
        (seqTM (outputProbeCleanupTM n) onOne)
        (seqTM (outputProbeCleanupTM n) onZero)
        hdifferent
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact hplacedInputParked.read_ne_start)
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩ i
          exact (hreadyWorkParked i).read_ne_start)
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact houtput.read_ne_start)
        hcleanupZero
      have htail := seqTM_hoareTimeSpace
        (rewindWorkTM (outputProbeCleanupCaptureIdx n))
        (branchWorkSymbolTM (outputProbeCleanupCaptureIdx n) Γ.one
          (seqTM (outputProbeCleanupTM n) onOne)
          (seqTM (outputProbeCleanupTM n) onZero))
        hrewind hreadyTransition hbranch
      have hall := seqTM_hoareTimeSpace (outputProbePlacedTM tm)
        (seqTM (rewindWorkTM (outputProbeCleanupCaptureIdx n))
          (branchWorkSymbolTM (outputProbeCleanupCaptureIdx n) Γ.one
            (seqTM (outputProbeCleanupTM n) onOne)
            (seqTM (outputProbeCleanupTM n) onZero)))
        hquery hqueryTransition htail
      refine ⟨probeSteps + 1 + (querySpace + 2 + 1 +
        (outputProbeCleanupTime n (input.length + querySpace + 1) limit
          (fun _ => querySpace) + 1 + zeroTime + 1)), ?_⟩
      simpa [outputProbeConsumeTM, outputProbeConsumeSpace, hbit,
        querySpace, rewindSpace, cleanupSpace, continuationSpace] using hall
  | true =>
      have hequal : ∀ inp work out,
          (inp = placedDone.input ∧ work = readyWork ∧ out = output) →
          (work (outputProbeCleanupCaptureIdx n)).read = Γ.one := by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        rw [hbit] at hreadyRead
        simpa using hreadyRead
      have hbranch := branchWorkSymbolTM_hoareTimeSpace_equal
        (outputProbeCleanupCaptureIdx n) Γ.one
        (seqTM (outputProbeCleanupTM n) onOne)
        (seqTM (outputProbeCleanupTM n) onZero)
        hequal
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact hplacedInputParked.read_ne_start)
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩ i
          exact (hreadyWorkParked i).read_ne_start)
        (by
          rintro inp work out ⟨rfl, rfl, rfl⟩
          exact houtput.read_ne_start)
        hcleanupOne
      have htail := seqTM_hoareTimeSpace
        (rewindWorkTM (outputProbeCleanupCaptureIdx n))
        (branchWorkSymbolTM (outputProbeCleanupCaptureIdx n) Γ.one
          (seqTM (outputProbeCleanupTM n) onOne)
          (seqTM (outputProbeCleanupTM n) onZero))
        hrewind hreadyTransition hbranch
      have hall := seqTM_hoareTimeSpace (outputProbePlacedTM tm)
        (seqTM (rewindWorkTM (outputProbeCleanupCaptureIdx n))
          (branchWorkSymbolTM (outputProbeCleanupCaptureIdx n) Γ.one
            (seqTM (outputProbeCleanupTM n) onOne)
            (seqTM (outputProbeCleanupTM n) onZero)))
        hquery hqueryTransition htail
      refine ⟨probeSteps + 1 + (querySpace + 2 + 1 +
        (outputProbeCleanupTime n (input.length + querySpace + 1) limit
          (fun _ => querySpace) + 1 + oneTime + 1)), ?_⟩
      simpa [outputProbeConsumeTM, outputProbeConsumeSpace, hbit,
        querySpace, rewindSpace, cleanupSpace, continuationSpace] using hall

theorem ComputesInSpace.outputProbeConsumeTM_hoareTimeSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (onZero onOne : TM (outputProbeControllerTapes n))
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
    {post : Bool → TapePred (outputProbeControllerTapes n)}
    {zeroTime oneTime zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post false) zeroTime input.length zeroSpace)
    (hone : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post true) oneTime input.length oneSpace) :
    ∃ consumeTime,
      (outputProbeConsumeTM tm onZero onOne).HoareTimeSpace
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output)
        (post ((f input)[index]'hindex)) consumeTime input.length
          (outputProbeConsumeSpace n (max 1 (space input.length)) index
            frameSpace limit
            (if (f input)[index]'hindex then oneSpace else zeroSpace)) := by
  have hextraRead : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).read ≠ Γ.start := by
    intro i hi
    exact (hextras i hi).read_ne_start
  have hqueryResult :=
    hcomp.outputProbePlacedTM_hoareTimeSpace_frame_internal input index
      hindex output houtput extras frameSpace hextraRead hframe
  exact hcomp.outputProbeConsumeTM_hoareTimeSpace_bit_internal onZero onOne
    input index ((f input)[index]'hindex) output houtput extras frameSpace
    limit hextras hframe hcleanupCounter hcleanupLimit hlimit hqueryResult
    hzero hone

theorem
    ComputesInSpace.outputProbeConsumeTM_index_halts_hoareTimeSpace_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (onZero onOne : TM (outputProbeControllerTapes n))
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
    {post : Bool → TapePred (outputProbeControllerTapes n)}
    {zeroTime oneTime zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post false) zeroTime input.length zeroSpace)
    (hone : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post true) oneTime input.length oneSpace) :
    ∃ bit consumeTime,
      (outputProbeConsumeTM tm onZero onOne).HoareTimeSpace
        (fun inp work out =>
          inp = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).input ∧
          work = (outputProbePlacedFrameCfg tm input
              (outputProbeCounterTape (index + 1)) output extras).work ∧
          out = output)
        (post bit) consumeTime input.length
          (outputProbeConsumeSpace n (max 1 (space input.length)) index
            frameSpace limit (if bit then oneSpace else zeroSpace)) := by
  have hextraRead : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).read ≠ Γ.start := by
    intro i hi
    exact (hextras i hi).read_ne_start
  obtain ⟨probeSteps, done, bit, hquery⟩ :=
    hcomp.outputProbePlacedTM_index_halts_hoareTimeSpace_frame_internal
      input index output houtput extras frameSpace hextraRead hframe
  obtain ⟨consumeTime, hconsume⟩ :=
    hcomp.outputProbeConsumeTM_hoareTimeSpace_bit_internal onZero onOne
      input index bit output houtput extras frameSpace limit hextras hframe
      hcleanupCounter hcleanupLimit hlimit ⟨probeSteps, done, hquery⟩ hzero hone
  exact ⟨bit, consumeTime, hconsume⟩

theorem
    ComputesInSpace.outputProbeConsumeTM_index_halts_hoareTimeSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (onZero onOne : TM (outputProbeControllerTapes n))
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
    {post : Bool → TapePred (outputProbeControllerTapes n)}
    {zeroTime oneTime zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post false) zeroTime input.length zeroSpace)
    (hone : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post true) oneTime input.length oneSpace)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (outerFrameSpace : ℕ)
    (houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start)
    (houterFrame : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace) :
    ∃ bit consumeTime,
      (placeWorkTM 0 controllerTapes
        (outputProbeConsumeTM tm onZero onOne)).HoareTimeSpace
        (placeWorkPred (outputProbeConsumeTM tm onZero onOne) 0
          controllerTapes outerExtras
          (fun inp work out =>
            inp = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).input ∧
            work = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).work ∧
            out = output))
        (placeWorkPred (outputProbeConsumeTM tm onZero onOne) 0
          controllerTapes outerExtras (post bit))
        consumeTime input.length
          (max
            (outputProbeConsumeSpace n (max 1 (space input.length)) index
              frameSpace limit (if bit then oneSpace else zeroSpace))
            outerFrameSpace) := by
  obtain ⟨bit, consumeTime, hconsume⟩ :=
    hcomp.outputProbeConsumeTM_index_halts_hoareTimeSpace_internal
      onZero onOne input index output houtput extras frameSpace limit hextras
      hframe hcleanupCounter hcleanupLimit hlimit hzero hone
  refine ⟨bit, consumeTime, ?_⟩
  exact placeWorkTM_hoareTimeSpace_frame_internal
    (outputProbeConsumeTM tm onZero onOne) 0 controllerTapes outerExtras
    hconsume houterRead houterFrame

theorem ComputesInSpace.outputProbeConsumeTM_hoareTimeSpace_frame_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (onZero onOne : TM (outputProbeControllerTapes n))
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
    {post : Bool → TapePred (outputProbeControllerTapes n)}
    {zeroTime oneTime zeroSpace oneSpace : ℕ}
    (hzero : onZero.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post false) zeroTime input.length zeroSpace)
    (hone : onOne.HoareTimeSpace
      (fun inp work out =>
        inp = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).input ∧
        work = (outputProbePlacedFrameCfg tm input
            (outputProbeCounterTape 0) output extras).work ∧
        out = output)
      (post true) oneTime input.length oneSpace)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (outerFrameSpace : ℕ)
    (houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start)
    (houterFrame : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace) :
    ∃ consumeTime,
      (placeWorkTM 0 controllerTapes
        (outputProbeConsumeTM tm onZero onOne)).HoareTimeSpace
        (placeWorkPred (outputProbeConsumeTM tm onZero onOne) 0
          controllerTapes outerExtras
          (fun inp work out =>
            inp = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).input ∧
            work = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).work ∧
            out = output))
        (placeWorkPred (outputProbeConsumeTM tm onZero onOne) 0
          controllerTapes outerExtras (post ((f input)[index]'hindex)))
        consumeTime input.length
          (max
            (outputProbeConsumeSpace n (max 1 (space input.length)) index
              frameSpace limit
              (if (f input)[index]'hindex then oneSpace else zeroSpace))
            outerFrameSpace) := by
  obtain ⟨consumeTime, hconsume⟩ :=
    hcomp.outputProbeConsumeTM_hoareTimeSpace_internal onZero onOne input
      index hindex output houtput extras frameSpace limit hextras hframe
      hcleanupCounter hcleanupLimit hlimit hzero hone
  refine ⟨consumeTime, ?_⟩
  exact placeWorkTM_hoareTimeSpace_frame_internal
    (outputProbeConsumeTM tm onZero onOne) 0 controllerTapes outerExtras
    hconsume houterRead houterFrame

theorem outputProbePlacedTM_isTransducer_internal (tm : TM n) :
    (outputProbePlacedTM tm).IsTransducer := by
  exact ((outputProbeStartedTM tm).retargetOutput_isTransducer).placeWorkTM 0 2

theorem IsTransducer.outputProbeConsumeTM_internal
    {tm : TM n}
    {onZero onOne : TM (outputProbeControllerTapes n)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeConsumeTM tm onZero onOne).IsTransducer := by
  unfold outputProbeConsumeTM
  apply IsTransducer.seqTM
  · exact outputProbePlacedTM_isTransducer_internal tm
  apply IsTransducer.seqTM
  · exact rewindWorkTM_isTransducer _
  apply IsTransducer.branchWorkSymbolTM
  · exact (outputProbeCleanupTM_isTransducer _).seqTM hone
  · exact (outputProbeCleanupTM_isTransducer _).seqTM hzero

end TM

end Complexity
