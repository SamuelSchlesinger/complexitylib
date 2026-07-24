/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeConsume
import Complexitylib.Models.TuringMachine.OutputProbeLatch.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Restartable output probes with a framed bit latch -- proof internals
-/

namespace Complexity

namespace TM

private theorem outputProbeLatch_hasBinaryNat_parked {tape : Tape}
    {value : ℕ} (hvalue : tape.HasBinaryNat value) : Parked tape := by
  refine ⟨by rw [hvalue.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start hvalue.2.2

private theorem outputProbeLatchCounter_not_middle (n : ℕ) :
    ¬placeWorkInMiddle 0 (n + 2) (outputProbeCleanupCounterIdx n) := by
  simp [placeWorkInMiddle, outputProbeCleanupCounterIdx]

private theorem outputProbeLatchCleanCounter
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (value : ℕ)
    (hcounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat value) :
    ((outputProbePlacedFrameCfg tm input (outputProbeCounterTape 0)
      output extras).work
        (outputProbeCleanupCounterIdx n)).HasBinaryNat value := by
  rw [outputProbePlacedFrameCfg, placeWorkCfg_work_extra]
  exact hcounter
  exact outputProbeLatchCounter_not_middle n

private theorem outputProbeLatchCleanInputParked
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) :
    Parked (outputProbePlacedFrameCfg tm input (outputProbeCounterTape 0)
      output extras).input := by
  simp only [outputProbePlacedFrameCfg, placeWorkCfg_input,
    retargetCfgFrame_input, outputProbeStartedCfg]
  simpa [Tape.move] using parked_init_input input

private theorem outputProbeLatchCleanWorkParked
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
        exact outputProbeLatch_hasBinaryNat_parked
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

private theorem outputProbeLatchCleanWithin
    (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (frameSpace : ℕ)
    (hframe : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace) :
    Cfg.WithinAuxSpace
      (⟨(outputProbeLatchZeroTM n).qstart,
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape 0) output extras).input,
        (outputProbePlacedFrameCfg tm input
          (outputProbeCounterTape 0) output extras).work,
        output⟩ :
      Cfg (outputProbeControllerTapes n) (outputProbeLatchZeroTM n).Q)
      input.length (outputProbeLatchCleanSpace frameSpace) := by
  constructor
  · intro i
    rw [outputProbePlacedFrameCfg]
    by_cases hi : placeWorkInMiddle 0 (n + 2) i
    · simp only [placeWorkCfg, hi, dite_true]
      let coord := placeWorkCoord 0 (n + 2) i hi
      have hhead :
          ((tm.outputProbeStartedTM.retargetCfgFrame
            (tm.outputProbeStartedCfg input (outputProbeCounterTape 0))
            output).work coord).head = 1 := by
        by_cases hsource : coord.val < n + 1
        · rw [retargetCfgFrame_work_lt _ _ _ coord hsource]
          by_cases hsourceWork : coord.val < n
          · simp [outputProbeStartedCfg, hsourceWork, Tape.move]
          · simp [outputProbeStartedCfg,
              outputProbeCounterTape, Tape.move]
        · have hvirtualOutput : coord = Fin.last (n + 1) := by
            apply Fin.ext
            simp only [Fin.last, coord]
            have hcoord : coord.val < n + 2 := coord.isLt
            omega
          rw [hvirtualOutput, retargetCfgFrame_work_last]
          simp [outputProbeStartedCfg, Tape.move]
      change
        ((tm.outputProbeStartedTM.retargetCfgFrame
          (tm.outputProbeStartedCfg input (outputProbeCounterTape 0))
          output).work coord).head ≤ outputProbeLatchCleanSpace frameSpace
      rw [hhead]
      exact Nat.le_max_left 1 frameSpace
    · rw [placeWorkCfg_work_extra]
      exact le_trans (hframe i hi) (Nat.le_max_right 1 frameSpace)
      exact hi
  · have hhead :
        (outputProbePlacedFrameCfg tm input (outputProbeCounterTape 0)
          output extras).input.head = 1 := by
      simp [outputProbePlacedFrameCfg, outputProbeStartedCfg, Tape.move]
    rw [hhead]
    omega

theorem outputProbeLatchFramePost_latch_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out) :
    (work (outputProbeLatchIdx n controllerTapes)).HasBinaryNat
      (if bit then 1 else 0) := by
  obtain ⟨sourceWork, hsource, hwork⟩ := hpost
  rw [hwork, outputProbeLatchIdx, placeWorkCfg_work_middle]
  exact hsource.2.2.1

theorem outputProbeLatchFrameCfg_post_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool) :
    outputProbeLatchFramePost tm controllerTapes outerExtras input output
      extras bit
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras bit).input
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras bit).work
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras bit).output := by
  refine ⟨(outputProbeLatchInnerFrameCfg tm input output extras bit).work,
    ?_, rfl⟩
  refine ⟨rfl, ?_, ?_, rfl⟩
  · intro i hi
    simp [outputProbeLatchInnerFrameCfg, Function.update_of_ne hi]
  · simp only [outputProbeLatchInnerFrameCfg, Function.update_self]
    exact Tape.init_move_right_hasBinaryNat _

theorem outputProbeLatchFramePost_eq_frameCfg_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (inp : Tape)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) → Tape)
    (out : Tape)
    (hpost : outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras bit inp work out) :
    inp = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras bit).input ∧
      work = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
        output extras bit).work ∧
      out = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
        output extras bit).output := by
  obtain ⟨sourceWork, hsource, hwork⟩ := hpost
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  have hsourceWork :
      sourceWork =
        (outputProbeLatchInnerFrameCfg tm input output extras bit).work := by
    funext i
    by_cases hi : i = outputProbeCleanupCounterIdx n
    · subst i
      rw [hsource.2.2.1.eq_init_move_right]
      simp [outputProbeLatchInnerFrameCfg, outputProbeCounterTape]
    · simpa [outputProbeLatchInnerFrameCfg, cleanCfg,
        Function.update_of_ne hi] using hsource.2.1 i hi
  refine ⟨?_, ?_, ?_⟩
  · simpa [outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg, cleanCfg]
      using hsource.1
  · rw [hwork]
    rw [hsourceWork]
    funext i
    by_cases hi : placeWorkInMiddle 0 (outputProbeControllerTapes n) i
    · simp [outputProbeLatchFrameCfg, placeWorkCfg, hi]
    · simp [outputProbeLatchFrameCfg, placeWorkCfg, hi]
  · simpa [outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg, cleanCfg]
      using hsource.2.2.2

theorem ComputesInSpace.outputProbeLatchTM_hoareTimeSpace_internal
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
        (outerExtras i).head ≤ outerFrameSpace) :
    ∃ latchTime,
      (outputProbeLatchTM tm controllerTapes).HoareTimeSpace
        (placeWorkPred (outputProbeLatchInnerTM tm) 0 controllerTapes
          outerExtras
          (fun inp work out =>
            inp = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).input ∧
            work = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).work ∧
            out = output))
        (outputProbeLatchFramePost tm controllerTapes outerExtras input
          output extras ((f input)[index]'hindex))
        latchTime input.length
          (max
            (outputProbeConsumeSpace n (max 1 (space input.length)) index
              frameSpace limit
              (outputProbeLatchContinuationSpace
                ((f input)[index]'hindex) frameSpace))
            outerFrameSpace) := by
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  let cleanSpace := outputProbeLatchCleanSpace frameSpace
  have hinputParked : Parked cleanCfg.input := by
    exact outputProbeLatchCleanInputParked tm input output extras
  have hworkParked : ∀ i, Parked (cleanCfg.work i) := by
    exact outputProbeLatchCleanWorkParked tm input output extras hextras
  have hcounter :
      (cleanCfg.work (outputProbeCleanupCounterIdx n)).HasBinaryNat 0 := by
    exact outputProbeLatchCleanCounter tm input output extras 0 hcleanupCounter
  have hwithin :
      Cfg.WithinAuxSpace
        (⟨(outputProbeLatchZeroTM n).qstart, cleanCfg.input,
          cleanCfg.work, output⟩ :
        Cfg (outputProbeControllerTapes n) (outputProbeLatchZeroTM n).Q)
        input.length cleanSpace := by
    exact outputProbeLatchCleanWithin tm input output extras frameSpace hframe
  have hzeroTime := skipTM_hoareTime_frame cleanCfg.input cleanCfg.work output
    hinputParked hworkParked houtput
  have hzeroBase := hzeroTime.toHoareTimeSpace (inputLength := input.length)
    (initialSpace := cleanSpace) (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      exact hwithin)
  have hzero : (outputProbeLatchZeroTM n).HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (outputProbeLatchPost tm input output extras false)
      1 input.length (cleanSpace + 1) := by
    apply hzeroBase.consequence (fun _ _ _ h => h) _ le_rfl le_rfl le_rfl
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, fun _ _ => rfl, by simpa using hcounter, rfl⟩
  have hwithinOne :
      Cfg.WithinAuxSpace
        (⟨(outputProbeLatchOneTM n).qstart, cleanCfg.input,
          cleanCfg.work, output⟩ :
        Cfg (outputProbeControllerTapes n) (outputProbeLatchOneTM n).Q)
        input.length cleanSpace := by
    simpa [outputProbeLatchZeroTM, outputProbeLatchOneTM] using hwithin
  have honeBase := binarySuccTM_hoareTimeSpace_frame
    (outputProbeCleanupCounterIdx n) 0 input.length cleanSpace
    cleanCfg.input cleanCfg.work output hcounter hinputParked.read_ne_start
    (fun i _ => (hworkParked i).read_ne_start) houtput.read_ne_start
    hwithinOne
  have hone : (outputProbeLatchOneTM n).HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (outputProbeLatchPost tm input output extras true)
      (binarySuccTime 0) input.length (cleanSpace + binarySuccTime 0) := by
    apply honeBase.consequence (fun _ _ _ h => h) _ le_rfl le_rfl le_rfl
    rintro inp work out ⟨rfl, hother, hone, rfl⟩
    exact ⟨rfl, hother, by simpa using hone, rfl⟩
  obtain ⟨latchTime, hlatch⟩ :=
    hcomp.outputProbeConsumeTM_hoareTimeSpace_frame
      (outputProbeLatchZeroTM n) (outputProbeLatchOneTM n)
      input index hindex output houtput extras frameSpace limit hextras hframe
      hcleanupCounter hcleanupLimit hlimit hzero hone controllerTapes
      outerExtras outerFrameSpace houterRead houterFrame
  refine ⟨latchTime, ?_⟩
  simpa [outputProbeLatchTM, outputProbeLatchInnerTM,
    outputProbeLatchFramePost, outputProbeLatchContinuationSpace,
    cleanSpace] using hlatch

theorem
    ComputesInSpace.outputProbeLatchTM_index_halts_hoareTimeSpace_internal
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
        (outerExtras i).head ≤ outerFrameSpace) :
    ∃ bit latchTime,
      (outputProbeLatchTM tm controllerTapes).HoareTimeSpace
        (placeWorkPred (outputProbeLatchInnerTM tm) 0 controllerTapes
          outerExtras
          (fun inp work out =>
            inp = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).input ∧
            work = (outputProbePlacedFrameCfg tm input
                (outputProbeCounterTape (index + 1)) output extras).work ∧
            out = output))
        (outputProbeLatchFramePost tm controllerTapes outerExtras input
          output extras bit)
        latchTime input.length
          (max
            (outputProbeConsumeSpace n (max 1 (space input.length)) index
              frameSpace limit
              (outputProbeLatchContinuationSpace bit frameSpace))
            outerFrameSpace) := by
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  let cleanSpace := outputProbeLatchCleanSpace frameSpace
  have hinputParked : Parked cleanCfg.input := by
    exact outputProbeLatchCleanInputParked tm input output extras
  have hworkParked : ∀ i, Parked (cleanCfg.work i) := by
    exact outputProbeLatchCleanWorkParked tm input output extras hextras
  have hcounter :
      (cleanCfg.work (outputProbeCleanupCounterIdx n)).HasBinaryNat 0 := by
    exact outputProbeLatchCleanCounter tm input output extras 0 hcleanupCounter
  have hwithin :
      Cfg.WithinAuxSpace
        (⟨(outputProbeLatchZeroTM n).qstart, cleanCfg.input,
          cleanCfg.work, output⟩ :
        Cfg (outputProbeControllerTapes n) (outputProbeLatchZeroTM n).Q)
        input.length cleanSpace := by
    exact outputProbeLatchCleanWithin tm input output extras frameSpace hframe
  have hzeroTime := skipTM_hoareTime_frame cleanCfg.input cleanCfg.work output
    hinputParked hworkParked houtput
  have hzeroBase := hzeroTime.toHoareTimeSpace (inputLength := input.length)
    (initialSpace := cleanSpace) (by
      rintro inp work out ⟨rfl, rfl, rfl⟩
      exact hwithin)
  have hzero : (outputProbeLatchZeroTM n).HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (outputProbeLatchPost tm input output extras false)
      1 input.length (cleanSpace + 1) := by
    apply hzeroBase.consequence (fun _ _ _ h => h) _ le_rfl le_rfl le_rfl
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, fun _ _ => rfl, by simpa using hcounter, rfl⟩
  have hwithinOne :
      Cfg.WithinAuxSpace
        (⟨(outputProbeLatchOneTM n).qstart, cleanCfg.input,
          cleanCfg.work, output⟩ :
        Cfg (outputProbeControllerTapes n) (outputProbeLatchOneTM n).Q)
        input.length cleanSpace := by
    simpa [outputProbeLatchZeroTM, outputProbeLatchOneTM] using hwithin
  have honeBase := binarySuccTM_hoareTimeSpace_frame
    (outputProbeCleanupCounterIdx n) 0 input.length cleanSpace
    cleanCfg.input cleanCfg.work output hcounter hinputParked.read_ne_start
    (fun i _ => (hworkParked i).read_ne_start) houtput.read_ne_start
    hwithinOne
  have hone : (outputProbeLatchOneTM n).HoareTimeSpace
      (fun inp work out =>
        inp = cleanCfg.input ∧ work = cleanCfg.work ∧ out = output)
      (outputProbeLatchPost tm input output extras true)
      (binarySuccTime 0) input.length (cleanSpace + binarySuccTime 0) := by
    apply honeBase.consequence (fun _ _ _ h => h) _ le_rfl le_rfl le_rfl
    rintro inp work out ⟨rfl, hother, hone, rfl⟩
    exact ⟨rfl, hother, by simpa using hone, rfl⟩
  obtain ⟨bit, latchTime, hlatch⟩ :=
    hcomp.outputProbeConsumeTM_index_halts_hoareTimeSpace_frame_internal
      (outputProbeLatchZeroTM n) (outputProbeLatchOneTM n)
      input index output houtput extras frameSpace limit hextras hframe
      hcleanupCounter hcleanupLimit hlimit hzero hone controllerTapes
      outerExtras outerFrameSpace houterRead houterFrame
  refine ⟨bit, latchTime, ?_⟩
  simpa [outputProbeLatchTM, outputProbeLatchInnerTM,
    outputProbeLatchFramePost, outputProbeLatchContinuationSpace,
    cleanSpace] using hlatch

theorem outputProbeLatchTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ) :
    (outputProbeLatchTM tm controllerTapes).IsTransducer := by
  have hzero : (outputProbeLatchZeroTM n).IsTransducer := by
    intro state inputHead workHeads outputHead
    cases state <;> cases outputHead <;>
      simp [outputProbeLatchZeroTM, skipTM, idleDir]
  have hone : (outputProbeLatchOneTM n).IsTransducer := by
    exact binarySuccTM_isTransducer (outputProbeCleanupCounterIdx n)
  exact (hzero.outputProbeConsumeTM hone).placeWorkTM 0 controllerTapes

end TM

end Complexity
