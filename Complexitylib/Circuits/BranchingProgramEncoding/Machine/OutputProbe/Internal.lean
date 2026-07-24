/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.Instr
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.OutputProbeIndexed

/-!
# Branching-program emission from restored output-probe frames -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem emitInstrTM_latchFrame_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (counterIdx varIdx : Fin controllerTapes) (hne : counterIdx ≠ varIdx)
    (varValue : ℕ) (perm0 perm1 : Equiv.Perm (Fin 5))
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (ys : List Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : OutAcc ys output)
    (hcounter :
      (outerExtras (outputProbeIndexedControllerIdx n counterIdx))
        |>.HasBinaryNat 0)
    (hvar :
      (outerExtras (outputProbeIndexedControllerIdx n varIdx))
        |>.HasBinaryNat varValue) :
    (emitInstrTM (outputProbeIndexedControllerIdx n counterIdx)
      (outputProbeIndexedControllerIdx n varIdx) perm0 perm1).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (EmitPred
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (ys ++ Instr.encode
          { var := varValue, perm0 := perm0, perm1 := perm1 }))
      (emitInstrTime varValue) := by
  intro inp work out hpost
  obtain ⟨hinputParked, hworkParked, houtputParked⟩ :=
    outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
      output extras false hextras houter houtput.parked inp work out hpost
  have hcounterWork :
      (work (outputProbeIndexedControllerIdx n counterIdx)).HasBinaryNat 0 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost counterIdx]
    exact hcounter
  have hvarWork :
      (work (outputProbeIndexedControllerIdx n varIdx)).HasBinaryNat
        varValue := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost varIdx]
    exact hvar
  have hphysical : outputProbeIndexedControllerIdx n counterIdx ≠
      outputProbeIndexedControllerIdx n varIdx :=
    (outputProbeIndexedControllerIdx_injective n).ne hne
  have hframe := outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
    outerExtras input output extras false inp work out hpost
  have houtAcc : OutAcc ys out := by
    rw [hframe.2.2]
    simpa using houtput
  have hrun := emitInstrTM_hoareTime
    (outputProbeIndexedControllerIdx n counterIdx)
    (outputProbeIndexedControllerIdx n varIdx) hphysical varValue perm0 perm1
    inp work ys hinputParked hcounterWork hvarWork
    (fun i _ _ => hworkParked i)
  obtain ⟨done, elapsed, helapsed, hreach, hhalt, hdone⟩ :=
    hrun inp work out ⟨rfl, rfl, houtAcc⟩
  refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
  rcases hdone with ⟨hinputDone, hworkDone, houtputDone⟩
  exact ⟨hinputDone.trans hframe.1,
    hworkDone.trans hframe.2.1, houtputDone⟩

theorem skipTM_latchFrame_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (ys : List Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : OutAcc ys output) :
    (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (EmitPred
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work ys)
      1 := by
  intro inp work out hpost
  obtain ⟨hinputParked, hworkParked, houtputParked⟩ :=
    outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
      output extras false hextras houter houtput.parked inp work out hpost
  have hframe := outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
    outerExtras input output extras false inp work out hpost
  have houtAcc : OutAcc ys out := by
    rw [hframe.2.2]
    simpa using houtput
  have hrun := skipTM_hoareTime_frame inp work out hinputParked hworkParked
    houtputParked
  obtain ⟨done, elapsed, helapsed, hreach, hhalt, hdone⟩ :=
    hrun inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
  rcases hdone with ⟨hinputDone, hworkDone, houtputDone⟩
  exact ⟨hinputDone.trans hframe.1,
    hworkDone.trans hframe.2.1, by rw [houtputDone]; exact houtAcc⟩

end Machine

end BPCode

end Complexity
