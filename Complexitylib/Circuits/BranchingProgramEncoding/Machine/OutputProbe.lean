/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbe.Internal

/-!
# Branching-program emission from restored output-probe frames

This adapter lets the Barrington controller emit a canonical instruction
directly from two registers in its restored restartable-query frame.  The
output accumulator advances, while the physical input and complete work frame
remain literal fixed points.
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

/-- Emit one instruction from controller-local variable and scratch registers
inside a restored zero-latch output-probe frame. -/
theorem emitInstrTM_latchFrame_hoareTime
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
      (emitInstrTime varValue) :=
  emitInstrTM_latchFrame_hoareTime_internal tm controllerTapes counterIdx
    varIdx hne varValue perm0 perm1 outerExtras input output extras ys
    hextras houter houtput hcounter hvar

/-- The constant-instruction specialization consumes a canonical zero value
register and emits exactly `BPInstr.const target`. -/
theorem emitConstInstrTM_latchFrame_hoareTime
    (tm : TM n) (controllerTapes : ℕ)
    (counterIdx zeroIdx : Fin controllerTapes) (hne : counterIdx ≠ zeroIdx)
    (target : Equiv.Perm (Fin 5))
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
    (hzero :
      (outerExtras (outputProbeIndexedControllerIdx n zeroIdx))
        |>.HasBinaryNat 0) :
    (emitConstInstrTM (outputProbeIndexedControllerIdx n counterIdx)
      (outputProbeIndexedControllerIdx n zeroIdx) target).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (EmitPred
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (ys ++ Instr.encode (BPInstr.const target)))
      (emitInstrTime 0) := by
  simpa [emitConstInstrTM, BPInstr.const] using
    emitInstrTM_latchFrame_hoareTime tm controllerTapes counterIdx zeroIdx hne
      0 target target outerExtras input output extras ys hextras houter houtput
      hcounter hzero

/-- The false-leaf continuation emits nothing and converts the restored latch
predicate to its literal accumulator frame. -/
theorem skipTM_latchFrame_hoareTime
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
      1 :=
  skipTM_latchFrame_hoareTime_internal tm controllerTapes outerExtras input
    output extras ys hextras houter houtput

end Machine

end BPCode

end Complexity
