/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeConsume.Defs
import Complexitylib.Models.TuringMachine.Placement.Defs
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc.Defs

/-!
# Restartable output probes with a framed bit latch -- definitions

The consume/reset combinator branches while the captured bit is still in
finite control. This module records that bit in the cleanup counter after the
query-owned tapes have been restored, then places the complete query beside an
arbitrary serializer frame. The cleanup counter is zero before every query and
is therefore a reusable one-bit latch.
-/

namespace Complexity

namespace TM

/-- The zero continuation leaves the restored query frame unchanged. -/
def outputProbeLatchZeroTM (n : ℕ) : TM (outputProbeControllerTapes n) :=
  skipTM

/-- The one continuation raises the restored zero cleanup counter to one. -/
def outputProbeLatchOneTM (n : ℕ) : TM (outputProbeControllerTapes n) :=
  binarySuccTM (outputProbeCleanupCounterIdx n)

/-- Query one source-output bit, restore the query frame, and retain the bit in
the cleanup counter as canonical binary zero or one. -/
def outputProbeLatchInnerTM (tm : TM n) : TM (outputProbeControllerTapes n) :=
  outputProbeConsumeTM tm (outputProbeLatchZeroTM n)
    (outputProbeLatchOneTM n)

/-- Place the latched query before `controllerTapes` arbitrary serializer work
tapes. -/
def outputProbeLatchTM (tm : TM n) (controllerTapes : ℕ) :
    TM (0 + outputProbeControllerTapes n + controllerTapes) :=
  placeWorkTM 0 controllerTapes (outputProbeLatchInnerTM tm)

/-- Physical location of the reusable bit latch in the placed controller. -/
def outputProbeLatchIdx (n controllerTapes : ℕ) :
    Fin (0 + outputProbeControllerTapes n + controllerTapes) :=
  placeWorkIdx 0 controllerTapes (outputProbeCleanupCounterIdx n)

/-- Exact restored inner frame with the queried Boolean stored in the cleanup
counter. -/
def outputProbeLatchPost (tm : TM n) (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool) :
    TapePred (outputProbeControllerTapes n) :=
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  fun inp work out =>
    inp = cleanCfg.input ∧
    (∀ i, i ≠ outputProbeCleanupCounterIdx n →
      work i = cleanCfg.work i) ∧
    (work (outputProbeCleanupCounterIdx n)).HasBinaryNat
      (if bit then 1 else 0) ∧
    out = output

/-- Stable outer-frame form of `outputProbeLatchPost`. -/
def outputProbeLatchFramePost (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool) :
    TapePred (0 + outputProbeControllerTapes n + controllerTapes) :=
  placeWorkPred (outputProbeLatchInnerTM tm) 0 controllerTapes outerExtras
    (outputProbeLatchPost tm input output extras bit)

/-- Canonical restored inner query frame with an explicit zero-or-one latch. -/
def outputProbeLatchInnerFrameCfg (tm : TM n) (input : List Bool)
    (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool) :
    Cfg (outputProbeControllerTapes n) (outputProbeLatchInnerTM tm).Q :=
  let cleanCfg := outputProbePlacedFrameCfg tm input
    (outputProbeCounterTape 0) output extras
  { state := (outputProbeLatchInnerTM tm).qstart
    input := cleanCfg.input
    work := Function.update cleanCfg.work (outputProbeCleanupCounterIdx n)
      (outputProbeCounterTape (if bit then 1 else 0))
    output := output }

/-- Canonical restored query frame placed before arbitrary controller tapes. -/
def outputProbeLatchFrameCfg (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool) :
    Cfg (0 + outputProbeControllerTapes n + controllerTapes)
      (outputProbeLatchTM tm controllerTapes).Q :=
  placeWorkCfg (outputProbeLatchInnerTM tm) 0 controllerTapes outerExtras
    (outputProbeLatchInnerFrameCfg tm input output extras bit)

/-- Auxiliary-space budget of the restored inner query frame. -/
def outputProbeLatchCleanSpace (frameSpace : ℕ) : ℕ :=
  max 1 frameSpace

/-- Continuation-space budget used by the zero and one latch branches. -/
def outputProbeLatchContinuationSpace (bit : Bool) (frameSpace : ℕ) : ℕ :=
  if bit then
    outputProbeLatchCleanSpace frameSpace + binarySuccTime 0
  else
    outputProbeLatchCleanSpace frameSpace + 1

end TM

end Complexity
