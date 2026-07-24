/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeConsume.Internal

/-!
# Restartable output-probe consumption

This combinator converts a captured query bit into a finite-control branch,
cleans the probe-owned tapes, and only then enters the selected continuation.
-/

namespace Complexity

namespace TM

/-- A restartable output probe reads the selected source bit, restores its
canonical frame, and then runs the matching continuation within an explicit
all-prefix space envelope. -/
theorem ComputesInSpace.outputProbeConsumeTM_hoareTimeSpace
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
            (if (f input)[index]'hindex then oneSpace else zeroSpace)) :=
  hcomp.outputProbeConsumeTM_hoareTimeSpace_internal onZero onOne input
    index hindex output houtput extras frameSpace limit hextras hframe
    hcleanupCounter hcleanupLimit hlimit hzero hone

/-- A restartable output probe also consumes every numeric query position,
selects a Boolean continuation, and restores the same reusable frame and
space envelope. -/
theorem ComputesInSpace.outputProbeConsumeTM_index_halts_hoareTimeSpace
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
            frameSpace limit (if bit then oneSpace else zeroSpace)) :=
  hcomp.outputProbeConsumeTM_index_halts_hoareTimeSpace_internal
    onZero onOne input index output houtput extras frameSpace limit hextras
    hframe hcleanupCounter hcleanupLimit hlimit hzero hone

/-- The complete consume/reset step may occupy a middle work block while an
arbitrary stable serializer frame is preserved around it. -/
theorem ComputesInSpace.outputProbeConsumeTM_hoareTimeSpace_frame
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
            outerFrameSpace) :=
  hcomp.outputProbeConsumeTM_hoareTimeSpace_frame_internal onZero onOne input
    index hindex output houtput extras frameSpace limit hextras hframe
    hcleanupCounter hcleanupLimit hlimit hzero hone controllerTapes
    outerExtras outerFrameSpace houterRead houterFrame

/-- The placed restartable query never moves the real output head left. -/
theorem outputProbePlacedTM_isTransducer (tm : TM n) :
    (outputProbePlacedTM tm).IsTransducer :=
  outputProbePlacedTM_isTransducer_internal tm

/-- Probe consumption is a transducer whenever both continuations are. -/
theorem IsTransducer.outputProbeConsumeTM
    {tm : TM n}
    {onZero onOne : TM (outputProbeControllerTapes n)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeConsumeTM tm onZero onOne).IsTransducer :=
  hzero.outputProbeConsumeTM_internal hone

end TM

end Complexity
