/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeLatch.Defs
import Complexitylib.Models.TuringMachine.OutputProbeLatch.Internal

/-!
# Restartable output probes with a framed bit latch

This module turns the finite-control result of a restartable output query into
a persistent canonical binary zero-or-one latch. The query and its cleanup
occupy a fixed prefix of the work vector; arbitrary serializer tapes after that
prefix remain a literal stable frame.
-/

namespace Complexity

namespace TM

/-- The canonical restored query frame satisfies the stable outer-frame
predicate with its explicit zero-or-one latch. -/
theorem outputProbeLatchFrameCfg_post
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
        extras bit).output :=
  outputProbeLatchFrameCfg_post_internal tm controllerTapes outerExtras input
    output extras bit

/-- The restored latch-frame predicate determines the canonical physical
input, work, and output tapes uniquely. -/
theorem outputProbeLatchFramePost_eq_frameCfg
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
        output extras bit).output :=
  outputProbeLatchFramePost_eq_frameCfg_internal tm controllerTapes
    outerExtras input output extras bit inp work out hpost

/-- The physical latch selected by the placed frame predicate contains exactly
the queried Boolean as canonical binary zero or one. -/
theorem outputProbeLatchFramePost_latch
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
      (if bit then 1 else 0) :=
  outputProbeLatchFramePost_latch_internal tm controllerTapes outerExtras
    input output extras bit inp work out hpost

/-- A valid source-output query restores its complete query frame and stores
the selected Boolean as canonical binary zero or one in the reusable cleanup
counter. Every outer serializer tape is preserved exactly, and the theorem
carries the combined all-prefix auxiliary-space bound. -/
theorem ComputesInSpace.outputProbeLatchTM_hoareTimeSpace
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
            outerFrameSpace) :=
  hcomp.outputProbeLatchTM_hoareTimeSpace_internal input index hindex output
    houtput extras frameSpace limit hextras hframe hcleanupCounter
    hcleanupLimit hlimit controllerTapes outerExtras outerFrameSpace
    houterRead houterFrame

/-- Every numeric output query restores its complete query frame and stores
the selected Boolean as canonical binary zero or one in the reusable cleanup
counter, while preserving every outer serializer tape. -/
theorem ComputesInSpace.outputProbeLatchTM_index_halts_hoareTimeSpace
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
            outerFrameSpace) :=
  hcomp.outputProbeLatchTM_index_halts_hoareTimeSpace_internal input index
    output houtput extras frameSpace limit hextras hframe hcleanupCounter
    hcleanupLimit hlimit controllerTapes outerExtras outerFrameSpace
    houterRead houterFrame

/-- The latched query is one-way-output safe. -/
theorem outputProbeLatchTM_isTransducer (tm : TM n) (controllerTapes : ℕ) :
    (outputProbeLatchTM tm controllerTapes).IsTransducer :=
  outputProbeLatchTM_isTransducer_internal tm controllerTapes

end TM

end Complexity
