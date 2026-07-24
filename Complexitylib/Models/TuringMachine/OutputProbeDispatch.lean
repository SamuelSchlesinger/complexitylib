/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch.Internal

/-!
# Dynamically indexed output-probe dispatch

This module exposes the outer-controller branch that consumes a persistent
output-probe latch. It is the reusable body boundary for bounded scans whose
Boolean branches update controller registers before the next query.
-/

namespace Complexity

namespace TM

/-- A restored latch frame is parked on its input, every work tape, and its
real output whenever both supplied frames are parked. -/
theorem outputProbeLatchFramePost_parked
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
    Parked inp ∧ (∀ i, Parked (work i)) ∧ Parked out :=
  outputProbeLatchFramePost_parked_internal tm controllerTapes outerExtras
    input output extras bit hextras houter houtput inp work out hpost

/-- Clearing a true latch restores exactly the false/zero latch frame. A caller
supplies the initial frame-space certificate; the standard head-growth bound
then covers every clearing prefix. -/
theorem outputProbeLatch_clear_hoareTimeSpace
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
        (initialSpace + clearWorkTimeBound 1) :=
  outputProbeLatch_clear_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras hextras houter houtput inputLength
    initialSpace hinitial

/-- Dispatching a parked latch selects the continuation indexed by its exact
Boolean value, with no space overhead beyond that continuation. -/
theorem outputProbeLatchDispatchTM_hoareTimeSpace
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
        inputLength (if bit then oneSpace else zeroSpace) :=
  outputProbeLatchDispatchTM_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras bit hextras houter houtput onZero onOne
    hzero hone

/-- Resetting dispatch presents both selected continuations with the exact
canonical zero-latch frame. The true branch pays for clearing its one-bit
latch; the false branch enters its continuation directly. -/
theorem outputProbeLatchResetDispatchTM_hoareTimeSpace
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
        else zeroSpace) :=
  outputProbeLatchResetDispatchTM_hoareTimeSpace_internal tm controllerTapes
    outerExtras input output extras bit hextras houter houtput onZero onOne
    hclearInitial hzero hone

/-- Any certified dynamically indexed latch phase composes with the direct
Boolean dispatch. The only seam obligation is the parked restored frame, which
is discharged from the probe-frame hypotheses. -/
theorem outputProbeIndexedDispatchTM_of_latch_hoareTimeSpace
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
        (max latchSpace (if bit then oneSpace else zeroSpace)) :=
  outputProbeIndexedDispatchTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes sourceIdx scratchIdx outerExtras input output extras bit
    hextras houter houtput onZero onOne hlatch hzero hone

/-- A certified dynamic latch phase composes with invariant-restoring Boolean
dispatch: both selected continuations start from the exact zero-latch frame. -/
theorem outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace
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
          else zeroSpace)) :=
  outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes sourceIdx scratchIdx outerExtras input output extras bit
    hextras houter houtput onZero onOne hlatch hclearInitial hzero hone

/-- Direct latch dispatch is one-way-output safe whenever both continuations
are one-way-output safe. -/
theorem IsTransducer.outputProbeLatchDispatchTM
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeLatchDispatchTM n controllerTapes onZero onOne).IsTransducer :=
  hzero.outputProbeLatchDispatchTM_internal hone

/-- Dynamic query-and-dispatch is one-way-output safe whenever both selected
continuations are one-way-output safe. -/
theorem IsTransducer.outputProbeIndexedDispatchTM
    {tm : TM n} {controllerTapes : ℕ}
    {sourceIdx scratchIdx : Fin controllerTapes}
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeIndexedDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).IsTransducer :=
  hzero.outputProbeIndexedDispatchTM_internal hone

/-- Latch-resetting dispatch is one-way-output safe whenever both normalized
continuations are one-way-output safe. -/
theorem IsTransducer.outputProbeLatchResetDispatchTM
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeLatchResetDispatchTM n controllerTapes onZero
      onOne).IsTransducer :=
  hzero.outputProbeLatchResetDispatchTM_internal hone

/-- Dynamic query, latch reset, and Boolean dispatch preserve one-way-output
safety whenever both selected continuations do. -/
theorem IsTransducer.outputProbeIndexedResetDispatchTM
    {tm : TM n} {controllerTapes : ℕ}
    {sourceIdx scratchIdx : Fin controllerTapes}
    {onZero onOne : TM (0 + outputProbeControllerTapes n + controllerTapes)}
    (hzero : onZero.IsTransducer) (hone : onOne.IsTransducer) :
    (outputProbeIndexedResetDispatchTM tm controllerTapes sourceIdx scratchIdx
      onZero onOne).IsTransducer :=
  hzero.outputProbeIndexedResetDispatchTM_internal hone

end TM

end Complexity
