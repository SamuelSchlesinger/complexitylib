/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeIndexed.Defs
import Complexitylib.Models.TuringMachine.OutputProbeIndexed.Internal

/-!
# Dynamically indexed restartable output probes

This module bridges ghost-indexed output-probe contracts to concrete machine
loops. A preserved controller register is copied into the probe countdown,
incremented to select that zero-based position, and queried through the total
framed bit latch.
-/

namespace Complexity

namespace TM

/-- The canonical zero-latch frame is exactly the dynamic-query entry frame
with only its private countdown overwritten by canonical zero. This reusable
identity is the tape-level seam between successive indexed probe clients. -/
theorem outputProbeLatchFrameCfg_work_eq_queryUpdate
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
        (outputProbeCounterTape 0) :=
  outputProbeLatchFrameCfg_work_eq_queryUpdate_internal tm input output
    extras hcleanupCounter controllerTapes value outerExtras

/-- Controller-local indices embed injectively after the complete probe frame. -/
theorem outputProbeIndexedControllerIdx_injective
    (n : ℕ) {controllerTapes : ℕ} :
    Function.Injective
      (@outputProbeIndexedControllerIdx n controllerTapes) :=
  outputProbeIndexedControllerIdx_injective_internal n

/-- Every embedded controller-local index lies outside the probe frame. -/
theorem outputProbeIndexedControllerIdx_not_middle
    (n : ℕ) {controllerTapes : ℕ} (idx : Fin controllerTapes) :
    ¬placeWorkInMiddle 0 (outputProbeControllerTapes n)
      (outputProbeIndexedControllerIdx n idx) :=
  outputProbeIndexedControllerIdx_not_middle_internal n idx

/-- The private countdown lies inside the placed probe frame. -/
theorem outputProbeIndexedCountdownIdx_middle (n controllerTapes : ℕ) :
    placeWorkInMiddle 0 (outputProbeControllerTapes n)
      (outputProbeIndexedCountdownIdx n controllerTapes) :=
  outputProbeIndexedCountdownIdx_middle_internal n controllerTapes

/-- No controller-local register aliases the private probe countdown. -/
theorem outputProbeIndexedControllerIdx_ne_countdown
    (n : ℕ) {controllerTapes : ℕ} (idx : Fin controllerTapes) :
    outputProbeIndexedControllerIdx n idx ≠
      outputProbeIndexedCountdownIdx n controllerTapes :=
  outputProbeIndexedControllerIdx_ne_countdown_internal n idx

/-- A controller-local tape remains exactly equal to its stable outer-frame
value after a latched query. -/
theorem outputProbeLatchFramePost_controller
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
      outerExtras (outputProbeIndexedControllerIdx n idx) :=
  outputProbeLatchFramePost_controller_internal tm controllerTapes
    outerExtras input output extras bit inp work out hpost idx

/-- Updating one controller-local tape after a latched query is represented by
the same update to the stable outer frame; the complete query-owned frame is
unchanged. -/
theorem outputProbeLatchFramePost_updateController
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
      out :=
  outputProbeLatchFramePost_updateController_internal tm controllerTapes
    outerExtras input output extras bit inp work out hpost idx tape

/-- The physical private countdown in a doubly framed query contains the
declared one-based query value. -/
theorem outputProbeIndexedFrameCountdown
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
      (outputProbeIndexedCountdownIdx n controllerTapes)).HasBinaryNat value :=
  outputProbeIndexedFrameCountdown_internal tm controllerTapes value input
    output innerExtras outerExtras

/-- Dynamic countdown preparation preserves every non-countdown tape, writes
the canonical one-based query position, and has an explicit all-prefix space
envelope. -/
theorem outputProbeIndexedPrepareTM_hoareTimeSpace
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
        (outputProbeIndexedPrepareSpace initialSpace index) :=
  outputProbeIndexedPrepareTM_hoareTimeSpace_internal n controllerTapes
    sourceIdx scratchIdx hdistinct index inputLength initialSpace inp₀ work₀
    out₀ hsource hcountdown hscratch hinput hwork houtput hworkSpace
    hinputSpace

/-- A valid zero-based controller index is copied into the private query
countdown and returns the corresponding source-output bit in the persistent
framed latch. -/
theorem ComputesInSpace.outputProbeIndexedLatchTM_hoareTimeSpace
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
              outerFrameSpace)) :=
  hcomp.outputProbeIndexedLatchTM_hoareTimeSpace_internal input index hindex
    output houtput extras frameSpace limit hextras hframe hcleanupCounter
    hcleanupLimit hlimit controllerTapes outerExtras outerFrameSpace
    houterRead houterFrame sourceIdx scratchIdx hdistinct initialSpace work₀
    hsource hcountdown hscratch hinput hwork hworkSpace hinputSpace hqueryWork

/-- A zero-based index stored in a controller register selects one arbitrary
source-output bit. Preparation preserves the register, writes the private
one-based countdown, and composes with the total framed latch while retaining
an explicit all-prefix space bound. -/
theorem ComputesInSpace.outputProbeIndexedLatchTM_index_halts_hoareTimeSpace
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
              outerFrameSpace)) :=
  hcomp.outputProbeIndexedLatchTM_index_halts_hoareTimeSpace_internal input
    index output houtput extras frameSpace limit hextras hframe
    hcleanupCounter hcleanupLimit hlimit controllerTapes outerExtras
    outerFrameSpace houterRead houterFrame sourceIdx scratchIdx hdistinct
    initialSpace work₀ hsource hcountdown hscratch hinput hwork hworkSpace
    hinputSpace hqueryWork

/-- Dynamic countdown preparation is one-way-output safe. -/
theorem outputProbeIndexedPrepareTM_isTransducer
    (n controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    (outputProbeIndexedPrepareTM n controllerTapes
      sourceIdx scratchIdx).IsTransducer :=
  outputProbeIndexedPrepareTM_isTransducer_internal n controllerTapes
    sourceIdx scratchIdx

/-- A dynamically indexed latched query is one-way-output safe. -/
theorem outputProbeIndexedLatchTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (sourceIdx scratchIdx : Fin controllerTapes) :
    (outputProbeIndexedLatchTM tm controllerTapes
      sourceIdx scratchIdx).IsTransducer :=
  outputProbeIndexedLatchTM_isTransducer_internal tm controllerTapes
    sourceIdx scratchIdx

end TM

end Complexity
