/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Internal

/-!
# Decoding terminated-unary fields through output probes

This module exposes the first formula-code query controller used by the
uniform Barrington construction. It scans a terminated-unary field with a
bounded dynamic output probe, preserving a success/failure flag in a concrete
one-bit work register.
-/

namespace Complexity

namespace TM

/-- The bounded semantic controller agrees exactly with the existing
probe-oracle terminated-unary decoder, including unavailable positions and
fuel exhaustion. -/
theorem outputProbeDecodeNatRun_result
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    (outputProbeDecodeNatRun query fuel
      { cursor := cursor, value := value, active := true }).result? =
        FormulaCode.BitOracle.decodeNatAt? query fuel cursor value :=
  outputProbeDecodeNatRun_result_internal query fuel cursor value

/-- A successful oracle-level decode determines the entire final pure
controller state: accumulated value, advanced cursor, and cleared active flag. -/
theorem outputProbeDecodeNatStateAt_eq_of_result
    (bits : List Bool) (fuel cursor value result nextCursor : ℕ)
    (hdecode : FormulaCode.BitOracle.decodeNatAt?
      (FormulaCode.BitOracle.ofList bits) fuel cursor value =
        some (result, nextCursor)) :
    outputProbeDecodeNatStateAt bits
        { cursor := cursor, value := value, active := true } fuel =
      { cursor := nextCursor, value := result, active := false } :=
  outputProbeDecodeNatStateAt_eq_of_result_internal bits fuel cursor value
    result nextCursor hdecode

/-- One semantic decoder iteration over a finite output list consumes its
actual bit whenever the active cursor is valid, and otherwise preserves an
inactive state. -/
theorem outputProbeDecodeNatStep_ofList
    (bits : List Bool) (state : OutputProbeDecodeNatState)
    (hcursor : state.active = true → state.cursor < bits.length) :
    outputProbeDecodeNatStep (FormulaCode.BitOracle.ofList bits) state =
      if state.active then
        { cursor := state.cursor + 1
          value := state.value +
            if outputProbeDecodeNatSourceBit bits state.cursor then 1 else 0
          active := outputProbeDecodeNatSourceBit bits state.cursor }
      else
        state :=
  outputProbeDecodeNatStep_ofList_internal bits state hcursor

/-- Compact form of `outputProbeDecodeNatStep_ofList`: the finite source bit
drives the shared pure state transition. -/
theorem outputProbeDecodeNatStep_ofList_eq_afterBit
    (bits : List Bool) (state : OutputProbeDecodeNatState)
    (hcursor : state.active = true → state.cursor < bits.length) :
    outputProbeDecodeNatStep (FormulaCode.BitOracle.ofList bits) state =
      outputProbeDecodeNatStateAfterBit state
        (outputProbeDecodeNatSourceBit bits state.cursor) :=
  outputProbeDecodeNatStep_ofList_eq_afterBit_internal bits state hcursor

/-- The concrete controller-frame updates for one decoder bit are literally
the canonical frame of the corresponding pure next state. -/
theorem outputProbeDecodeNatOuterExtrasStep_state
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hvalueActive : valueIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (bit : Bool) :
    outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
        (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
          outerExtras state)
        state bit =
      outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
        outerExtras (outputProbeDecodeNatStateAfterBit state bit) :=
  outputProbeDecodeNatOuterExtrasStep_state_internal n cursorIdx valueIdx
    activeIdx hcursorValue hcursorActive hvalueActive outerExtras state bit

/-- Running one more pure decoder iteration is the same as stepping the state
obtained after the previous iterations. -/
theorem outputProbeDecodeNatRun_succ
    (query : FormulaCode.BitOracle) (fuel : ℕ)
    (state : OutputProbeDecodeNatState) :
    outputProbeDecodeNatRun query (fuel + 1) state =
      outputProbeDecodeNatStep query
        (outputProbeDecodeNatRun query fuel state) :=
  outputProbeDecodeNatRun_succ_internal query fuel state

/-- The canonical decoder frame exposes its cursor register. -/
theorem outputProbeDecodeNatStateOuterExtras_cursor
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat state.cursor :=
  outputProbeDecodeNatStateOuterExtras_cursor_internal n cursorIdx valueIdx
    activeIdx hcursorValue hcursorActive outerExtras state

/-- The canonical decoder frame exposes its accumulated value register. -/
theorem outputProbeDecodeNatStateOuterExtras_value
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (hvalueActive : valueIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat state.value :=
  outputProbeDecodeNatStateOuterExtras_value_internal n cursorIdx valueIdx
    activeIdx hvalueActive outerExtras state

/-- The canonical decoder frame exposes its zero-or-one active register. -/
theorem outputProbeDecodeNatStateOuterExtras_active
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat (if state.active then 1 else 0) :=
  outputProbeDecodeNatStateOuterExtras_active_internal n cursorIdx valueIdx
    activeIdx outerExtras state

/-- The canonical loop frame exposes its exact binary iteration counter. -/
theorem outputProbeDecodeNatLoopOuterExtras_loop
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (hloopCursor : loopIdx ≠ cursorIdx)
    (hloopValue : loopIdx ≠ valueIdx)
    (hloopActive : loopIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ) :
    (outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
      loopIdx outerExtras state iteration
      (outputProbeIndexedControllerIdx n loopIdx)).HasBinaryNat iteration :=
  outputProbeDecodeNatLoopOuterExtras_loop_internal n cursorIdx valueIdx
    activeIdx loopIdx hloopCursor hloopValue hloopActive outerExtras state
    iteration

/-- If the cursor, value, active flag, and loop counter already contain their
canonical values, rebuilding that decoder frame changes no tape. -/
theorem outputProbeDecodeNatLoopOuterExtras_eq_self
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat state.cursor)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat state.value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat (if state.active then 1 else 0))
    (hloop :
      (outerExtras (outputProbeIndexedControllerIdx n loopIdx))
        |>.HasBinaryNat iteration) :
    outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx loopIdx
      outerExtras state iteration = outerExtras :=
  outputProbeDecodeNatLoopOuterExtras_eq_self_internal n cursorIdx valueIdx
    activeIdx loopIdx outerExtras state iteration hcursor hvalue hactive hloop

/-- Rebuilding a decoder loop frame preserves the parked outer-frame
invariant. -/
theorem outputProbeDecodeNatLoopOuterExtras_parked
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (state : OutputProbeDecodeNatState) (iteration : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx
        activeIdx loopIdx outerExtras state iteration i) :=
  outputProbeDecodeNatLoopOuterExtras_parked_internal n cursorIdx valueIdx
    activeIdx loopIdx outerExtras houter state iteration

/-- A decoder loop frame leaves every unrelated controller register literally
unchanged. -/
theorem outputProbeDecodeNatLoopOuterExtras_other
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx loopIdx idx : Fin controllerTapes)
    (hcursor : idx ≠ cursorIdx) (hvalue : idx ≠ valueIdx)
    (hactive : idx ≠ activeIdx) (hloop : idx ≠ loopIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ) :
    outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
        loopIdx outerExtras state iteration
        (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) :=
  outputProbeDecodeNatLoopOuterExtras_other_internal n cursorIdx valueIdx
    activeIdx loopIdx idx hcursor hvalue hactive hloop outerExtras state
    iteration

/-- On a zero terminator, the concrete selected continuation clears the
active flag and advances the cursor exactly once. -/
theorem outputProbeDecodeNatZeroTM_hoareTime
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx activeIdx : Fin controllerTapes)
    (hdistinct : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1) :
    (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
      activeIdx).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeNatZeroOuterExtras n cursorIdx activeIdx outerExtras
          cursor)
        input output extras false)
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor) :=
  outputProbeDecodeNatZeroTM_hoareTime_internal tm controllerTapes cursorIdx
    activeIdx hdistinct outerExtras input output extras hextras houter houtput
    cursor hcursor hactive

/-- On a unary one-bit, the concrete selected continuation increments both
the accumulator and cursor exactly once. -/
theorem outputProbeDecodeNatOneTM_hoareTime
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx : Fin controllerTapes)
    (hdistinct : cursorIdx ≠ valueIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor value : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value) :
    (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
      valueIdx).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (outputProbeDecodeNatOneOuterExtras n cursorIdx valueIdx outerExtras
          cursor value)
        input output extras false)
      (binarySuccTime value + 1 + binarySuccTime cursor) :=
  outputProbeDecodeNatOneTM_hoareTime_internal tm controllerTapes cursorIdx
    valueIdx hdistinct outerExtras input output extras hextras houter houtput
    cursor value hcursor hvalue

/-- Compose a certified dynamic source probe with the exact terminated-unary
zero/one register updates. Both branches restore the physical probe latch to
canonical zero before exposing the updated controller frame. -/
theorem outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape) (bit : Bool)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (cursor value : ℕ)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {latchTime latchSpace inputLength clearInitialSpace zeroInitialSpace
      oneInitialSpace : ℕ}
    (hlatch : (outputProbeIndexedLatchTM tm controllerTapes cursorIdx
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
    (hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).Q).WithinAuxSpace inputLength zeroInitialSpace)
    (honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        ({ state := (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).qstart
           input := inp
           work := work
           output := out } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).Q).WithinAuxSpace inputLength oneInitialSpace) :
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).HoareTimeSpace pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx activeIdx
            outerExtras cursor value bit)
          input output extras false)
        (latchTime + 1 +
          outputProbeLatchDispatchTime bit
            (clearWorkTimeBound 1 + 1 + binarySuccTime cursor)
            (clearWorkTimeBound 1 + 1 +
              (binarySuccTime value + 1 + binarySuccTime cursor)))
        inputLength
        (max latchSpace
          (if bit then
            max (clearInitialSpace + clearWorkTimeBound 1)
              (oneInitialSpace +
                (binarySuccTime value + 1 + binarySuccTime cursor))
          else
            zeroInitialSpace +
              (clearWorkTimeBound 1 + 1 + binarySuccTime cursor))) :=
  outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal tm
    controllerTapes cursorIdx scratchIdx valueIdx activeIdx hcursorValue
    hcursorActive outerExtras input output extras bit hextras houter houtput
    cursor value hcursor hvalue hactive hlatch hclearInitial hzeroInitial
    honeInitial

/-- Derive one exact active decoder step directly from a space-bounded source
transducer. Finite frame maxima and the private countdown-reset seam are chosen
internally; the caller supplies only the stable controller invariants. -/
theorem ComputesInSpace.outputProbeDecodeNatActiveTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorScratch : cursorIdx ≠ scratchIdx)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      (∀ inp work out, pre inp work out →
        inp = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).input ∧
        work = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).work ∧
        out = (outputProbeLatchFrameCfg tm controllerTapes outerExtras input
          output extras false).output) ∧
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx).HoareTime pre
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx
              activeIdx outerExtras cursor value
              ((f input)[cursor]'hcursorBound))
            input output extras false)
          bodyBound :=
  hcomp.outputProbeDecodeNatActiveTM_hoareTime_internal input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit controllerTapes outerExtras houter cursorIdx
    scratchIdx valueIdx activeIdx hcursorScratch hcursorValue hcursorActive
    hcursor hscratch value hvalue hactive

/-- Lift a source-derived active query step through the concrete decoder's
outer active-flag dispatch. -/
theorem ComputesInSpace.outputProbeDecodeNatBodyTM_active_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorScratch : cursorIdx ≠ scratchIdx)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat cursor)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 1) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx).HoareTime pre
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx
              activeIdx outerExtras cursor value
              ((f input)[cursor]'hcursorBound))
            input output extras false)
          bodyBound :=
  hcomp.outputProbeDecodeNatBodyTM_active_hoareTime_internal input cursor
    hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
    hcleanupLimit hlimit controllerTapes outerExtras houter cursorIdx
    scratchIdx valueIdx activeIdx hcursorScratch hcursorValue hcursorActive
    hcursor hscratch value hvalue hactive

/-- Once the terminator has cleared the active register, one decoder-body
iteration is exactly a no-op over the restored probe frame. -/
theorem outputProbeDecodeNatBodyTM_inactive_hoareTime
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (hinactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat 0) :
    (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).HoareTime
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        (outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false)
        2 :=
  outputProbeDecodeNatBodyTM_inactive_hoareTime_internal tm controllerTapes
    cursorIdx scratchIdx valueIdx activeIdx outerExtras input output extras
    hextras houter houtput hinactive

/-- Unified exact body contract matching one pure semantic decoder step.
Active states query the valid source cursor; inactive states preserve the
complete frame without imposing a source-position side condition. -/
theorem ComputesInSpace.outputProbeDecodeNatBodyTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (state : OutputProbeDecodeNatState)
    (hcursorBound : state.active = true →
      state.cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : state.active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        (state.cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorScratch : cursorIdx ≠ scratchIdx)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hcursor :
      (outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat state.cursor)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0)
    (hvalue :
      (outerExtras (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat state.value)
    (hactive :
      (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat (if state.active then 1 else 0)) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx).HoareTime pre
          (outputProbeLatchFramePost tm controllerTapes
            (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
              outerExtras state
              (outputProbeDecodeNatSourceBit (f input) state.cursor))
            input output extras false)
          bodyBound :=
  hcomp.outputProbeDecodeNatBodyTM_hoareTime_internal input state hcursorBound
    output houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    hlimit controllerTapes outerExtras houter cursorIdx scratchIdx valueIdx
    activeIdx hcursorScratch hcursorValue hcursorActive hcursor hscratch
    hvalue hactive

/-- Package exact decoder-iteration witnesses into a complete bounded-loop
certificate whose configurations expose the pure decoder state after every
iteration. -/
noncomputable def outputProbeDecodeNatSegmentSpecOfIterationWitnesses
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes)
    (hloopFuel : loopIdx ≠ fuelIdx)
    (hloopCursor : loopIdx ≠ cursorIdx)
    (hloopValue : loopIdx ≠ valueIdx)
    (hloopActive : loopIdx ≠ activeIdx)
    (hfuelCursor : fuelIdx ≠ cursorIdx)
    (hfuelValue : fuelIdx ≠ valueIdx)
    (hfuelActive : fuelIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (initial : OutputProbeDecodeNatState)
    (bodyTime : ℕ → ℕ) (startValue fuelValue : ℕ)
    (hfuel :
      (outerExtras (outputProbeIndexedControllerIdx n fuelIdx)).HasBinaryNat
        fuelValue)
    (iterationWitness : ∀ value, startValue ≤ value → value < fuelValue →
      ∃ time, time ≤ binaryForIterationTime bodyTime value ∧
        (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx
          valueIdx activeIdx loopIdx fuelIdx).reachesIn time
          (outputProbeDecodeNatIterationStartCfg tm controllerTapes cursorIdx
            scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits
            input output extras initial value)
          (outputProbeDecodeNatIterationDoneCfg tm controllerTapes cursorIdx
            scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits
            input output extras initial value)) :
    BinaryForSegmentSpec
      (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx)
      (outputProbeIndexedControllerIdx n loopIdx)
      (outputProbeIndexedControllerIdx n fuelIdx)
      bodyTime startValue fuelValue :=
  outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal tm
    controllerTapes cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx
    hloopFuel hloopCursor hloopValue hloopActive hfuelCursor hfuelValue
    hfuelActive outerExtras bits input output extras hextras houter houtput
    initial bodyTime startValue fuelValue hfuel iterationWitness

/-- Derive the complete exact bounded decoder loop from a source transducer's
`ComputesInSpace` contract.

The returned body-time function noncomputably selects the actual deterministic
runtime of each replayed source query. The register layout structurally keeps
all six controller roles distinct, and the segment's final frame stores
`outputProbeDecodeNatStateAt (f input) initial fuelValue`. -/
noncomputable def ComputesInSpace.outputProbeDecodeNatSegmentSpec
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeNatLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (initial : OutputProbeDecodeNatState)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n layout.scratchIdx))
        |>.HasBinaryNat 0)
    (startValue fuelValue : ℕ)
    (hfuel :
      (outerExtras (outputProbeIndexedControllerIdx n layout.fuelIdx))
        |>.HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, startValue ≤ value → value < fuelValue →
      (outputProbeDecodeNatStateAt (f input) initial value).active = true →
      (outputProbeDecodeNatStateAt (f input) initial value).cursor <
        (f input).length)
    (hqueryLimit : ∀ value, startValue ≤ value → value < fuelValue →
      (outputProbeDecodeNatStateAt (f input) initial value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input) initial value).cursor + 1) ≤
          cleanupLimit) :
    Σ bodyTime : ℕ → ℕ,
      BinaryForSegmentSpec
        (outputProbeDecodeNatBodyTM tm controllerTapes layout.cursorIdx
          layout.scratchIdx layout.valueIdx layout.activeIdx)
        (outputProbeIndexedControllerIdx n layout.loopIdx)
        (outputProbeIndexedControllerIdx n layout.fuelIdx)
        bodyTime startValue fuelValue :=
  hcomp.outputProbeDecodeNatSegmentSpecInternal input output houtput extras
    hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes layout
    outerExtras houter initial hscratch startValue fuelValue hfuel hqueryValid
    hqueryLimit

/-- A complete source-derived decoder run gives a bounded Hoare contract
between its canonical start and final latch frames. The existential body-time
function records the selected runtimes of the restartable source probes. -/
theorem ComputesInSpace.outputProbeDecodeNatTM_hoareTime
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeNatLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (initial : OutputProbeDecodeNatState)
    (hscratch :
      (outerExtras (outputProbeIndexedControllerIdx n layout.scratchIdx))
        |>.HasBinaryNat 0)
    (startValue fuelValue : ℕ) (hstartFuel : startValue ≤ fuelValue)
    (hfuel :
      (outerExtras (outputProbeIndexedControllerIdx n layout.fuelIdx))
        |>.HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, startValue ≤ value → value < fuelValue →
      (outputProbeDecodeNatStateAt (f input) initial value).active = true →
      (outputProbeDecodeNatStateAt (f input) initial value).cursor <
        (f input).length)
    (hqueryLimit : ∀ value, startValue ≤ value → value < fuelValue →
      (outputProbeDecodeNatStateAt (f input) initial value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input) initial value).cursor + 1) ≤
          cleanupLimit) :
    ∃ bodyTime : ℕ → ℕ,
      (outputProbeDecodeNatTM tm controllerTapes layout.cursorIdx
        layout.scratchIdx layout.valueIdx layout.activeIdx layout.loopIdx
        layout.fuelIdx).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatLoopOuterExtras n layout.cursorIdx
            layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
            (outputProbeDecodeNatStateAt (f input) initial startValue)
            startValue)
          input output extras false)
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatLoopOuterExtras n layout.cursorIdx
            layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
            (outputProbeDecodeNatStateAt (f input) initial fuelValue)
            fuelValue)
          input output extras false)
        (binaryForLoopTime bodyTime fuelValue startValue
          (fuelValue - startValue)) :=
  hcomp.outputProbeDecodeNatTM_hoareTime_internal input output houtput extras
    hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes layout
    outerExtras houter initial hscratch startValue fuelValue hstartFuel hfuel
    hqueryValid hqueryLimit

/-- The complete bounded decoder preserves the append-only output discipline. -/
theorem outputProbeDecodeNatTM_isTransducer
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes) :
    (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx valueIdx
      activeIdx loopIdx fuelIdx).IsTransducer :=
  outputProbeDecodeNatTM_isTransducer_internal tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx loopIdx fuelIdx

end TM

end Complexity
