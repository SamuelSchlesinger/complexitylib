/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.OutputProbeDecodeNat.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDispatch
import Complexitylib.Models.TuringMachine.OutputProbeScan.Internal
import Complexitylib.Models.TuringMachine.Registers.RegisterOps
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Decoding terminated-unary fields through output probes -- internals
-/

namespace Complexity

namespace TM

private theorem OutputProbeDecodeNatLayout.roles_ne_internal
    (layout : OutputProbeDecodeNatLayout controllerTapes)
    {i j : Fin 6} (hne : i ≠ j) : layout.roles i ≠ layout.roles j := by
  intro heq
  exact hne (layout.roles.injective heq)

private theorem outputProbeDecodeNatRun_inactive_internal
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    outputProbeDecodeNatRun query fuel
        { cursor := cursor, value := value, active := false } =
      { cursor := cursor, value := value, active := false } := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simpa [outputProbeDecodeNatRun, outputProbeDecodeNatStep] using ih

theorem outputProbeDecodeNatRun_result_internal
    (query : FormulaCode.BitOracle) (fuel cursor value : ℕ) :
    (outputProbeDecodeNatRun query fuel
      { cursor := cursor, value := value, active := true }).result? =
        FormulaCode.BitOracle.decodeNatAt? query fuel cursor value := by
  induction fuel generalizing cursor value with
  | zero => rfl
  | succ fuel ih =>
      rw [FormulaCode.BitOracle.decodeNatAt?]
      simp only [outputProbeDecodeNatRun, outputProbeDecodeNatStep, if_true]
      cases hbit : query cursor with
      | none =>
          simp only
          rw [ih]
          cases fuel <;>
            simp [FormulaCode.BitOracle.decodeNatAt?, hbit]
      | some bit =>
          cases bit with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
              rw [outputProbeDecodeNatRun_inactive_internal]
              rfl
          | true =>
              simpa [hbit] using ih (cursor + 1) (value + 1)

theorem outputProbeDecodeNatStateAt_eq_of_result_internal
    (bits : List Bool) (fuel cursor value result nextCursor : ℕ)
    (hdecode : FormulaCode.BitOracle.decodeNatAt?
      (FormulaCode.BitOracle.ofList bits) fuel cursor value =
        some (result, nextCursor)) :
    outputProbeDecodeNatStateAt bits
        { cursor := cursor, value := value, active := true } fuel =
      { cursor := nextCursor, value := result, active := false } := by
  let state := outputProbeDecodeNatStateAt bits
    { cursor := cursor, value := value, active := true } fuel
  have hresult : state.result? = some (result, nextCursor) := by
    change (outputProbeDecodeNatRun (FormulaCode.BitOracle.ofList bits) fuel
      { cursor := cursor, value := value, active := true }).result? =
        some (result, nextCursor)
    rw [outputProbeDecodeNatRun_result_internal]
    exact hdecode
  rcases hstate : state with ⟨stateCursor, stateValue, stateActive⟩
  change state =
    { cursor := nextCursor, value := result, active := false }
  cases stateActive
  · rw [hstate] at hresult ⊢
    simp only [OutputProbeDecodeNatState.result?, Bool.false_eq_true,
      if_false, Option.some.injEq, Prod.mk.injEq] at hresult
    rcases hresult with ⟨rfl, rfl⟩
    rfl
  · rw [hstate] at hresult
    simp [OutputProbeDecodeNatState.result?] at hresult

theorem outputProbeDecodeNatStep_ofList_internal
    (bits : List Bool) (state : OutputProbeDecodeNatState)
    (hcursor : state.active = true → state.cursor < bits.length) :
    outputProbeDecodeNatStep (FormulaCode.BitOracle.ofList bits) state =
      if state.active then
        { cursor := state.cursor + 1
          value := state.value +
            if outputProbeDecodeNatSourceBit bits state.cursor then 1 else 0
          active := outputProbeDecodeNatSourceBit bits state.cursor }
      else
        state := by
  by_cases hactive : state.active
  · have hbound := hcursor hactive
    simp [outputProbeDecodeNatStep, hactive, FormulaCode.BitOracle.ofList,
      outputProbeDecodeNatSourceBit,
      List.getElem?_eq_getElem hbound]
  · simp [outputProbeDecodeNatStep, hactive]

theorem outputProbeDecodeNatStep_ofList_eq_afterBit_internal
    (bits : List Bool) (state : OutputProbeDecodeNatState)
    (hcursor : state.active = true → state.cursor < bits.length) :
    outputProbeDecodeNatStep (FormulaCode.BitOracle.ofList bits) state =
      outputProbeDecodeNatStateAfterBit state
        (outputProbeDecodeNatSourceBit bits state.cursor) := by
  rw [outputProbeDecodeNatStep_ofList_internal bits state hcursor]
  rfl

theorem outputProbeDecodeNatOuterExtrasStep_state_internal
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
        outerExtras (outputProbeDecodeNatStateAfterBit state bit) := by
  have hcursorValuePhysical :
      outputProbeDecodeNatCursorIdx n cursorIdx ≠
        outputProbeDecodeNatValueIdx n valueIdx := by
    intro heq
    exact hcursorValue (outputProbeIndexedControllerIdx_injective n heq)
  have hcursorActivePhysical :
      outputProbeDecodeNatCursorIdx n cursorIdx ≠
        outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hcursorActive (outputProbeIndexedControllerIdx_injective n heq)
  have hvalueActivePhysical :
      outputProbeDecodeNatValueIdx n valueIdx ≠
        outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hvalueActive (outputProbeIndexedControllerIdx_injective n heq)
  by_cases hactiveState : state.active
  · cases bit with
    | false =>
        funext i
        simp only [outputProbeDecodeNatOuterExtrasStep, hactiveState, if_true,
          outputProbeDecodeNatOuterExtrasAfter,
          outputProbeDecodeNatZeroOuterExtras,
          outputProbeDecodeNatStateOuterExtras,
          outputProbeDecodeNatStateAfterBit, Bool.false_eq_true, if_false]
        by_cases hcursor :
            i = outputProbeDecodeNatCursorIdx n cursorIdx
        · subst i
          simp [hcursorActivePhysical, hcursorValuePhysical]
        · by_cases hvalue :
              i = outputProbeDecodeNatValueIdx n valueIdx
          · subst i
            simp [hcursor, hvalueActivePhysical]
          · by_cases hactive :
                i = outputProbeDecodeNatActiveIdx n activeIdx
            · subst i
              simp [hcursor]
            · simp [hcursor, hvalue, hactive]
    | true =>
        funext i
        simp only [outputProbeDecodeNatOuterExtrasStep, hactiveState, if_true,
          outputProbeDecodeNatOuterExtrasAfter,
          outputProbeDecodeNatOneOuterExtras,
          outputProbeDecodeNatStateOuterExtras,
          outputProbeDecodeNatStateAfterBit]
        by_cases hcursor :
            i = outputProbeDecodeNatCursorIdx n cursorIdx
        · subst i
          simp [hcursorActivePhysical, hcursorValuePhysical]
        · by_cases hvalue :
              i = outputProbeDecodeNatValueIdx n valueIdx
          · subst i
            simp [hcursor, hvalueActivePhysical]
          · by_cases hactive :
                i = outputProbeDecodeNatActiveIdx n activeIdx
            · subst i
              simp [hcursor, hvalue]
            · simp [hcursor, hvalue, hactive]
  · simp [outputProbeDecodeNatOuterExtrasStep,
      outputProbeDecodeNatStateAfterBit, hactiveState]

theorem outputProbeDecodeNatRun_succ_internal
    (query : FormulaCode.BitOracle) (fuel : ℕ)
    (state : OutputProbeDecodeNatState) :
    outputProbeDecodeNatRun query (fuel + 1) state =
      outputProbeDecodeNatStep query
        (outputProbeDecodeNatRun query fuel state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simpa [outputProbeDecodeNatRun] using
        ih (outputProbeDecodeNatStep query state)

private theorem outputProbeDecodeNatCounterTape_hasBinaryNat_internal
    (value : ℕ) : (outputProbeCounterTape value).HasBinaryNat value := by
  simpa [outputProbeCounterTape] using
    Tape.init_move_right_hasBinaryNat value

theorem outputProbeDecodeNatStateOuterExtras_cursor_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat state.cursor := by
  have hcursorValuePhysical :
      outputProbeDecodeNatCursorIdx n cursorIdx ≠
        outputProbeDecodeNatValueIdx n valueIdx := by
    intro heq
    exact hcursorValue (outputProbeIndexedControllerIdx_injective n heq)
  have hcursorActivePhysical :
      outputProbeDecodeNatCursorIdx n cursorIdx ≠
        outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hcursorActive (outputProbeIndexedControllerIdx_injective n heq)
  simpa [outputProbeDecodeNatStateOuterExtras, hcursorValuePhysical,
    hcursorActivePhysical] using
    outputProbeDecodeNatCounterTape_hasBinaryNat_internal state.cursor

theorem outputProbeDecodeNatStateOuterExtras_value_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (hvalueActive : valueIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat state.value := by
  have hvalueActivePhysical :
      outputProbeDecodeNatValueIdx n valueIdx ≠
        outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hvalueActive (outputProbeIndexedControllerIdx_injective n heq)
  simpa [outputProbeDecodeNatStateOuterExtras, hvalueActivePhysical] using
    outputProbeDecodeNatCounterTape_hasBinaryNat_internal state.value

theorem outputProbeDecodeNatStateOuterExtras_active_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
      outerExtras state (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat (if state.active then 1 else 0) := by
  simpa [outputProbeDecodeNatStateOuterExtras] using
    outputProbeDecodeNatCounterTape_hasBinaryNat_internal
      (if state.active then 1 else 0)

theorem outputProbeDecodeNatStateOuterExtras_other_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx idx : Fin controllerTapes)
    (hcursor : idx ≠ cursorIdx) (hvalue : idx ≠ valueIdx)
    (hactive : idx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) :
    outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
        outerExtras state (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  have hcursorPhysical : outputProbeIndexedControllerIdx n idx ≠
      outputProbeDecodeNatCursorIdx n cursorIdx := by
    intro heq
    exact hcursor (outputProbeIndexedControllerIdx_injective n heq)
  have hvaluePhysical : outputProbeIndexedControllerIdx n idx ≠
      outputProbeDecodeNatValueIdx n valueIdx := by
    intro heq
    exact hvalue (outputProbeIndexedControllerIdx_injective n heq)
  have hactivePhysical : outputProbeIndexedControllerIdx n idx ≠
      outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hactive (outputProbeIndexedControllerIdx_injective n heq)
  simp [outputProbeDecodeNatStateOuterExtras, hcursorPhysical,
    hvaluePhysical, hactivePhysical]

theorem outputProbeDecodeNatLoopOuterExtras_loop_internal
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
      (outputProbeIndexedControllerIdx n loopIdx)).HasBinaryNat iteration := by
  rw [outputProbeDecodeNatLoopOuterExtras,
    outputProbeDecodeNatStateOuterExtras_other_internal n cursorIdx valueIdx
      activeIdx loopIdx hloopCursor hloopValue hloopActive]
  rw [Function.update_self]
  exact Tape.init_move_right_hasBinaryNat iteration

/-- Canonical decoder-register contents make the loop-frame normalization a
literal no-op. -/
theorem outputProbeDecodeNatLoopOuterExtras_eq_self_internal
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
      outerExtras state iteration = outerExtras := by
  have hcursorEq : outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx) =
      outputProbeCounterTape state.cursor := by
    simpa [outputProbeCounterTape] using hcursor.eq_init_move_right
  have hvalueEq : outerExtras (outputProbeDecodeNatValueIdx n valueIdx) =
      outputProbeCounterTape state.value := by
    simpa [outputProbeCounterTape] using hvalue.eq_init_move_right
  have hactiveEq : outerExtras (outputProbeDecodeNatActiveIdx n activeIdx) =
      outputProbeCounterTape (if state.active then 1 else 0) := by
    simpa [outputProbeCounterTape] using hactive.eq_init_move_right
  have hloopEq : outerExtras (outputProbeIndexedControllerIdx n loopIdx) =
      outputProbeCounterTape iteration := by
    simpa [outputProbeCounterTape] using hloop.eq_init_move_right
  rw [outputProbeDecodeNatLoopOuterExtras,
    outputProbeDecodeNatStateOuterExtras]
  rw [← hloopEq, Function.update_eq_self]
  rw [← hcursorEq, Function.update_eq_self]
  rw [← hvalueEq, Function.update_eq_self]
  rw [← hactiveEq, Function.update_eq_self]

private theorem outputProbeDecodeNatCounterTape_parked_internal
    (value : ℕ) : Parked (outputProbeCounterTape value) := by
  have h : (outputProbeCounterTape value).HasBinaryNat value := by
    simpa [outputProbeCounterTape] using
      Tape.init_move_right_hasBinaryNat value
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem outputProbeDecodeNatUpdateOuter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (idx : Fin controllerTapes) (value : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (Function.update outerExtras
        (outputProbeIndexedControllerIdx n idx)
        (outputProbeCounterTape value) i) := by
  intro i hi
  by_cases heq : i = outputProbeIndexedControllerIdx n idx
  · subst i
    rw [Function.update_self]
    exact outputProbeDecodeNatCounterTape_parked_internal value
  · rw [Function.update_of_ne heq]
    exact houter i hi

theorem outputProbeDecodeNatStateOuterExtras_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (state : OutputProbeDecodeNatState) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx
        activeIdx outerExtras state i) := by
  have hcursor := outputProbeDecodeNatUpdateOuter_parked_internal n
    outerExtras houter cursorIdx state.cursor
  have hvalue := outputProbeDecodeNatUpdateOuter_parked_internal n
    (Function.update outerExtras (outputProbeDecodeNatCursorIdx n cursorIdx)
      (outputProbeCounterTape state.cursor)) hcursor valueIdx state.value
  have hactive := outputProbeDecodeNatUpdateOuter_parked_internal n
    (Function.update
      (Function.update outerExtras
        (outputProbeDecodeNatCursorIdx n cursorIdx)
        (outputProbeCounterTape state.cursor))
      (outputProbeDecodeNatValueIdx n valueIdx)
      (outputProbeCounterTape state.value)) hvalue activeIdx
    (if state.active then 1 else 0)
  simpa [outputProbeDecodeNatStateOuterExtras,
    outputProbeDecodeNatCursorIdx, outputProbeDecodeNatValueIdx,
    outputProbeDecodeNatActiveIdx] using hactive

theorem outputProbeDecodeNatLoopOuterExtras_parked_internal
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
        activeIdx loopIdx outerExtras state iteration i) := by
  have hloop := outputProbeDecodeNatUpdateOuter_parked_internal n
    outerExtras houter loopIdx iteration
  exact outputProbeDecodeNatStateOuterExtras_parked_internal n cursorIdx
    valueIdx activeIdx
    (Function.update outerExtras (outputProbeIndexedControllerIdx n loopIdx)
      (outputProbeCounterTape iteration)) hloop state

theorem outputProbeDecodeNatLoopOuterExtras_other_internal
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
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  rw [outputProbeDecodeNatLoopOuterExtras,
    outputProbeDecodeNatStateOuterExtras_other_internal n cursorIdx valueIdx
      activeIdx idx hcursor hvalue hactive]
  rw [Function.update_of_ne]
  intro heq
  exact hloop (outputProbeIndexedControllerIdx_injective n heq)

theorem outputProbeDecodeNatFrameCfg_post_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    outputProbeLatchFramePost tm controllerTapes
      (outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
        loopIdx outerExtras
        (outputProbeDecodeNatStateAt bits initial iteration) iteration)
      input output extras false
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).input
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).work
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).output := by
  exact outputProbeLatchFrameCfg_post tm controllerTapes _ input output extras
    false

theorem outputProbeDecodeNatFrameCfg_parked_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houtput : Parked output)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    Parked (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
      activeIdx loopIdx outerExtras bits input output extras initial
      iteration).input ∧
      (∀ i, Parked
        ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
          activeIdx loopIdx outerExtras bits input output extras initial
          iteration).work i)) ∧
      Parked (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).output := by
  exact outputProbeLatchFramePost_parked tm controllerTapes _ input output
    extras false hextras
    (outputProbeDecodeNatLoopOuterExtras_parked_internal n cursorIdx valueIdx
      activeIdx loopIdx outerExtras houter
      (outputProbeDecodeNatStateAt bits initial iteration) iteration)
    houtput _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)

theorem outputProbeDecodeNatFrameCfg_cursor_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
      activeIdx loopIdx outerExtras bits input output extras initial
      iteration).work (outputProbeDecodeNatCursorIdx n cursorIdx))
        |>.HasBinaryNat
          (outputProbeDecodeNatStateAt bits initial iteration).cursor := by
  change ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
    activeIdx loopIdx outerExtras bits input output extras initial
    iteration).work (outputProbeIndexedControllerIdx n cursorIdx))
      |>.HasBinaryNat
        (outputProbeDecodeNatStateAt bits initial iteration).cursor
  rw [outputProbeLatchFramePost_controller tm controllerTapes _ input output
    extras false _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)
    cursorIdx]
  exact outputProbeDecodeNatStateOuterExtras_cursor_internal n cursorIdx
    valueIdx activeIdx hcursorValue hcursorActive _ _

theorem outputProbeDecodeNatFrameCfg_value_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (hvalueActive : valueIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
      activeIdx loopIdx outerExtras bits input output extras initial
      iteration).work (outputProbeDecodeNatValueIdx n valueIdx))
        |>.HasBinaryNat
          (outputProbeDecodeNatStateAt bits initial iteration).value := by
  change ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
    activeIdx loopIdx outerExtras bits input output extras initial
    iteration).work (outputProbeIndexedControllerIdx n valueIdx))
      |>.HasBinaryNat
        (outputProbeDecodeNatStateAt bits initial iteration).value
  rw [outputProbeLatchFramePost_controller tm controllerTapes _ input output
    extras false _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)
    valueIdx]
  exact outputProbeDecodeNatStateOuterExtras_value_internal n cursorIdx
    valueIdx activeIdx hvalueActive _ _

theorem outputProbeDecodeNatFrameCfg_active_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
      activeIdx loopIdx outerExtras bits input output extras initial
      iteration).work (outputProbeDecodeNatActiveIdx n activeIdx))
        |>.HasBinaryNat
          (if (outputProbeDecodeNatStateAt bits initial iteration).active then
            1 else 0) := by
  change ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
    activeIdx loopIdx outerExtras bits input output extras initial
    iteration).work (outputProbeIndexedControllerIdx n activeIdx))
      |>.HasBinaryNat
        (if (outputProbeDecodeNatStateAt bits initial iteration).active then
          1 else 0)
  rw [outputProbeLatchFramePost_controller tm controllerTapes _ input output
    extras false _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)
    activeIdx]
  exact outputProbeDecodeNatStateOuterExtras_active_internal n cursorIdx
    valueIdx activeIdx _ _

theorem outputProbeDecodeNatFrameCfg_loop_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (hloopCursor : loopIdx ≠ cursorIdx)
    (hloopValue : loopIdx ≠ valueIdx)
    (hloopActive : loopIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    ((outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
      activeIdx loopIdx outerExtras bits input output extras initial
      iteration).work (outputProbeIndexedControllerIdx n loopIdx))
        |>.HasBinaryNat iteration := by
  rw [outputProbeLatchFramePost_controller tm controllerTapes _ input output
    extras false _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)
    loopIdx]
  exact outputProbeDecodeNatLoopOuterExtras_loop_internal n cursorIdx valueIdx
    activeIdx loopIdx hloopCursor hloopValue hloopActive outerExtras _ iteration

theorem outputProbeDecodeNatFrameCfg_other_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx valueIdx activeIdx loopIdx idx : Fin controllerTapes)
    (hcursor : idx ≠ cursorIdx) (hvalue : idx ≠ valueIdx)
    (hactive : idx ≠ activeIdx) (hloop : idx ≠ loopIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ) :
    (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).work (outputProbeIndexedControllerIdx n idx) =
      outerExtras (outputProbeIndexedControllerIdx n idx) := by
  rw [outputProbeLatchFramePost_controller tm controllerTapes _ input output
    extras false _ _ _
    (outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      iteration)
    idx]
  exact outputProbeDecodeNatLoopOuterExtras_other_internal n cursorIdx valueIdx
    activeIdx loopIdx idx hcursor hvalue hactive hloop outerExtras _ iteration

theorem outputProbeDecodeNatStateAt_succ_internal
    (bits : List Bool) (initial : OutputProbeDecodeNatState) (iteration : ℕ)
    (hcursor : (outputProbeDecodeNatStateAt bits initial iteration).active =
      true →
      (outputProbeDecodeNatStateAt bits initial iteration).cursor <
        bits.length) :
    outputProbeDecodeNatStateAt bits initial (iteration + 1) =
      outputProbeDecodeNatStateAfterBit
        (outputProbeDecodeNatStateAt bits initial iteration)
        (outputProbeDecodeNatSourceBit bits
          (outputProbeDecodeNatStateAt bits initial iteration).cursor) := by
  rw [outputProbeDecodeNatStateAt, outputProbeDecodeNatRun_succ_internal]
  exact outputProbeDecodeNatStep_ofList_eq_afterBit_internal bits _ hcursor

theorem outputProbeDecodeNatLoopOuterExtras_step_internal
    (n : ℕ) {controllerTapes : ℕ}
    (cursorIdx valueIdx activeIdx loopIdx : Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hvalueActive : valueIdx ≠ activeIdx)
    (hloopCursor : loopIdx ≠ cursorIdx)
    (hloopValue : loopIdx ≠ valueIdx)
    (hloopActive : loopIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (iteration : ℕ) (bit : Bool) :
    Function.update
        (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
          (outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
            loopIdx outerExtras state iteration)
          state bit)
        (outputProbeIndexedControllerIdx n loopIdx)
        (outputProbeCounterTape (iteration + 1)) =
      outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
        loopIdx outerExtras (outputProbeDecodeNatStateAfterBit state bit)
        (iteration + 1) := by
  rw [outputProbeDecodeNatLoopOuterExtras,
    outputProbeDecodeNatOuterExtrasStep_state_internal n cursorIdx valueIdx
      activeIdx hcursorValue hcursorActive hvalueActive]
  funext i
  have hloopCursorPhysical : outputProbeIndexedControllerIdx n loopIdx ≠
      outputProbeDecodeNatCursorIdx n cursorIdx := by
    intro heq
    exact hloopCursor (outputProbeIndexedControllerIdx_injective n heq)
  have hloopValuePhysical : outputProbeIndexedControllerIdx n loopIdx ≠
      outputProbeDecodeNatValueIdx n valueIdx := by
    intro heq
    exact hloopValue (outputProbeIndexedControllerIdx_injective n heq)
  have hloopActivePhysical : outputProbeIndexedControllerIdx n loopIdx ≠
      outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hloopActive (outputProbeIndexedControllerIdx_injective n heq)
  have hcursorValuePhysical : outputProbeDecodeNatCursorIdx n cursorIdx ≠
      outputProbeDecodeNatValueIdx n valueIdx := by
    intro heq
    exact hcursorValue (outputProbeIndexedControllerIdx_injective n heq)
  have hcursorActivePhysical : outputProbeDecodeNatCursorIdx n cursorIdx ≠
      outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hcursorActive (outputProbeIndexedControllerIdx_injective n heq)
  have hvalueActivePhysical : outputProbeDecodeNatValueIdx n valueIdx ≠
      outputProbeDecodeNatActiveIdx n activeIdx := by
    intro heq
    exact hvalueActive (outputProbeIndexedControllerIdx_injective n heq)
  by_cases hloop : i = outputProbeIndexedControllerIdx n loopIdx
  · subst i
    simp [outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatStateOuterExtras, hloopCursorPhysical,
      hloopValuePhysical, hloopActivePhysical]
  · by_cases hcursor : i = outputProbeDecodeNatCursorIdx n cursorIdx
    · subst i
      rw [Function.update_of_ne hloop]
      simp [outputProbeDecodeNatLoopOuterExtras,
        outputProbeDecodeNatStateOuterExtras,
        hcursorValuePhysical, hcursorActivePhysical]
    · by_cases hvalue : i = outputProbeDecodeNatValueIdx n valueIdx
      · subst i
        rw [Function.update_of_ne hloop]
        simp [outputProbeDecodeNatLoopOuterExtras,
          outputProbeDecodeNatStateOuterExtras,
          hvalueActivePhysical]
      · by_cases hactive : i = outputProbeDecodeNatActiveIdx n activeIdx
        · subst i
          rw [Function.update_of_ne hloop]
          simp [outputProbeDecodeNatLoopOuterExtras,
            outputProbeDecodeNatStateOuterExtras]
        · simp [outputProbeDecodeNatLoopOuterExtras,
            outputProbeDecodeNatStateOuterExtras, hloop, hcursor, hvalue,
            hactive]

private theorem outputProbeDecodeNatSucc_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes) (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat
        value) :
    (binarySuccTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape (value + 1)))
        input output extras false)
      (binarySuccTime value) := by
  let physical := outputProbeIndexedControllerIdx n idx
  let nextTape := outputProbeCounterTape (value + 1)
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htarget : (work physical).HasBinaryNat value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hvalue
  obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, htargetDone,
      houtputDone⟩ :=
    binarySuccTM_reachesIn_frame physical value inp work out htarget
      hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkDone : done.work = Function.update work physical nextTape := by
    funext i
    by_cases hi : i = physical
    · subst i
      rw [Function.update_self]
      exact htargetDone.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hotherDone i hi
  refine ⟨done, binarySuccTime value, le_rfl, hreach, hhalt, ?_⟩
  rw [hinputDone, hworkDone, houtputDone]
  simpa [physical, nextTape] using
    outputProbeLatchFramePost_updateController tm controllerTapes outerExtras
      input output extras false inp work out hpost idx nextTape

private theorem outputProbeDecodeNatClear_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes)
    (hone :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat 1) :
    (clearWorkTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape 0))
        input output extras false)
      (clearWorkTimeBound 1) := by
  let physical := outputProbeIndexedControllerIdx n idx
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htargetNat : (work physical).HasBinaryNat 1 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hone
  have htarget : work physical =
      (Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right :=
    htargetNat.eq_init_move_right
  have hclear := clearWorkTM_hoareTime_frame physical (1 : ℕ).bits inp work out
    htarget hinput (fun i _ => hwork i) hout
  obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone, hworkDone,
      houtputDone⟩ := hclear inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨done, elapsed, ?_, hreach, hhalt, ?_⟩
  · simpa using helapsed
  · rw [hinputDone, hworkDone, houtputDone]
    simpa [physical, outputProbeCounterTape] using
      outputProbeLatchFramePost_updateController tm controllerTapes
        outerExtras input output extras false inp work out hpost idx
        (outputProbeCounterTape 0)

theorem outputProbeDecodeNatZeroTM_hoareTime_internal
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
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor) := by
  let activePhysical := outputProbeDecodeNatActiveIdx n activeIdx
  let cursorPhysical := outputProbeDecodeNatCursorIdx n cursorIdx
  let clearedOuter := Function.update outerExtras activePhysical
    (outputProbeCounterTape 0)
  have hphysical : cursorPhysical ≠ activePhysical := by
    intro heq
    exact hdistinct
      (outputProbeIndexedControllerIdx_injective n heq)
  have hclear := outputProbeDecodeNatClear_hoareTime_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    activeIdx hactive
  have hclearedParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (clearedOuter i) :=
    outputProbeDecodeNatUpdateOuter_parked_internal n outerExtras houter
      activeIdx 0
  have hclearedCursor : (clearedOuter cursorPhysical).HasBinaryNat cursor := by
    dsimp only [clearedOuter]
    rw [Function.update_of_ne hphysical]
    exact hcursor
  have hsucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes clearedOuter input output extras hextras hclearedParked
    houtput cursorIdx cursor hclearedCursor
  apply seqTM_hoareTime _ _ hclear
  · intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes clearedOuter input output extras false hextras
      hclearedParked houtput inp work out hpost
    obtain ⟨hinpEq, hworkEq, houtEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinp.read_ne_start
        (fun i => (hwork i).read_ne_start) hout.read_ne_start
    simpa [hinpEq, hworkEq, houtEq] using hpost
  · simpa [outputProbeDecodeNatZeroTM,
      outputProbeDecodeNatZeroOuterExtras, clearedOuter, activePhysical,
      cursorPhysical] using hsucc

theorem outputProbeDecodeNatOneTM_hoareTime_internal
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
      (binarySuccTime value + 1 + binarySuccTime cursor) := by
  let valuePhysical := outputProbeDecodeNatValueIdx n valueIdx
  let cursorPhysical := outputProbeDecodeNatCursorIdx n cursorIdx
  let incrementedOuter := Function.update outerExtras valuePhysical
    (outputProbeCounterTape (value + 1))
  have hphysical : cursorPhysical ≠ valuePhysical := by
    intro heq
    exact hdistinct
      (outputProbeIndexedControllerIdx_injective n heq)
  have hvalueSucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes outerExtras input output extras hextras houter houtput
    valueIdx value hvalue
  have hincrementedParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (incrementedOuter i) :=
    outputProbeDecodeNatUpdateOuter_parked_internal n outerExtras houter
      valueIdx (value + 1)
  have hincrementedCursor :
      (incrementedOuter cursorPhysical).HasBinaryNat cursor := by
    dsimp only [incrementedOuter]
    rw [Function.update_of_ne hphysical]
    exact hcursor
  have hcursorSucc := outputProbeDecodeNatSucc_hoareTime_internal tm
    controllerTapes incrementedOuter input output extras hextras
    hincrementedParked houtput cursorIdx cursor hincrementedCursor
  apply seqTM_hoareTime _ _ hvalueSucc
  · intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes incrementedOuter input output extras false hextras
      hincrementedParked houtput inp work out hpost
    obtain ⟨hinpEq, hworkEq, houtEq⟩ :=
      phaseTransition_eq_self_of_reads_ne_start hinp.read_ne_start
        (fun i => (hwork i).read_ne_start) hout.read_ne_start
    simpa [hinpEq, hworkEq, houtEq] using hpost
  · simpa [outputProbeDecodeNatOneTM,
      outputProbeDecodeNatOneOuterExtras, incrementedOuter, valuePhysical,
      cursorPhysical] using hcursorSucc

theorem outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal
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
              (clearWorkTimeBound 1 + 1 + binarySuccTime cursor))) := by
  have hzeroTime := outputProbeDecodeNatZeroTM_hoareTime_internal tm
    controllerTapes cursorIdx activeIdx hcursorActive outerExtras input output
    extras hextras houter houtput cursor hcursor hactive
  have hzero := hzeroTime.toHoareTimeSpace hzeroInitial
  have honeTime := outputProbeDecodeNatOneTM_hoareTime_internal tm
    controllerTapes cursorIdx valueIdx hcursorValue outerExtras input output
    extras hextras houter houtput cursor value hcursor hvalue
  have hone := honeTime.toHoareTimeSpace honeInitial
  simpa [outputProbeDecodeNatActiveTM,
    outputProbeDecodeNatOuterExtrasAfter] using
    outputProbeIndexedResetDispatchTM_of_latch_hoareTimeSpace tm
      controllerTapes cursorIdx scratchIdx outerExtras input output extras bit
      hextras houter houtput
      (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx activeIdx)
      (outputProbeDecodeNatOneTM n controllerTapes cursorIdx valueIdx)
      (post := fun branch =>
        outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasAfter n cursorIdx valueIdx activeIdx
            outerExtras cursor value branch)
          input output extras false)
      hlatch hclearInitial hzero hone

theorem ComputesInSpace.outputProbeDecodeNatActiveTM_hoareTime_internal
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
          bodyBound := by
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  let queryFrame := placeWorkCfg (outputProbePlacedTM tm) 0 controllerTapes
    outerExtras
    (outputProbePlacedFrameCfg tm input
      (outputProbeCounterTape (cursor + 1)) output extras)
  let frameSpace := Finset.univ.sup fun i => (extras i).head
  let outerFrameSpace := Finset.univ.sup fun i => (outerExtras i).head
  let initialSpace := Finset.univ.sup fun i => (frame.work i).head
  let pre : TapePred
      (0 + outputProbeControllerTapes n + controllerTapes) :=
    fun inp work out =>
      inp = queryFrame.input ∧ work = frame.work ∧ out = output
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  have hparked := outputProbeLatchFramePost_parked tm controllerTapes
    outerExtras input output extras false hextras houter houtput frame.input
    frame.work frame.output hframePost
  have hframeBound : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i →
      (extras i).head ≤ frameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (extras j).head)
      (Finset.mem_univ i)
  have houterRead : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).read ≠ Γ.start := by
    intro i hi
    exact (houter i hi).read_ne_start
  have houterBound : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        (outerExtras i).head ≤ outerFrameSpace := by
    intro i _hi
    exact Finset.le_sup (f := fun j => (outerExtras j).head)
      (Finset.mem_univ i)
  have hworkBound : ∀ i, (frame.work i).head ≤ initialSpace := by
    intro i
    exact Finset.le_sup (f := fun j => (frame.work j).head)
      (Finset.mem_univ i)
  have hqueryInput : queryFrame.input = frame.input := by
    rfl
  have hqueryOutput : frame.output = output := by
    simp [frame, outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
      outputProbePlacedFrameCfg]
  have hcursorWork :
      (frame.work (outputProbeIndexedControllerIdx n cursorIdx))
        |>.HasBinaryNat cursor := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      cursorIdx]
    exact hcursor
  have hscratchWork :
      (frame.work (outputProbeIndexedControllerIdx n scratchIdx))
        |>.HasBinaryNat 0 := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      scratchIdx]
    exact hscratch
  have hframeWork : frame.work = Function.update queryFrame.work
      (outputProbeIndexedCountdownIdx n controllerTapes)
      (outputProbeCounterTape 0) := by
    exact outputProbeLatchFrameCfg_work_eq_queryUpdate tm input output extras
      hcleanupCounter controllerTapes cursor outerExtras
  have hcountdown :
      (frame.work (outputProbeIndexedCountdownIdx n controllerTapes))
        |>.HasBinaryNat 0 := by
    rw [hframeWork, Function.update_self]
    exact Tape.init_move_right_hasBinaryNat 0
  have hqueryWork : ∀ i,
      i ≠ outputProbeIndexedCountdownIdx n controllerTapes →
      frame.work i = queryFrame.work i := by
    intro i hi
    rw [hframeWork, Function.update_of_ne hi]
  have hinputSpace : queryFrame.input.head ≤
      input.length + initialSpace + 1 := by
    simp [queryFrame, outputProbePlacedFrameCfg, outputProbeStartedCfg,
      Tape.move]
  obtain ⟨latchTime, hlatch⟩ :=
    hcomp.outputProbeIndexedLatchTM_hoareTimeSpace input cursor hcursorBound
      output houtput extras frameSpace cleanupLimit hextras hframeBound
      hcleanupCounter hcleanupLimit hlimit controllerTapes outerExtras
      outerFrameSpace houterRead houterBound cursorIdx scratchIdx
      hcursorScratch initialSpace frame.work hcursorWork hcountdown
      hscratchWork (hqueryInput ▸ hparked.1) hparked.2.1 hworkBound hinputSpace
      hqueryWork
  let falseFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras false
  let trueFrame := outputProbeLatchFrameCfg tm controllerTapes outerExtras
    input output extras true
  let falseSpace := Finset.univ.sup fun i => (falseFrame.work i).head
  let trueSpace := Finset.univ.sup fun i => (trueFrame.work i).head
  have hframeInitial (bit : Bool) : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras bit inp work out →
      ({ state := (skipTM (n := 0 + outputProbeControllerTapes n +
              controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (skipTM (n := 0 + outputProbeControllerTapes n +
            controllerTapes)).Q).WithinAuxSpace input.length
          (Finset.univ.sup fun i =>
            ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
              output extras bit).work i).head) := by
    intro inp work out hpost
    obtain ⟨hinp, hwork, _hout⟩ := outputProbeLatchFramePost_eq_frameCfg tm
      controllerTapes outerExtras input output extras bit inp work out hpost
    subst inp
    subst work
    constructor
    · intro i
      exact Finset.le_sup
        (f := fun j =>
          ((outputProbeLatchFrameCfg tm controllerTapes outerExtras input
            output extras bit).work j).head)
        (Finset.mem_univ i)
    · simp [outputProbeLatchFrameCfg, outputProbeLatchInnerFrameCfg,
        outputProbePlacedFrameCfg, outputProbeStartedCfg, Tape.move]
  have hclearInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras true inp work out →
      ({ state := (clearWorkTM
              (outputProbeLatchIdx n controllerTapes)).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (clearWorkTM (outputProbeLatchIdx n controllerTapes)).Q
        ).WithinAuxSpace input.length trueSpace := by
    simpa [trueSpace, trueFrame] using hframeInitial true
  have hzeroInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
              activeIdx).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
            activeIdx).Q).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  have honeInitial : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
      ({ state := (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
              valueIdx).qstart
         input := inp
         work := work
         output := out } :
        Cfg (0 + outputProbeControllerTapes n + controllerTapes)
          (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
            valueIdx).Q).WithinAuxSpace input.length falseSpace := by
    simpa [falseSpace, falseFrame] using hframeInitial false
  let bodyBound := outputProbeIndexedPrepareTime cursor + 1 + latchTime + 1 +
    outputProbeLatchDispatchTime ((f input)[cursor]'hcursorBound)
      (clearWorkTimeBound 1 + 1 + binarySuccTime cursor)
      (clearWorkTimeBound 1 + 1 +
        (binarySuccTime value + 1 + binarySuccTime cursor))
  have hbody :=
    outputProbeDecodeNatActiveTM_of_latch_hoareTimeSpace_internal tm
      controllerTapes cursorIdx scratchIdx valueIdx activeIdx hcursorValue
      hcursorActive outerExtras input output extras
      ((f input)[cursor]'hcursorBound) hextras houter houtput cursor value
      hcursor hvalue hactive hlatch hclearInitial hzeroInitial honeInitial
  refine ⟨bodyBound, pre, ?_, ?_, ?_⟩
  · intro inp work out hpre
    exact ⟨hpre.1.trans hqueryInput, hpre.2.1,
      hpre.2.2.trans hqueryOutput.symm⟩
  · exact ⟨hqueryInput.symm, rfl, hqueryOutput⟩
  · simpa [bodyBound] using hbody.1

theorem ComputesInSpace.outputProbeDecodeNatBodyTM_active_hoareTime_internal
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
          bodyBound := by
  obtain ⟨activeBound, pre, hpreExact, hpre, hactiveRun⟩ :=
    hcomp.outputProbeDecodeNatActiveTM_hoareTime_internal input cursor
      hcursorBound output houtput extras hextras hcleanupCounter cleanupLimit
      hcleanupLimit hlimit controllerTapes outerExtras houter cursorIdx
      scratchIdx valueIdx activeIdx hcursorScratch hcursorValue hcursorActive
      hcursor hscratch value hvalue hactive
  let frame := outputProbeLatchFrameCfg tm controllerTapes outerExtras input
    output extras false
  have hframePost := outputProbeLatchFrameCfg_post tm controllerTapes
    outerExtras input output extras false
  have hparked := outputProbeLatchFramePost_parked tm controllerTapes
    outerExtras input output extras false hextras houter houtput frame.input
    frame.work frame.output hframePost
  let activePhysical := outputProbeDecodeNatActiveIdx n activeIdx
  have hactiveFrame : (frame.work activePhysical).HasBinaryNat 1 := by
    dsimp only [activePhysical, outputProbeDecodeNatActiveIdx]
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false frame.input frame.work frame.output hframePost
      activeIdx]
    exact hactive
  have hactiveRead : (frame.work activePhysical).read = Γ.one := by
    rw [hactiveFrame.eq_init_move_right]
    rfl
  have hbody := branchWorkSymbolTM_hoareTime_equal activePhysical Γ.one
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx)
    skipTM
    (fun inp work out hp => by
      rw [(hpreExact inp work out hp).2.1]
      exact hactiveRead)
    (fun inp work out hp => by
      rw [(hpreExact inp work out hp).1]
      exact hparked.1.read_ne_start)
    (fun inp work out hp i => by
      rw [(hpreExact inp work out hp).2.1]
      exact (hparked.2.1 i).read_ne_start)
    (fun inp work out hp => by
      rw [(hpreExact inp work out hp).2.2]
      exact hparked.2.2.read_ne_start)
    hactiveRun
  refine ⟨activeBound + 1, pre, hpre, ?_⟩
  simpa [outputProbeDecodeNatBodyTM, activePhysical] using hbody

theorem outputProbeDecodeNatBodyTM_inactive_hoareTime_internal
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
        2 := by
  let activePhysical := outputProbeDecodeNatActiveIdx n activeIdx
  have hinactiveController :
      (outerExtras (outputProbeIndexedControllerIdx n activeIdx))
        |>.HasBinaryNat 0 := by
    simpa [outputProbeDecodeNatActiveIdx] using hinactive
  have hskip : (skipTM (n := 0 + outputProbeControllerTapes n +
      controllerTapes)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      1 := by
    intro inp work out hpost
    obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes outerExtras input output extras false hextras houter
      houtput inp work out hpost
    obtain ⟨done, elapsed, helapsed, hreach, hhalt, hinputDone, hworkDone,
        houtputDone⟩ :=
      skipTM_hoareTime_frame inp work out hinput hwork hout inp work out
        ⟨rfl, rfl, rfl⟩
    refine ⟨done, elapsed, helapsed, hreach, hhalt, ?_⟩
    simpa [hinputDone, hworkDone, houtputDone] using hpost
  have hbody := branchWorkSymbolTM_hoareTime_different activePhysical Γ.one
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx)
    skipTM
    (fun inp work out hpost => by
      have hcontroller := outputProbeLatchFramePost_controller tm
        controllerTapes outerExtras input output extras false inp work out
        hpost activeIdx
      dsimp only [activePhysical, outputProbeDecodeNatActiveIdx]
      rw [hcontroller, hinactiveController.eq_init_move_right]
      decide)
    (fun inp work out hpost =>
      (outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
        output extras false hextras houter houtput inp work out hpost).1
        |>.read_ne_start)
    (fun inp work out hpost i =>
      ((outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
        output extras false hextras houter houtput inp work out hpost).2.1 i)
        |>.read_ne_start)
    (fun inp work out hpost =>
      (outputProbeLatchFramePost_parked tm controllerTapes outerExtras input
        output extras false hextras houter houtput inp work out hpost).2.2
        |>.read_ne_start)
    hskip
  simpa [outputProbeDecodeNatBodyTM, activePhysical] using hbody

theorem ComputesInSpace.outputProbeDecodeNatBodyTM_hoareTime_internal
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
          bodyBound := by
  by_cases hactiveState : state.active
  · have hbound := hcursorBound hactiveState
    have hlimitState := hlimit hactiveState
    have hactiveOne :
        (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
          |>.HasBinaryNat 1 := by
      simpa [hactiveState] using hactive
    obtain ⟨bodyBound, pre, hpre, hbody⟩ :=
      hcomp.outputProbeDecodeNatBodyTM_active_hoareTime_internal input
        state.cursor hbound output houtput extras hextras hcleanupCounter
        cleanupLimit hcleanupLimit hlimitState controllerTapes outerExtras
        houter cursorIdx scratchIdx valueIdx activeIdx hcursorScratch
        hcursorValue hcursorActive hcursor hscratch state.value hvalue
        hactiveOne
    have hbit : outputProbeDecodeNatSourceBit (f input) state.cursor =
        (f input)[state.cursor] := by
      simp [outputProbeDecodeNatSourceBit,
        List.getElem?_eq_getElem hbound]
    refine ⟨bodyBound, pre, hpre, ?_⟩
    simpa [outputProbeDecodeNatOuterExtrasStep, hactiveState, hbit] using
      hbody
  · have hinactiveZero :
        (outerExtras (outputProbeDecodeNatActiveIdx n activeIdx))
          |>.HasBinaryNat 0 := by
      simpa [hactiveState] using hactive
    let pre := outputProbeLatchFramePost tm controllerTapes outerExtras input
      output extras false
    have hpre := outputProbeLatchFrameCfg_post tm controllerTapes outerExtras
      input output extras false
    have hbody := outputProbeDecodeNatBodyTM_inactive_hoareTime_internal tm
      controllerTapes cursorIdx scratchIdx valueIdx activeIdx outerExtras
      input output extras hextras houter houtput hinactiveZero
    refine ⟨2, pre, ?_, ?_⟩
    · exact hpre
    · simpa [pre, outputProbeDecodeNatOuterExtrasStep, hactiveState] using
        hbody

private theorem outputProbeDecodeNatBinarySuccCanonical_reachesIn_internal
    (idx : Fin n) (value : ℕ)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (hvalue : (work idx).HasBinaryNat value)
    (hinp : Parked inp) (hwork : ∀ i, Parked (work i))
    (hout : Parked out) :
    (binarySuccTM idx).reachesIn (binarySuccTime value)
      { state := (binarySuccTM idx).qstart
        input := inp
        work := work
        output := out }
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (outputProbeCounterTape (value + 1))
        output := out } := by
  obtain ⟨done, hreach, hhalt, hinput, hother, htarget, houtput⟩ :=
    binarySuccTM_reachesIn_frame idx value inp work out hvalue
      hinp.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkEq : done.work = Function.update work idx
      (outputProbeCounterTape (value + 1)) := by
    funext i
    by_cases hi : i = idx
    · subst i
      simp only [Function.update_self]
      simpa [outputProbeCounterTape] using htarget.eq_init_move_right
    · rw [Function.update_of_ne hi, hother i hi]
  have hdone : done =
      { state := (binarySuccTM idx).qhalt
        input := inp
        work := Function.update work idx
          (outputProbeCounterTape (value + 1))
        output := out } :=
    Cfg.ext hhalt hinput hworkEq houtput
  simpa [hdone] using hreach

theorem outputProbeDecodeNatBodyTM_reachesIn_frame_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (state : OutputProbeDecodeNatState) (bit : Bool)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyBound : ℕ}
    (hpre : pre
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).input
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).work
      (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
        extras false).output)
    (hbody : (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
      scratchIdx valueIdx activeIdx).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
            outerExtras state bit)
          input output extras false)
        bodyBound) :
    ∃ time, time ≤ bodyBound ∧
      (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
        valueIdx activeIdx).reachesIn time
        { state := (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
              scratchIdx valueIdx activeIdx).qstart
          input := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).input
          work := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).work
          output := (outputProbeLatchFrameCfg tm controllerTapes outerExtras
            input output extras false).output }
        { state := (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
              scratchIdx valueIdx activeIdx).qhalt
          input := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
              outerExtras state bit)
            input output extras false).input
          work := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
              outerExtras state bit)
            input output extras false).work
          output := (outputProbeLatchFrameCfg tm controllerTapes
            (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
              outerExtras state bit)
            input output extras false).output } := by
  obtain ⟨done, time, htime, hreach, hhalt, hpost⟩ := hbody _ _ _ hpre
  obtain ⟨hinput, hwork, houtput⟩ :=
    outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
      (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
        outerExtras state bit)
      input output extras false done.input done.work done.output hpost
  have hdone : done =
      { state := (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
            scratchIdx valueIdx activeIdx).qhalt
        input := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
            outerExtras state bit)
          input output extras false).input
        work := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
            outerExtras state bit)
          input output extras false).work
        output := (outputProbeLatchFrameCfg tm controllerTapes
          (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
            outerExtras state bit)
          input output extras false).output } :=
    Cfg.ext hhalt hinput hwork houtput
  exact ⟨time, htime, hdone ▸ hreach⟩

theorem outputProbeDecodeNatIteration_reachesIn_of_body_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes)
    (hcursorValue : cursorIdx ≠ valueIdx)
    (hcursorActive : cursorIdx ≠ activeIdx)
    (hvalueActive : valueIdx ≠ activeIdx)
    (hloopCursor : loopIdx ≠ cursorIdx)
    (hloopValue : loopIdx ≠ valueIdx)
    (hloopActive : loopIdx ≠ activeIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (bits input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output)
    (initial : OutputProbeDecodeNatState) (iteration : ℕ)
    (hcursorBound :
      (outputProbeDecodeNatStateAt bits initial iteration).active = true →
      (outputProbeDecodeNatStateAt bits initial iteration).cursor <
        bits.length)
    {pre : TapePred (0 + outputProbeControllerTapes n + controllerTapes)}
    {bodyBound : ℕ}
    (hpre : pre
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).input
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).work
      (outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx valueIdx
        activeIdx loopIdx outerExtras bits input output extras initial
        iteration).output)
    (hbody : (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
      scratchIdx valueIdx activeIdx).HoareTime pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx activeIdx
            (outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
              loopIdx outerExtras
              (outputProbeDecodeNatStateAt bits initial iteration) iteration)
            (outputProbeDecodeNatStateAt bits initial iteration)
            (outputProbeDecodeNatSourceBit bits
              (outputProbeDecodeNatStateAt bits initial iteration).cursor))
          input output extras false)
        bodyBound) :
    ∃ time, time ≤ bodyBound + 1 + binarySuccTime iteration ∧
      (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx valueIdx
        activeIdx loopIdx fuelIdx).reachesIn time
        (outputProbeDecodeNatIterationStartCfg tm controllerTapes cursorIdx
          scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits input
          output extras initial iteration)
        (outputProbeDecodeNatIterationDoneCfg tm controllerTapes cursorIdx
          scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits input
          output extras initial iteration) := by
  let state := outputProbeDecodeNatStateAt bits initial iteration
  let currentOuter := outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx
    activeIdx loopIdx outerExtras state iteration
  let bit := outputProbeDecodeNatSourceBit bits state.cursor
  let afterOuter := outputProbeDecodeNatOuterExtrasStep n cursorIdx valueIdx
    activeIdx currentOuter state bit
  let body := outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx
  let counter := outputProbeIndexedControllerIdx n loopIdx
  let limit := outputProbeIndexedControllerIdx n fuelIdx
  let currentFrame := outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx
    valueIdx activeIdx loopIdx outerExtras bits input output extras initial
    iteration
  let afterFrame := outputProbeLatchFrameCfg tm controllerTapes afterOuter
    input output extras false
  let nextFrame := outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx
    valueIdx activeIdx loopIdx outerExtras bits input output extras initial
    (iteration + 1)
  obtain ⟨bodySteps, hbodySteps, hbodyRun⟩ :=
    outputProbeDecodeNatBodyTM_reachesIn_frame_internal tm controllerTapes
      cursorIdx scratchIdx valueIdx activeIdx currentOuter state bit input
      output extras hpre hbody
  have hcurrentOuterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (currentOuter i) :=
    outputProbeDecodeNatLoopOuterExtras_parked_internal n cursorIdx valueIdx
      activeIdx loopIdx outerExtras houter state iteration
  have hafterOuterEq : afterOuter =
      outputProbeDecodeNatStateOuterExtras n cursorIdx valueIdx activeIdx
        (Function.update outerExtras counter
          (outputProbeCounterTape iteration))
        (outputProbeDecodeNatStateAfterBit state bit) := by
    exact outputProbeDecodeNatOuterExtrasStep_state_internal n cursorIdx
      valueIdx activeIdx hcursorValue hcursorActive hvalueActive _ state bit
  have hloopBaseParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked ((Function.update outerExtras counter
          (outputProbeCounterTape iteration)) i) :=
    outputProbeDecodeNatUpdateOuter_parked_internal n outerExtras houter
      loopIdx iteration
  have hafterOuterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (afterOuter i) := by
    rw [hafterOuterEq]
    exact outputProbeDecodeNatStateOuterExtras_parked_internal n cursorIdx
      valueIdx activeIdx _ hloopBaseParked _
  have hafterPost := outputProbeLatchFrameCfg_post tm controllerTapes
    afterOuter input output extras false
  have hafterParked := outputProbeLatchFramePost_parked tm controllerTapes
    afterOuter input output extras false hextras hafterOuterParked houtput
    afterFrame.input afterFrame.work afterFrame.output hafterPost
  have hafterLoop : (afterFrame.work counter).HasBinaryNat iteration := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes afterOuter
      input output extras false afterFrame.input afterFrame.work
      afterFrame.output hafterPost loopIdx, hafterOuterEq,
      outputProbeDecodeNatStateOuterExtras_other_internal n cursorIdx valueIdx
        activeIdx loopIdx hloopCursor hloopValue hloopActive,
      Function.update_self]
    exact Tape.init_move_right_hasBinaryNat iteration
  have hsucc := outputProbeDecodeNatBinarySuccCanonical_reachesIn_internal
    counter iteration afterFrame.input afterFrame.work afterFrame.output
    hafterLoop hafterParked.1 hafterParked.2.1 hafterParked.2.2
  let updatedOuter := Function.update afterOuter counter
    (outputProbeCounterTape (iteration + 1))
  have hupdatedPost : outputProbeLatchFramePost tm controllerTapes
      updatedOuter input output extras false afterFrame.input
      (Function.update afterFrame.work counter
        (outputProbeCounterTape (iteration + 1)))
      afterFrame.output := by
    exact outputProbeLatchFramePost_updateController tm controllerTapes
      afterOuter input output extras false afterFrame.input afterFrame.work
      afterFrame.output hafterPost loopIdx
      (outputProbeCounterTape (iteration + 1))
  have hupdatedEq := outputProbeLatchFramePost_eq_frameCfg tm controllerTapes
    updatedOuter input output extras false afterFrame.input
    (Function.update afterFrame.work counter
      (outputProbeCounterTape (iteration + 1)))
    afterFrame.output hupdatedPost
  have hnextState : outputProbeDecodeNatStateAt bits initial (iteration + 1) =
      outputProbeDecodeNatStateAfterBit state bit := by
    exact outputProbeDecodeNatStateAt_succ_internal bits initial iteration
      hcursorBound
  have hupdatedOuter : updatedOuter =
      outputProbeDecodeNatLoopOuterExtras n cursorIdx valueIdx activeIdx
        loopIdx outerExtras
        (outputProbeDecodeNatStateAt bits initial (iteration + 1))
        (iteration + 1) := by
    rw [hnextState]
    exact outputProbeDecodeNatLoopOuterExtras_step_internal n cursorIdx
      valueIdx activeIdx loopIdx hcursorValue hcursorActive hvalueActive
      hloopCursor hloopValue hloopActive outerExtras state iteration bit
  have hnextInput : afterFrame.input = nextFrame.input := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeDecodeNatFrameCfg] using hupdatedEq.1
  have hnextWork : Function.update afterFrame.work counter
      (outputProbeCounterTape (iteration + 1)) = nextFrame.work := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeDecodeNatFrameCfg] using hupdatedEq.2.1
  have hnextOutput : afterFrame.output = nextFrame.output := by
    simpa [updatedOuter, hupdatedOuter, nextFrame,
      outputProbeDecodeNatFrameCfg] using hupdatedEq.2.2
  have hsuccNext : (binarySuccTM counter).reachesIn
      (binarySuccTime iteration)
      { state := (binarySuccTM counter).qstart
        input := afterFrame.input
        work := afterFrame.work
        output := afterFrame.output }
      { state := (binarySuccTM counter).qhalt
        input := nextFrame.input
        work := nextFrame.work
        output := nextFrame.output } := by
    have hend :
        ({ state := (binarySuccTM counter).qhalt
           input := afterFrame.input
           work := Function.update afterFrame.work counter
             (outputProbeCounterTape (iteration + 1))
           output := afterFrame.output } :
          Cfg (0 + outputProbeControllerTapes n + controllerTapes)
            (binarySuccTM counter).Q) =
        { state := (binarySuccTM counter).qhalt
          input := nextFrame.input
          work := nextFrame.work
          output := nextFrame.output } :=
      Cfg.ext rfl hnextInput hnextWork hnextOutput
    exact hend ▸ hsucc
  have hinpTransition : transitionInput afterFrame.input = afterFrame.input :=
    hafterParked.1.transitionInput_eq_self
  have hworkTransition :
      (fun i => transitionTape (afterFrame.work i)) = afterFrame.work := by
    funext i
    exact (hafterParked.2.1 i).transitionTape_eq_self
  have houtTransition : transitionTape afterFrame.output = afterFrame.output :=
    hafterParked.2.2.transitionTape_eq_self
  have hsuccNext' : (binarySuccTM counter).reachesIn
      (binarySuccTime iteration)
      { state := (binarySuccTM counter).qstart
        input := transitionInput afterFrame.input
        work := fun i => transitionTape (afterFrame.work i)
        output := transitionTape afterFrame.output }
      { state := (binarySuccTM counter).qhalt
        input := nextFrame.input
        work := nextFrame.work
        output := nextFrame.output } := by
    rw [hinpTransition, hworkTransition, houtTransition]
    exact hsuccNext
  have hseq := seqTM_reachesIn_of_reachesIn body (binarySuccTM counter)
    hbodyRun rfl hsuccNext'
  have hlift := binaryForTM_iteration_reachesIn_internal body counter limit
    hseq
  refine ⟨bodySteps + 1 + binarySuccTime iteration, ?_, ?_⟩
  · omega
  · simpa [body, counter, limit, state, bit, currentOuter, afterOuter,
      currentFrame, afterFrame, nextFrame, outputProbeDecodeNatTM,
      outputProbeDecodeNatIterationStartCfg,
      outputProbeDecodeNatIterationDoneCfg, binaryForIterationWrap,
      binaryForIterationTM, phase1Wrap, phase2Wrap] using hlift

/-- Internal constructor for the exact bounded decoder segment invariant. -/
noncomputable def outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal
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
      bodyTime startValue fuelValue := by
  let body := outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx
  let counter := outputProbeIndexedControllerIdx n loopIdx
  let limit := outputProbeIndexedControllerIdx n fuelIdx
  let scanCfg := outputProbeDecodeNatScanCfg tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits input output
    extras initial
  let iterationStartCfg := outputProbeDecodeNatIterationStartCfg tm
    controllerTapes cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx
    outerExtras bits input output extras initial
  let iterationDoneCfg := outputProbeDecodeNatIterationDoneCfg tm
    controllerTapes cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx
    outerExtras bits input output extras initial
  let doneCfg := outputProbeDecodeNatDoneCfg tm controllerTapes cursorIdx
    scratchIdx valueIdx activeIdx loopIdx fuelIdx outerExtras bits input output
    extras initial fuelValue
  apply BinaryForSegmentSpec.ofWitnessesInternal
    (outputProbeScan_address_ne_limit_internal n hloopFuel)
    scanCfg iterationStartCfg iterationDoneCfg doneCfg
  · intro value _hstart hvalue
    let frame := outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      value
    have hparked := outputProbeDecodeNatFrameCfg_parked_internal tm
      controllerTapes cursorIdx valueIdx activeIdx loopIdx outerExtras houter
      bits input output extras hextras houtput initial value
    have hcounter := outputProbeDecodeNatFrameCfg_loop_internal tm
      controllerTapes cursorIdx valueIdx activeIdx loopIdx hloopCursor
      hloopValue hloopActive outerExtras bits input output extras initial value
    have hlimitFrame : (frame.work limit).HasBinaryNat fuelValue := by
      rw [outputProbeDecodeNatFrameCfg_other_internal tm controllerTapes
        cursorIdx valueIdx activeIdx loopIdx fuelIdx hfuelCursor hfuelValue
        hfuelActive (Ne.symm hloopFuel) outerExtras bits input output extras
        initial value]
      exact hfuel
    have hrun := binaryForTM_compare_reachesIn_frame_of_lt_internal body
      counter limit (outputProbeScan_address_ne_limit_internal n hloopFuel)
      value fuelValue hvalue frame.input frame.work frame.output hcounter
      hlimitFrame hparked.1.read_ne_start
      (fun i _ _ => (hparked.2.1 i).read_ne_start)
      hparked.2.2.read_ne_start
    simpa [body, counter, limit, scanCfg, iterationStartCfg,
      outputProbeDecodeNatTM, outputProbeDecodeNatScanCfg,
      outputProbeDecodeNatIterationStartCfg, frame] using hrun
  · intro value hstart hvalue
    simpa [scanCfg, iterationStartCfg, iterationDoneCfg,
      outputProbeDecodeNatTM] using iterationWitness value hstart hvalue
  · intro value _hstart _hvalue
    let frame := outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      (value + 1)
    let c : Cfg (0 + outputProbeControllerTapes n + controllerTapes)
        (binaryForIterationTM body counter).Q :=
      { state := (binaryForIterationTM body counter).qhalt
        input := frame.input
        work := frame.work
        output := frame.output }
    have hparked := outputProbeDecodeNatFrameCfg_parked_internal tm
      controllerTapes cursorIdx valueIdx activeIdx loopIdx outerExtras houter
      bits input output extras hextras houtput initial (value + 1)
    have hstep := binaryForTM_step_iteration_halt_internal body counter limit c
      rfl hparked.1.read_ne_start
      (fun i => (hparked.2.1 i).read_ne_start) hparked.2.2.read_ne_start
    simpa [body, counter, limit, iterationDoneCfg, scanCfg,
      outputProbeDecodeNatTM, outputProbeDecodeNatIterationDoneCfg,
      outputProbeDecodeNatScanCfg, binaryForIterationWrap, c, frame] using hstep
  · let frame := outputProbeDecodeNatFrameCfg tm controllerTapes cursorIdx
      valueIdx activeIdx loopIdx outerExtras bits input output extras initial
      fuelValue
    have hparked := outputProbeDecodeNatFrameCfg_parked_internal tm
      controllerTapes cursorIdx valueIdx activeIdx loopIdx outerExtras houter
      bits input output extras hextras houtput initial fuelValue
    have hcounter := outputProbeDecodeNatFrameCfg_loop_internal tm
      controllerTapes cursorIdx valueIdx activeIdx loopIdx hloopCursor
      hloopValue hloopActive outerExtras bits input output extras initial
      fuelValue
    have hlimitFrame : (frame.work limit).HasBinaryNat fuelValue := by
      rw [outputProbeDecodeNatFrameCfg_other_internal tm controllerTapes
        cursorIdx valueIdx activeIdx loopIdx fuelIdx hfuelCursor hfuelValue
        hfuelActive (Ne.symm hloopFuel) outerExtras bits input output extras
        initial fuelValue]
      exact hfuel
    have hrun := binaryForTM_compare_reachesIn_frame_of_eq_internal body
      counter limit (outputProbeScan_address_ne_limit_internal n hloopFuel)
      fuelValue frame.input frame.work frame.output hcounter hlimitFrame
      hparked.1.read_ne_start
      (fun i _ _ => (hparked.2.1 i).read_ne_start)
      hparked.2.2.read_ne_start
    simpa [body, counter, limit, scanCfg, doneCfg, outputProbeDecodeNatTM,
      outputProbeDecodeNatScanCfg, outputProbeDecodeNatDoneCfg, frame] using
      hrun
  · simp [doneCfg, outputProbeDecodeNatDoneCfg, outputProbeDecodeNatTM,
      binaryForTM]

/-- Internal constructor selecting every source-dependent decoder-body
runtime and assembling the complete bounded loop certificate. -/
noncomputable def
    ComputesInSpace.outputProbeDecodeNatSegmentSpecInternal
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
        bodyTime startValue fuelValue := by
  classical
  have hcursorScratch : layout.cursorIdx ≠ layout.scratchIdx :=
    layout.roles_ne_internal (by decide)
  have hcursorValue : layout.cursorIdx ≠ layout.valueIdx :=
    layout.roles_ne_internal (by decide)
  have hcursorActive : layout.cursorIdx ≠ layout.activeIdx :=
    layout.roles_ne_internal (by decide)
  have hvalueActive : layout.valueIdx ≠ layout.activeIdx :=
    layout.roles_ne_internal (by decide)
  have hloopFuel : layout.loopIdx ≠ layout.fuelIdx :=
    layout.roles_ne_internal (by decide)
  have hloopCursor : layout.loopIdx ≠ layout.cursorIdx :=
    layout.roles_ne_internal (by decide)
  have hloopValue : layout.loopIdx ≠ layout.valueIdx :=
    layout.roles_ne_internal (by decide)
  have hloopActive : layout.loopIdx ≠ layout.activeIdx :=
    layout.roles_ne_internal (by decide)
  have hfuelCursor : layout.fuelIdx ≠ layout.cursorIdx :=
    layout.roles_ne_internal (by decide)
  have hfuelValue : layout.fuelIdx ≠ layout.valueIdx :=
    layout.roles_ne_internal (by decide)
  have hfuelActive : layout.fuelIdx ≠ layout.activeIdx :=
    layout.roles_ne_internal (by decide)
  have hscratchValue : layout.scratchIdx ≠ layout.valueIdx :=
    layout.roles_ne_internal (by decide)
  have hscratchActive : layout.scratchIdx ≠ layout.activeIdx :=
    layout.roles_ne_internal (by decide)
  have hscratchLoop : layout.scratchIdx ≠ layout.loopIdx :=
    layout.roles_ne_internal (by decide)
  let state (value : ℕ) :=
    outputProbeDecodeNatStateAt (f input) initial value
  let currentOuter (value : ℕ) :=
    outputProbeDecodeNatLoopOuterExtras n layout.cursorIdx layout.valueIdx
      layout.activeIdx layout.loopIdx outerExtras (state value) value
  have bodyExists : ∀ value, ∃ bodyBound : ℕ,
      ∀ (hstart : startValue ≤ value) (hvalue : value < fuelValue),
        ∃ pre : TapePred
            (0 + outputProbeControllerTapes n + controllerTapes),
          pre
            (outputProbeDecodeNatFrameCfg tm controllerTapes layout.cursorIdx
              layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
              (f input) input output extras initial value).input
            (outputProbeDecodeNatFrameCfg tm controllerTapes layout.cursorIdx
              layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
              (f input) input output extras initial value).work
            (outputProbeDecodeNatFrameCfg tm controllerTapes layout.cursorIdx
              layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
              (f input) input output extras initial value).output ∧
          (outputProbeDecodeNatBodyTM tm controllerTapes layout.cursorIdx
            layout.scratchIdx layout.valueIdx layout.activeIdx).HoareTime pre
              (outputProbeLatchFramePost tm controllerTapes
                (outputProbeDecodeNatOuterExtrasStep n layout.cursorIdx
                  layout.valueIdx layout.activeIdx (currentOuter value)
                  (state value)
                  (outputProbeDecodeNatSourceBit (f input)
                    (state value).cursor))
                input output extras false)
              bodyBound := by
    intro value
    by_cases hrange : startValue ≤ value ∧ value < fuelValue
    · have hcurrentParked : ∀ i,
          ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
            Parked (currentOuter value i) :=
        outputProbeDecodeNatLoopOuterExtras_parked_internal n
          layout.cursorIdx layout.valueIdx layout.activeIdx layout.loopIdx
          outerExtras houter (state value) value
      have hcursorCurrent :
          (currentOuter value
            (outputProbeDecodeNatCursorIdx n layout.cursorIdx))
              |>.HasBinaryNat (state value).cursor :=
        outputProbeDecodeNatStateOuterExtras_cursor_internal n
          layout.cursorIdx layout.valueIdx layout.activeIdx hcursorValue
          hcursorActive _ _
      have hscratchCurrent :
          (currentOuter value
            (outputProbeIndexedControllerIdx n layout.scratchIdx))
              |>.HasBinaryNat 0 := by
        change (outputProbeDecodeNatLoopOuterExtras n layout.cursorIdx
          layout.valueIdx layout.activeIdx layout.loopIdx outerExtras
          (state value) value
          (outputProbeIndexedControllerIdx n layout.scratchIdx))
            |>.HasBinaryNat 0
        rw [outputProbeDecodeNatLoopOuterExtras_other_internal n
          layout.cursorIdx layout.valueIdx layout.activeIdx layout.loopIdx
          layout.scratchIdx (Ne.symm hcursorScratch) hscratchValue
          hscratchActive hscratchLoop outerExtras (state value) value]
        exact hscratch
      have hvalueCurrent :
          (currentOuter value
            (outputProbeDecodeNatValueIdx n layout.valueIdx))
              |>.HasBinaryNat (state value).value :=
        outputProbeDecodeNatStateOuterExtras_value_internal n
          layout.cursorIdx layout.valueIdx layout.activeIdx hvalueActive _ _
      have hactiveCurrent :
          (currentOuter value
            (outputProbeDecodeNatActiveIdx n layout.activeIdx))
              |>.HasBinaryNat (if (state value).active then 1 else 0) :=
        outputProbeDecodeNatStateOuterExtras_active_internal n
          layout.cursorIdx layout.valueIdx layout.activeIdx _ _
      obtain ⟨bodyBound, pre, hpre, hbody⟩ :=
        hcomp.outputProbeDecodeNatBodyTM_hoareTime_internal input
          (state value) (hqueryValid value hrange.1 hrange.2) output houtput
          extras hextras hcleanupCounter cleanupLimit hcleanupLimit
          (hqueryLimit value hrange.1 hrange.2) controllerTapes
          (currentOuter value) hcurrentParked layout.cursorIdx
          layout.scratchIdx layout.valueIdx layout.activeIdx hcursorScratch
          hcursorValue hcursorActive hcursorCurrent hscratchCurrent
          hvalueCurrent hactiveCurrent
      refine ⟨bodyBound, ?_⟩
      intro _hstart _hvalue
      refine ⟨pre, ?_, hbody⟩
      simpa [currentOuter, state, outputProbeDecodeNatFrameCfg] using hpre
    · refine ⟨0, ?_⟩
      intro hstart hvalue
      exact (hrange ⟨hstart, hvalue⟩).elim
  choose bodyTime hbody using bodyExists
  refine ⟨bodyTime,
    outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal tm
      controllerTapes layout.cursorIdx layout.scratchIdx layout.valueIdx
      layout.activeIdx layout.loopIdx layout.fuelIdx hloopFuel hloopCursor
      hloopValue hloopActive hfuelCursor hfuelValue hfuelActive outerExtras
      (f input) input output extras hextras houter houtput initial bodyTime
      startValue fuelValue hfuel ?_⟩
  intro value hstart hvalue
  obtain ⟨pre, hpre, hhoare⟩ := hbody value hstart hvalue
  obtain ⟨time, htime, hrun⟩ :=
    outputProbeDecodeNatIteration_reachesIn_of_body_internal tm
      controllerTapes layout.cursorIdx layout.scratchIdx layout.valueIdx
      layout.activeIdx layout.loopIdx layout.fuelIdx hcursorValue
      hcursorActive hvalueActive hloopCursor hloopValue hloopActive
      outerExtras (f input) input output extras hextras houter houtput initial
      value (hqueryValid value hstart hvalue) hpre hhoare
  refine ⟨time, ?_, hrun⟩
  simp only [binaryForIterationTime]
  omega

/-- Internal initialized-frame Hoare adapter for the complete bounded decoder.
The selected body-time function is inherited from the source-dependent segment
certificate. -/
theorem ComputesInSpace.outputProbeDecodeNatTM_hoareTime_internal
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
          (fuelValue - startValue)) := by
  classical
  let packed := hcomp.outputProbeDecodeNatSegmentSpecInternal input output
    houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit
    controllerTapes layout outerExtras houter initial hscratch startValue
    fuelValue hfuel hqueryValid hqueryLimit
  let bodyTime := packed.1
  let spec := packed.2
  refine ⟨bodyTime, ?_⟩
  have hscanState :
      (spec.scanCfg startValue).state =
        (outputProbeDecodeNatTM tm controllerTapes layout.cursorIdx
          layout.scratchIdx layout.valueIdx layout.activeIdx layout.loopIdx
          layout.fuelIdx).qstart := by
    simp [spec, packed,
      ComputesInSpace.outputProbeDecodeNatSegmentSpecInternal,
      outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal,
      BinaryForSegmentSpec.ofWitnessesInternal, outputProbeDecodeNatScanCfg,
      outputProbeDecodeNatTM, binaryForTM]
  have hsegment := spec.hoareTime_internal hstartFuel hscanState
  apply hsegment.consequence
  · intro inp work out hpre
    have heq := outputProbeLatchFramePost_eq_frameCfg_internal tm
      controllerTapes _ input output extras false inp work out hpre
    simpa [spec, packed,
      ComputesInSpace.outputProbeDecodeNatSegmentSpecInternal,
      outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal,
      BinaryForSegmentSpec.ofWitnessesInternal, outputProbeDecodeNatScanCfg,
      outputProbeDecodeNatFrameCfg] using heq
  · intro inp work out hpost
    rcases hpost with ⟨hinp, hwork, hout⟩
    rw [hinp, hwork, hout]
    simpa [spec, packed,
      ComputesInSpace.outputProbeDecodeNatSegmentSpecInternal,
      outputProbeDecodeNatSegmentSpecOfIterationWitnessesInternal,
      BinaryForSegmentSpec.ofWitnessesInternal, outputProbeDecodeNatDoneCfg]
      using outputProbeDecodeNatFrameCfg_post_internal tm controllerTapes
        layout.cursorIdx layout.valueIdx layout.activeIdx layout.loopIdx
        outerExtras (f input) input output extras initial fuelValue
  · exact le_rfl

private theorem skipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

theorem outputProbeDecodeNatZeroTM_isTransducer_internal
    (n controllerTapes : ℕ) (cursorIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatZeroTM n controllerTapes cursorIdx
      activeIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · exact clearWorkTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeNatOneTM_isTransducer_internal
    (n controllerTapes : ℕ) (cursorIdx valueIdx : Fin controllerTapes) :
    (outputProbeDecodeNatOneTM n controllerTapes cursorIdx
      valueIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · exact binarySuccTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeNatActiveTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatActiveTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).IsTransducer := by
  apply IsTransducer.outputProbeIndexedResetDispatchTM
  · exact outputProbeDecodeNatZeroTM_isTransducer_internal n controllerTapes
      cursorIdx activeIdx
  · exact outputProbeDecodeNatOneTM_isTransducer_internal n controllerTapes
      cursorIdx valueIdx

theorem outputProbeDecodeNatBodyTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx : Fin controllerTapes) :
    (outputProbeDecodeNatBodyTM tm controllerTapes cursorIdx scratchIdx
      valueIdx activeIdx).IsTransducer := by
  apply IsTransducer.branchWorkSymbolTM
  · exact outputProbeDecodeNatActiveTM_isTransducer_internal tm
      controllerTapes cursorIdx scratchIdx valueIdx activeIdx
  · exact skipTM_isTransducer_internal

theorem outputProbeDecodeNatTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (cursorIdx scratchIdx valueIdx activeIdx loopIdx fuelIdx :
      Fin controllerTapes) :
    (outputProbeDecodeNatTM tm controllerTapes cursorIdx scratchIdx valueIdx
      activeIdx loopIdx fuelIdx).IsTransducer := by
  apply IsTransducer.binaryForTM
  exact outputProbeDecodeNatBodyTM_isTransducer_internal tm controllerTapes
    cursorIdx scratchIdx valueIdx activeIdx

end TM

end Complexity
