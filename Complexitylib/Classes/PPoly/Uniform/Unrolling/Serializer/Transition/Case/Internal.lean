/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs
public import Complexitylib.Circuits.Encoding.Formula

/-!
# Numeric transition-case schedules -- proof internals

The member-compilation proof treats the machine and one local transition view
as compile-time parameters. It erases them to numeric state, tape, and symbol
indices before identifying the emitted stream with the definitions layer.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem length_caseChoiceLiteralSchedule_internal
    (available choiceWire : ℕ) (choiceValue : Bool) :
    (caseChoiceLiteralSchedule available choiceWire choiceValue).length =
      caseChoiceLiteralSize choiceValue := by
  cases choiceValue <;> rfl

theorem length_caseWorkReadGates_internal
    (stateCount workCount T configBase available : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseWorkReadGates stateCount workCount T configBase available choiceValue
      workSymbolAt).length = workCount * caseReadSize T := by
  unfold caseWorkReadGates
  apply length_indexedGateBlocks_internal
  intro workIndex _
  simp [caseReadSize]

theorem getElem_caseWorkReadGates_internal
    (stateCount workCount T configBase available : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (workIndex : Fin workCount) (offset : Fin (caseReadSize T)) :
    (caseWorkReadGates stateCount workCount T configBase available choiceValue
      workSymbolAt)[workIndex.val * caseReadSize T + offset.val]'(by
        rw [length_caseWorkReadGates_internal]
        nlinarith [workIndex.isLt, offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseWorkReadAvailable T available workIndex.val choiceValue)
        (workIndex.val + 1) (workSymbolAt workIndex.val))[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) := by
  unfold caseWorkReadGates
  exact getElem_indexedGateBlocks_internal workCount (caseReadSize T)
    (fun workIndex =>
      readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseWorkReadAvailable T available workIndex choiceValue)
        (workIndex + 1) (workSymbolAt workIndex))
    (by
      intro workIndex _
      simp [caseReadSize])
    workIndex.val offset.val workIndex.isLt offset.isLt

theorem length_caseFormulaMemberGates_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaMemberGates stateCount workCount T configBase choiceWire
      available stateIndex inputSymbolIndex outputSymbolIndex choiceValue
      workSymbolAt).length =
        caseFormulaMembersSize workCount T choiceValue := by
  simp [caseFormulaMemberGates, length_caseChoiceLiteralSchedule_internal,
    length_caseWorkReadGates_internal, caseFormulaMembersSize, caseReadSize]
  ring

theorem length_caseFormulaSchedule_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue
      workSymbolAt).length =
        caseFormulaScheduleSize workCount T choiceValue := by
  simp [caseFormulaSchedule, length_caseFormulaMemberGates_internal,
    caseFormulaScheduleSize]
  omega

private theorem getElem_caseFormulaSchedule_member_aux
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex index : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (hindex : index < caseFormulaMembersSize workCount T choiceValue) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        index]'(by
          rw [length_caseFormulaSchedule_internal]
          exact lt_of_lt_of_le hindex (by
            simp [caseFormulaScheduleSize, caseFormulaMemberCount]
            omega)) =
      (caseFormulaMemberGates stateCount workCount T configBase choiceWire
        available stateIndex inputSymbolIndex outputSymbolIndex choiceValue
        workSymbolAt)[index]'(by
          rw [length_caseFormulaMemberGates_internal]
          exact hindex) := by
  unfold caseFormulaSchedule
  rw [List.getElem_append_left]
  · rw [List.getElem_append_left]
  · simp [length_caseFormulaMemberGates_internal]
    omega

theorem getElem_caseFormulaSchedule_choice_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseChoiceLiteralSize choiceValue)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        offset.val]'(by
          rw [length_caseFormulaSchedule_internal]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          nlinarith [offset.isLt]) =
      (caseChoiceLiteralSchedule available choiceWire choiceValue)[offset.val]'(by
        rw [length_caseChoiceLiteralSchedule_internal]
        exact offset.isLt) := by
  have hmember : offset.val <
      caseFormulaMembersSize workCount T choiceValue := by
    simp [caseFormulaMembersSize]
    nlinarith [offset.isLt]
  rw [getElem_caseFormulaSchedule_member_aux (hindex := hmember)]
  unfold caseFormulaMemberGates
  have hchoice : offset.val <
      (caseChoiceLiteralSchedule available choiceWire choiceValue).length := by
    rw [length_caseChoiceLiteralSchedule_internal]
    exact offset.isLt
  have hstate : offset.val <
      (caseChoiceLiteralSchedule available choiceWire choiceValue ++
        [CircuitCode.RawGate.copy
          (transitionStateRef configBase stateIndex)]).length := by
    simp [length_caseChoiceLiteralSchedule_internal]
  have hinput : offset.val <
      (caseChoiceLiteralSchedule available choiceWire choiceValue ++
        [CircuitCode.RawGate.copy
          (transitionStateRef configBase stateIndex)] ++
        readFormulaSchedule stateCount (workCount + 2) T configBase
          (caseInputReadAvailable available choiceValue) 0
          inputSymbolIndex).length := by
    simp [length_caseChoiceLiteralSchedule_internal]
    nlinarith [offset.isLt]
  have hwork : offset.val <
      (caseChoiceLiteralSchedule available choiceWire choiceValue ++
        [CircuitCode.RawGate.copy
          (transitionStateRef configBase stateIndex)] ++
        readFormulaSchedule stateCount (workCount + 2) T configBase
          (caseInputReadAvailable available choiceValue) 0 inputSymbolIndex ++
        caseWorkReadGates stateCount workCount T configBase available
          choiceValue workSymbolAt).length := by
    simp [length_caseChoiceLiteralSchedule_internal]
    nlinarith [offset.isLt]
  rw [List.getElem_append_left hwork, List.getElem_append_left hinput,
    List.getElem_append_left hstate, List.getElem_append_left hchoice]

theorem getElem_caseFormulaSchedule_state_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue]'(by
          rw [length_caseFormulaSchedule_internal]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          omega) =
      CircuitCode.RawGate.copy (transitionStateRef configBase stateIndex) := by
  have hmember : caseChoiceLiteralSize choiceValue <
      caseFormulaMembersSize workCount T choiceValue := by
    simp [caseFormulaMembersSize]
    omega
  rw [getElem_caseFormulaSchedule_member_aux (hindex := hmember)]
  unfold caseFormulaMemberGates
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal,
      length_caseWorkReadGates_internal, caseReadSize])]
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal])]
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal])]
  rw [List.getElem_append_right (by
    rw [length_caseChoiceLiteralSchedule_internal])]
  simp [length_caseChoiceLiteralSchedule_internal]

theorem getElem_caseFormulaSchedule_inputRead_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 + offset.val]'(by
          rw [length_caseFormulaSchedule_internal]
          simp [caseFormulaScheduleSize, caseFormulaMembersSize,
            caseFormulaMemberCount]
          nlinarith [offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseInputReadAvailable available choiceValue) 0 inputSymbolIndex)[
          offset.val]'(by
            rw [length_readFormulaSchedule]
            exact offset.isLt) := by
  have hoffset : offset.val < 4 * (T + 1) + 1 := offset.isLt
  have hmember : caseChoiceLiteralSize choiceValue + 1 + offset.val <
      caseFormulaMembersSize workCount T choiceValue := by
    have hread : caseReadSize T ≤
        (workCount + 2) * caseReadSize T :=
      Nat.le_mul_of_pos_left (caseReadSize T) (by omega)
    rw [caseReadSize] at hread
    rw [caseFormulaMembersSize]
    change caseChoiceLiteralSize choiceValue + 1 + offset.val <
      caseChoiceLiteralSize choiceValue + 1 +
        (workCount + 2) * (4 * (T + 1) + 1)
    nlinarith [hoffset, hread]
  rw [getElem_caseFormulaSchedule_member_aux (hindex := hmember)]
  unfold caseFormulaMemberGates
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal,
      length_caseWorkReadGates_internal, caseReadSize]
    omega)]
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal, caseReadSize]
    omega)]
  rw [List.getElem_append_right (by
    simp [length_caseChoiceLiteralSchedule_internal])]
  simp [length_caseChoiceLiteralSchedule_internal]

theorem getElem_caseFormulaSchedule_workRead_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (workIndex : Fin workCount) (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 + caseReadSize T +
          workIndex.val * caseReadSize T + offset.val]'(by
            rw [length_caseFormulaSchedule_internal]
            simp [caseFormulaScheduleSize, caseFormulaMembersSize,
              caseFormulaMemberCount]
            nlinarith [workIndex.isLt, offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseWorkReadAvailable T available workIndex.val choiceValue)
        (workIndex.val + 1) (workSymbolAt workIndex.val))[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) := by
  have hmul : (workIndex.val + 1) * caseReadSize T ≤
      workCount * caseReadSize T :=
    Nat.mul_le_mul_right (caseReadSize T) (by omega)
  have hwork : workIndex.val * caseReadSize T + offset.val <
      workCount * caseReadSize T := by
    nlinarith [offset.isLt, hmul]
  have hworkExpanded : workIndex.val * (4 * (T + 1) + 1) + offset.val <
      workCount * (4 * (T + 1) + 1) := hwork
  have hmember : caseChoiceLiteralSize choiceValue + 1 + caseReadSize T +
      workIndex.val * caseReadSize T + offset.val <
        caseFormulaMembersSize workCount T choiceValue := by
    rw [caseFormulaMembersSize]
    nlinarith [hwork]
  rw [getElem_caseFormulaSchedule_member_aux (hindex := hmember)]
  unfold caseFormulaMemberGates
  rw [List.getElem_append_left (by
    simp [length_caseChoiceLiteralSchedule_internal,
      length_caseWorkReadGates_internal, caseReadSize]
    nlinarith [hworkExpanded])]
  rw [List.getElem_append_right (by
    simp [length_caseChoiceLiteralSchedule_internal, caseReadSize]
    omega)]
  have hindex : caseChoiceLiteralSize choiceValue + 1 + caseReadSize T +
      workIndex.val * caseReadSize T + offset.val -
        (caseChoiceLiteralSize choiceValue + 1 + (4 * (T + 1) + 1)) =
      workIndex.val * caseReadSize T + offset.val := by
    change caseChoiceLiteralSize choiceValue + 1 + (4 * (T + 1) + 1) +
        workIndex.val * (4 * (T + 1) + 1) + offset.val -
          (caseChoiceLiteralSize choiceValue + 1 + (4 * (T + 1) + 1)) =
      workIndex.val * (4 * (T + 1) + 1) + offset.val
    omega
  simp only [List.length_append, List.length_singleton,
    length_caseChoiceLiteralSchedule_internal,
    length_readFormulaSchedule]
  simp only [hindex]
  exact getElem_caseWorkReadGates_internal stateCount workCount T configBase
    available choiceValue workSymbolAt workIndex offset

theorem getElem_caseFormulaSchedule_outputRead_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (offset : Fin (caseReadSize T)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseChoiceLiteralSize choiceValue + 1 +
          (workCount + 1) * caseReadSize T + offset.val]'(by
            rw [length_caseFormulaSchedule_internal]
            simp [caseFormulaScheduleSize, caseFormulaMembersSize,
              caseFormulaMemberCount]
            nlinarith [offset.isLt]) =
      (readFormulaSchedule stateCount (workCount + 2) T configBase
        (caseOutputReadAvailable workCount T available choiceValue)
        (workCount + 1) outputSymbolIndex)[offset.val]'(by
          rw [length_readFormulaSchedule]
          exact offset.isLt) := by
  have hmember : caseChoiceLiteralSize choiceValue + 1 +
      (workCount + 1) * caseReadSize T + offset.val <
        caseFormulaMembersSize workCount T choiceValue := by
    rw [caseFormulaMembersSize]
    nlinarith [offset.isLt]
  rw [getElem_caseFormulaSchedule_member_aux (hindex := hmember)]
  unfold caseFormulaMemberGates
  rw [List.getElem_append_right (by
    simp [length_caseChoiceLiteralSchedule_internal,
      length_caseWorkReadGates_internal, caseReadSize]
    ring_nf
    omega)]
  have hindex : caseChoiceLiteralSize choiceValue + 1 +
        (workCount + 1) * (4 * (T + 1) + 1) + offset.val -
      (caseChoiceLiteralSize choiceValue +
        (4 * (T + 1) + 1 + workCount * (4 * (T + 1) + 1) + 1)) =
      offset.val := by
    have hbase : caseChoiceLiteralSize choiceValue + 1 +
        (workCount + 1) * (4 * (T + 1) + 1) =
      caseChoiceLiteralSize choiceValue +
        (4 * (T + 1) + 1 + workCount * (4 * (T + 1) + 1) + 1) := by
      ring
    rw [hbase]
    omega
  simp [length_caseChoiceLiteralSchedule_internal,
    length_caseWorkReadGates_internal, caseReadSize, hindex]

theorem getElem_caseFormulaSchedule_identity_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseFormulaMembersSize workCount T choiceValue]'(by
          rw [length_caseFormulaSchedule_internal]
          simp [caseFormulaScheduleSize, caseFormulaMemberCount]
          omega) = CircuitCode.RawGate.constant 0 true := by
  unfold caseFormulaSchedule
  erw [List.getElem_append_left (by
    simp [length_caseFormulaMemberGates_internal])]
  rw [List.getElem_append_right (by
    rw [length_caseFormulaMemberGates_internal])]
  simp [length_caseFormulaMemberGates_internal]

theorem getElem_caseFormulaSchedule_connector_internal
    (stateCount workCount T configBase choiceWire available stateIndex
      inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolAt : ℕ → ℕ)
    (rank : Fin (caseFormulaMemberCount workCount)) :
    (caseFormulaSchedule stateCount workCount T configBase choiceWire available
      stateIndex inputSymbolIndex outputSymbolIndex choiceValue workSymbolAt)[
        caseFormulaMembersSize workCount T choiceValue + 1 + rank.val]'(by
          rw [length_caseFormulaSchedule_internal]
          simp [caseFormulaScheduleSize]) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) rank.val := by
  unfold caseFormulaSchedule
  erw [List.getElem_append_right (by
    simp [length_caseFormulaMemberGates_internal])]
  have hindex : caseFormulaMembersSize workCount T choiceValue + 1 + rank.val -
      (caseFormulaMembersSize workCount T choiceValue + 1) = rank.val := by
    omega
  simp only [List.length_append, List.length_singleton,
    length_caseFormulaMemberGates_internal, hindex]
  exact getElem_indexedRightFoldConnectors_internal .and available
    (caseFormulaMemberCount workCount)
    (caseFormulaSizeAt workCount T choiceValue) rank

private theorem size_caseChoiceLiteral
    (choiceWire : ℕ) (choiceValue : Bool) :
    (BoolFormula.literal choiceWire choiceValue).size =
      caseChoiceLiteralSize choiceValue := by
  cases choiceValue <;> rfl

private theorem compileRaw_caseChoiceLiteral
    (available choiceWire : ℕ) (choiceValue : Bool) :
    BoolFormula.compileRaw available
        (BoolFormula.literal choiceWire choiceValue) =
      caseChoiceLiteralSchedule available choiceWire choiceValue := by
  cases choiceValue <;>
    simp [BoolFormula.literal, BoolFormula.compileRaw,
      BoolFormula.rawOutputWire, BoolFormula.size,
      caseChoiceLiteralSchedule]

private theorem size_readFormula_eq_caseReadSize
    (tm : NTM k) (T configBase : ℕ) (tape : TapeSlot k) (symbol : Γ) :
    (readFormula tm T configBase tape symbol).size = caseReadSize T := by
  have h := congrArg List.length
    (compileRaw_readFormula_eq_schedule tm T configBase 0 tape symbol)
  simpa [caseReadSize] using h

private theorem compileRawOutputs_caseFixedWidth
    (count width available : ℕ) (formulaAt : ℕ → BoolFormula)
    (blockAt : ℕ → CircuitCode.RawCircuit)
    (hsize : ∀ index < count, (formulaAt index).size = width)
    (hcompile : ∀ index < count,
      BoolFormula.compileRaw (available + width * index) (formulaAt index) =
        blockAt index) :
    (BoolFormula.compileRawOutputs available
      (List.ofFn fun index : Fin count => formulaAt index.val)).circuit =
        indexedGateBlocks count blockAt := by
  induction count generalizing available formulaAt blockAt with
  | zero => simp [BoolFormula.compileRawOutputs, indexedGateBlocks]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [BoolFormula.compileRawOutputs, indexedGateBlocks, Fin.val_zero]
      have hcompileZero := hcompile 0 (by omega)
      have hsizeZero := hsize 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at hcompileZero
      rw [hcompileZero, hsizeZero]
      have htailSize : ∀ index < count,
          (formulaAt (index + 1)).size = width := by
        intro index hindex
        exact hsize (index + 1) (by omega)
      have htailCompile : ∀ index < count,
          BoolFormula.compileRaw ((available + width) + width * index)
              (formulaAt (index + 1)) = blockAt (index + 1) := by
        intro index hindex
        have h := hcompile (index + 1) (by omega)
        have hbase : (available + width) + width * index =
            available + width * (index + 1) := by ring
        rw [hbase]
        exact h
      have htail := ih (available + width)
        (fun index => formulaAt (index + 1))
        (fun index => blockAt (index + 1)) htailSize htailCompile
      exact congrArg (fun tail => blockAt 0 ++ tail) (by simpa using htail)

private theorem compileRawOutputs_circuit_append
    (available : ℕ) (left right : List BoolFormula) :
    (BoolFormula.compileRawOutputs available (left ++ right)).circuit =
      (BoolFormula.compileRawOutputs available left).circuit ++
        (BoolFormula.compileRawOutputs
          (available + (left.map BoolFormula.size).sum) right).circuit := by
  induction left generalizing available with
  | nil => simp [BoolFormula.compileRawOutputs]
  | cons formula formulas ih =>
      simp [BoolFormula.compileRawOutputs, ih, List.append_assoc,
        Nat.add_assoc]

private theorem compileRawOutputs_caseWorkReads
    (tm : NTM k) (T configBase available : ℕ)
    (view : TransitionCase tm) :
    (BoolFormula.compileRawOutputs
      (caseWorkReadAvailable T available 0 view.choice)
      (List.ofFn fun index : Fin k =>
        readFormula tm T configBase (.work index) (view.workRead index))).circuit =
      caseWorkReadGates (Fintype.card tm.Q) k T configBase available
        view.choice (fun index => if hindex : index < k then
          (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0) := by
  let formulaAt := fun index =>
    if hindex : index < k then
      readFormula tm T configBase (.work ⟨index, hindex⟩)
        (view.workRead ⟨index, hindex⟩)
    else
      BoolFormula.fls
  let workSymbolAt := fun index => if hindex : index < k then
    (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0
  let blockAt := fun index =>
    readFormulaSchedule (Fintype.card tm.Q) (k + 2) T configBase
      (caseWorkReadAvailable T available index view.choice) (index + 1)
      (workSymbolAt index)
  have hformulas :
      (List.ofFn fun index : Fin k =>
        readFormula tm T configBase (.work index) (view.workRead index)) =
      List.ofFn fun index : Fin k => formulaAt index.val := by
    apply congrArg List.ofFn
    funext index
    simp [formulaAt, index.isLt]
  rw [hformulas]
  have hcompiled := compileRawOutputs_caseFixedWidth k (caseReadSize T)
    (caseWorkReadAvailable T available 0 view.choice) formulaAt blockAt
    (by
      intro index hindex
      rw [show formulaAt index =
        readFormula tm T configBase (.work ⟨index, hindex⟩)
          (view.workRead ⟨index, hindex⟩) by simp [formulaAt, hindex]]
      exact size_readFormula_eq_caseReadSize tm T configBase
        (.work ⟨index, hindex⟩) (view.workRead ⟨index, hindex⟩))
    (by
      intro index hindex
      have hbase : caseWorkReadAvailable T available 0 view.choice +
          caseReadSize T * index =
        caseWorkReadAvailable T available index view.choice := by
        simp [caseWorkReadAvailable]
        ring
      rw [hbase]
      rw [show formulaAt index =
        readFormula tm T configBase (.work ⟨index, hindex⟩)
          (view.workRead ⟨index, hindex⟩) by simp [formulaAt, hindex]]
      rw [compileRaw_readFormula_eq_schedule]
      simp [blockAt, workSymbolAt, TapeSlot.index, hindex])
  unfold caseWorkReadGates
  exact hcompiled

private theorem caseWorkFormula_sizes
    (tm : NTM k) (T configBase : ℕ) (view : TransitionCase tm) :
    ((List.ofFn fun index : Fin k =>
      readFormula tm T configBase (.work index) (view.workRead index)).map
        BoolFormula.size) = List.replicate k (caseReadSize T) := by
  rw [List.map_ofFn, ← List.ofFn_const]
  apply congrArg List.ofFn
  funext index
  exact size_readFormula_eq_caseReadSize tm T configBase (.work index)
    (view.workRead index)

private theorem caseFormula_memberSizes
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (view : TransitionCase tm) :
    (([BoolFormula.literal choiceWire view.choice,
        configVar tm T configBase (.state view.state),
        readFormula tm T configBase .input view.inputRead] ++
      (List.ofFn fun index : Fin k =>
        readFormula tm T configBase (.work index) (view.workRead index)) ++
      [readFormula tm T configBase .output view.outputRead]).map
        BoolFormula.size) =
      [caseChoiceLiteralSize view.choice, 1] ++
        List.replicate (k + 2) (caseReadSize T) := by
  have hreplicate : List.replicate (k + 2) (caseReadSize T) =
      [caseReadSize T] ++ List.replicate k (caseReadSize T) ++
        [caseReadSize T] := by
    rw [show k + 2 = 1 + k + 1 by omega, List.replicate_add,
      List.replicate_add]
    rfl
  rw [List.map_append, List.map_append,
    caseWorkFormula_sizes tm T configBase view, hreplicate]
  simp [size_caseChoiceLiteral, size_readFormula_eq_caseReadSize, configVar,
    BoolFormula.size]

private theorem compileRawOutputs_caseFormulaMembers
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (view : TransitionCase tm) :
    (BoolFormula.compileRawOutputs available
      ([BoolFormula.literal choiceWire view.choice,
          configVar tm T configBase (.state view.state),
          readFormula tm T configBase .input view.inputRead] ++
        (List.ofFn fun index : Fin k =>
          readFormula tm T configBase (.work index) (view.workRead index)) ++
        [readFormula tm T configBase .output view.outputRead])).circuit =
      caseFormulaMemberGates (Fintype.card tm.Q) k T configBase choiceWire
        available (stateIndex tm view.state) (symbolIndex view.inputRead).val
        (symbolIndex view.outputRead).val view.choice
        (fun index : ℕ => if hindex : index < k then
          (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0) := by
  let leadingFormulas : List BoolFormula :=
    [BoolFormula.literal choiceWire view.choice,
      configVar tm T configBase (.state view.state),
      readFormula tm T configBase .input view.inputRead]
  let workFormulas : List BoolFormula := List.ofFn fun index : Fin k =>
    readFormula tm T configBase (.work index) (view.workRead index)
  let outputFormula : BoolFormula :=
    readFormula tm T configBase .output view.outputRead
  change (BoolFormula.compileRawOutputs available
    ((leadingFormulas ++ workFormulas) ++ [outputFormula])).circuit = _
  rw [compileRawOutputs_circuit_append available
    (leadingFormulas ++ workFormulas) [outputFormula]]
  rw [compileRawOutputs_circuit_append available leadingFormulas workFormulas]
  have hprefixSize : (leadingFormulas.map BoolFormula.size).sum =
      caseChoiceLiteralSize view.choice + 1 + caseReadSize T := by
    simp [leadingFormulas, size_caseChoiceLiteral,
      size_readFormula_eq_caseReadSize, configVar, BoolFormula.size]
    omega
  have hworkBase : available +
      (leadingFormulas.map BoolFormula.size).sum =
      caseWorkReadAvailable T available 0 view.choice := by
    rw [hprefixSize]
    simp [caseWorkReadAvailable, caseInputReadAvailable]
    ring
  have houtputBase :
      available +
        ((leadingFormulas ++ workFormulas).map BoolFormula.size).sum =
        caseOutputReadAvailable k T available view.choice := by
    rw [List.map_append, List.sum_append, hprefixSize]
    rw [show workFormulas.map BoolFormula.size =
      List.replicate k (caseReadSize T) by
        exact caseWorkFormula_sizes tm T configBase view]
    simp [caseOutputReadAvailable, caseInputReadAvailable]
    ring
  have hprefixCompile :
      (BoolFormula.compileRawOutputs available leadingFormulas).circuit =
        caseChoiceLiteralSchedule available choiceWire view.choice ++
          [CircuitCode.RawGate.copy
            (transitionStateRef configBase (stateIndex tm view.state))] ++
          readFormulaSchedule (Fintype.card tm.Q) (k + 2) T configBase
            (caseInputReadAvailable available view.choice) 0
            (symbolIndex view.inputRead).val := by
    unfold leadingFormulas
    simp only [BoolFormula.compileRawOutputs]
    rw [compileRaw_caseChoiceLiteral]
    rw [size_caseChoiceLiteral]
    simp only [configVar, BoolFormula.size]
    rw [show available + caseChoiceLiteralSize view.choice + 1 =
      caseInputReadAvailable available view.choice by
        rfl]
    rw [compileRaw_readFormula_eq_schedule]
    simp [BoolFormula.compileRaw, configWire, transitionStateRef,
      TapeSlot.index]
  rw [hprefixCompile, hworkBase,
    compileRawOutputs_caseWorkReads tm T configBase available view,
    houtputBase]
  simp only [BoolFormula.compileRawOutputs]
  rw [compileRaw_readFormula_eq_schedule]
  unfold caseFormulaMemberGates
  simp [TapeSlot.index]

private theorem caseFormulaSizeAt_eq_lookup
    (workCount T : ℕ) (choiceValue : Bool) :
    (fun index =>
      (([caseChoiceLiteralSize choiceValue, 1] ++
        List.replicate (workCount + 2) (caseReadSize T))[index]?).getD 0) =
      caseFormulaSizeAt workCount T choiceValue := by
  funext index
  cases index with
  | zero => simp [caseFormulaSizeAt]
  | succ index =>
      cases index with
      | zero => simp [caseFormulaSizeAt]
      | succ index =>
          by_cases hindex : index < workCount + 2
          · have hmember : index + 2 < caseFormulaMemberCount workCount := by
              simp [caseFormulaMemberCount]
              omega
            simp [caseFormulaSizeAt, hmember, hindex]
          · have hmember : ¬index + 2 < caseFormulaMemberCount workCount := by
              simp [caseFormulaMemberCount]
              omega
            simp [caseFormulaSizeAt, hmember, hindex]

theorem compileRaw_caseFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (view : TransitionCase tm) :
    BoolFormula.compileRaw available
        (caseFormula tm T configBase choiceWire view) =
      caseFormulaSchedule (Fintype.card tm.Q) k T configBase choiceWire
        available (stateIndex tm view.state) (symbolIndex view.inputRead).val
        (symbolIndex view.outputRead).val view.choice
        (fun index => if hindex : index < k then
          (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0) := by
  unfold caseFormula
  rw [compileRaw_conjs_eq_indexed]
  rw [compileRawOutputs_caseFormulaMembers tm T configBase choiceWire
    available view]
  rw [caseFormula_memberSizes tm T configBase choiceWire view]
  rw [caseFormulaSizeAt_eq_lookup]
  unfold caseFormulaSchedule
  simp [caseFormulaMemberCount]

end Serializer

end CircuitUnrolling

end Complexity
