/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Internal
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Defs

/-!
# Numeric transition-formula schedules -- proof internals

The proofs first align the fixed-width numeric member streams with sequential
formula compilation, then reuse the numeric right-fold suffix. Formula syntax,
bounded positions, tape slots, and symbols appear only in the final adapter
theorems.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem fixedWidthSizeAt_of_lt_internal
    {count width index : ℕ} (hindex : index < count) :
    fixedWidthSizeAt count width index = width := by
  simp [fixedWidthSizeAt, hindex]

theorem fixedWidthSizeAt_of_ge_internal
    {count width index : ℕ} (hindex : count ≤ index) :
    fixedWidthSizeAt count width index = 0 := by
  simp [fixedWidthSizeAt, Nat.not_lt.mpr hindex]

theorem length_readFormulaMemberBlock_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex
      position : ℕ) :
    (readFormulaMemberBlock stateCount tapeCount T configBase available
      tapeIndex symbolIndex position).length = 3 := by
  rfl

theorem length_readFormulaMemberGates_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaMemberGates stateCount tapeCount T configBase available
      tapeIndex symbolIndex).length = 3 * (T + 1) := by
  unfold readFormulaMemberGates
  rw [length_indexedGateBlocks_internal (T + 1) 3]
  · ring
  · intro position _
    exact length_readFormulaMemberBlock_internal stateCount tapeCount T
      configBase available tapeIndex symbolIndex position

theorem getElem_readFormulaMemberGates_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ)
    (position : Fin (T + 1)) (offset : Fin 3) :
    (readFormulaMemberGates stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[position.val * 3 + offset.val]'(by
        rw [length_readFormulaMemberGates_internal]
        nlinarith [position.isLt, offset.isLt]) =
      (readFormulaMemberBlock stateCount tapeCount T configBase available
        tapeIndex symbolIndex position.val)[offset.val]'(by
          rw [length_readFormulaMemberBlock_internal]
          exact offset.isLt) := by
  unfold readFormulaMemberGates
  exact getElem_indexedGateBlocks_internal (T + 1) 3
    (fun index => readFormulaMemberBlock stateCount tapeCount T configBase
      available tapeIndex symbolIndex index)
    (by
      intro index _
      exact length_readFormulaMemberBlock_internal stateCount tapeCount T
        configBase available tapeIndex symbolIndex index)
    position.val offset.val position.isLt offset.isLt

theorem length_readFormulaSchedule_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex).length = 4 * (T + 1) + 1 := by
  simp [readFormulaSchedule, length_readFormulaMemberGates_internal]
  ring

theorem getElem_readFormulaSchedule_member_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ)
    (position : Fin (T + 1)) (offset : Fin 3) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[position.val * 3 + offset.val]'(by
        rw [length_readFormulaSchedule_internal]
        nlinarith [position.isLt, offset.isLt]) =
      (readFormulaMemberBlock stateCount tapeCount T configBase available
        tapeIndex symbolIndex position.val)[offset.val]'(by
          rw [length_readFormulaMemberBlock_internal]
          exact offset.isLt) := by
  unfold readFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_left]
    exact getElem_readFormulaMemberGates_internal stateCount tapeCount T
      configBase available tapeIndex symbolIndex position offset
  · simp only [List.length_append, List.length_singleton,
      length_readFormulaMemberGates_internal]
    nlinarith [position.isLt, offset.isLt]

theorem getElem_readFormulaSchedule_identity_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[3 * (T + 1)]'(by
        rw [length_readFormulaSchedule_internal]
        omega) = CircuitCode.RawGate.constant 0 false := by
  unfold readFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_right]
    all_goals simp [length_readFormulaMemberGates_internal]
  · simp [length_readFormulaMemberGates_internal]

theorem getElem_readFormulaSchedule_connector_internal
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ)
    (rank : Fin (T + 1)) :
    (readFormulaSchedule stateCount tapeCount T configBase available
      tapeIndex symbolIndex)[3 * (T + 1) + 1 + rank.val]'(by
        rw [length_readFormulaSchedule_internal]
        omega) =
      indexedRightFoldConnector .or available (T + 1)
        (fixedWidthSizeAt (T + 1) 3) rank.val := by
  unfold readFormulaSchedule
  erw [List.getElem_append_right]
  · simp only [List.length_append,
      length_readFormulaMemberGates_internal, List.length_singleton]
    have hindex :
        3 * (T + 1) + 1 + rank.val - (3 * (T + 1) + 1) = rank.val := by
      omega
    simp only [hindex]
    exact getElem_indexedRightFoldConnectors_internal .or available
      (T + 1) (fixedWidthSizeAt (T + 1) 3) rank
  · simp only [List.length_append,
      length_readFormulaMemberGates_internal, List.length_singleton]
    omega

theorem length_predecessorHeadMemberGates_internal
    (stateCount T configBase tapeIndex target directionCode : ℕ) :
    (predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode).length = T + 1 := by
  unfold predecessorHeadMemberGates
  rw [length_indexedGateBlocks_internal (T + 1) 1]
  · omega
  · simp

theorem getElem_predecessorHeadMemberGates_internal
    (stateCount T configBase tapeIndex target directionCode : ℕ)
    (source : Fin (T + 1)) :
    (predecessorHeadMemberGates stateCount T configBase tapeIndex target
      directionCode)[source.val]'(by
        rw [length_predecessorHeadMemberGates_internal]
        exact source.isLt) =
      predecessorHeadMemberGate stateCount T configBase tapeIndex target
        directionCode source.val := by
  unfold predecessorHeadMemberGates
  have hget := getElem_indexedGateBlocks_internal (T + 1) 1
    (fun index => [predecessorHeadMemberGate stateCount T configBase
      tapeIndex target directionCode index]) (by simp) source.val 0
      source.isLt (by omega)
  simp only [Nat.mul_one, Nat.add_zero, List.getElem_cons_zero] at hget
  exact hget

theorem length_predecessorHeadFormulaSchedule_internal
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode).length = 2 * (T + 1) + 1 := by
  simp [predecessorHeadFormulaSchedule,
    length_predecessorHeadMemberGates_internal]
  ring

theorem getElem_predecessorHeadFormulaSchedule_member_internal
    (stateCount T configBase available tapeIndex target directionCode : ℕ)
    (source : Fin (T + 1)) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode)[source.val]'(by
        rw [length_predecessorHeadFormulaSchedule_internal]
        omega) =
      predecessorHeadMemberGate stateCount T configBase tapeIndex target
        directionCode source.val := by
  unfold predecessorHeadFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_left]
    exact getElem_predecessorHeadMemberGates_internal stateCount T configBase
      tapeIndex target directionCode source
  · simp only [List.length_append, List.length_singleton,
      length_predecessorHeadMemberGates_internal]
    omega

theorem getElem_predecessorHeadFormulaSchedule_identity_internal
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode)[T + 1]'(by
        rw [length_predecessorHeadFormulaSchedule_internal]
        omega) = CircuitCode.RawGate.constant 0 false := by
  unfold predecessorHeadFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_right]
    all_goals simp [length_predecessorHeadMemberGates_internal]
  · simp [length_predecessorHeadMemberGates_internal]

theorem getElem_predecessorHeadFormulaSchedule_connector_internal
    (stateCount T configBase available tapeIndex target directionCode : ℕ)
    (rank : Fin (T + 1)) :
    (predecessorHeadFormulaSchedule stateCount T configBase available
      tapeIndex target directionCode)[T + 1 + 1 + rank.val]'(by
        rw [length_predecessorHeadFormulaSchedule_internal]
        omega) =
      indexedRightFoldConnector .or available (T + 1)
        (fixedWidthSizeAt (T + 1) 1) rank.val := by
  unfold predecessorHeadFormulaSchedule
  erw [List.getElem_append_right]
  · simp only [List.length_append,
      length_predecessorHeadMemberGates_internal, List.length_singleton]
    have hindex :
        T + 1 + 1 + rank.val - (T + 1 + 1) = rank.val := by
      omega
    simp only [hindex]
    exact getElem_indexedRightFoldConnectors_internal .or available
      (T + 1) (fixedWidthSizeAt (T + 1) 1) rank
  · simp only [List.length_append,
      length_predecessorHeadMemberGates_internal, List.length_singleton]
    omega

private def numericReadMemberFormula
    (stateCount tapeCount T configBase tapeIndex symbolIndex position : ℕ) :
    BoolFormula :=
  .conj
    (.var (transitionHeadRef stateCount T configBase tapeIndex position))
    (.var (transitionCellRef stateCount tapeCount T configBase tapeIndex
      position symbolIndex))

private def numericPredecessorHeadMemberFormula
    (stateCount T configBase tapeIndex target directionCode source : ℕ) :
    BoolFormula :=
  if movedHeadPositionCode source directionCode = target then
    .var (transitionHeadRef stateCount T configBase tapeIndex source)
  else
    .fls

private theorem compileRawOutputs_fixedWidth
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
  | zero =>
      simp [BoolFormula.compileRawOutputs, indexedGateBlocks]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [BoolFormula.compileRawOutputs, indexedGateBlocks]
      simp only [Fin.val_zero]
      have hcompileZero := hcompile 0 (by omega)
      have hsizeZero := hsize 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at hcompileZero
      rw [hcompileZero, hsizeZero]
      have htailSize : ∀ index < count,
          (formulaAt (index + 1)).size = width := by
        intro index hindex
        exact hsize (index + 1) (by omega)
      have htailCompile : ∀ index < count,
          BoolFormula.compileRaw
              ((available + width) + width * index)
              (formulaAt (index + 1)) =
            blockAt (index + 1) := by
        intro index hindex
        have h := hcompile (index + 1) (by omega)
        have hbase : (available + width) + width * index =
            available + width * (index + 1) := by
          ring
        rw [hbase]
        exact h
      have htail := ih (available + width)
        (fun index => formulaAt (index + 1))
        (fun index => blockAt (index + 1)) htailSize htailCompile
      exact congrArg (fun tail => blockAt 0 ++ tail) (by simpa using htail)

private theorem numericReadMemberFormula_size
    (stateCount tapeCount T configBase tapeIndex symbolIndex position : ℕ) :
    (numericReadMemberFormula stateCount tapeCount T configBase tapeIndex
      symbolIndex position).size = 3 := by
  rfl

private theorem compileRaw_numericReadMemberFormula
    (stateCount tapeCount T configBase available tapeIndex symbolIndex
      position : ℕ) :
    BoolFormula.compileRaw (available + 3 * position)
        (numericReadMemberFormula stateCount tapeCount T configBase tapeIndex
          symbolIndex position) =
      readFormulaMemberBlock stateCount tapeCount T configBase available
        tapeIndex symbolIndex position := by
  simp [numericReadMemberFormula, readFormulaMemberBlock,
    BoolFormula.compileRaw, BoolFormula.rawOutputWire, BoolFormula.size]

private theorem numericPredecessorHeadMemberFormula_size
    (stateCount T configBase tapeIndex target directionCode source : ℕ) :
    (numericPredecessorHeadMemberFormula stateCount T configBase tapeIndex
      target directionCode source).size = 1 := by
  unfold numericPredecessorHeadMemberFormula
  split <;> rfl

private theorem compileRaw_numericPredecessorHeadMemberFormula
    (stateCount T configBase available tapeIndex target directionCode source : ℕ) :
    BoolFormula.compileRaw (available + source)
        (numericPredecessorHeadMemberFormula stateCount T configBase tapeIndex
          target directionCode source) =
      [predecessorHeadMemberGate stateCount T configBase tapeIndex target
        directionCode source] := by
  unfold numericPredecessorHeadMemberFormula predecessorHeadMemberGate
  split <;> rfl

private theorem formulaSizeAt_ofFn_fixedWidth
    (count width : ℕ) (formulaAt : ℕ → BoolFormula)
    (hsize : ∀ index < count, (formulaAt index).size = width) :
    (fun index =>
      ((((List.ofFn fun position : Fin count => formulaAt position.val).map
        BoolFormula.size)[index]?).getD 0)) =
      fixedWidthSizeAt count width := by
  funext index
  by_cases hindex : index < count
  · rw [fixedWidthSizeAt_of_lt_internal hindex]
    rw [List.getElem?_eq_getElem (by simp [hindex])]
    simp only [List.getElem_map, List.getElem_ofFn, Option.getD_some]
    exact hsize index hindex
  · rw [fixedWidthSizeAt_of_ge_internal (Nat.le_of_not_gt hindex)]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

private theorem compileRaw_numericReadFormula
    (stateCount tapeCount T configBase available tapeIndex symbolIndex : ℕ) :
    BoolFormula.compileRaw available
        (BoolFormula.disjs (List.ofFn fun position : Fin (T + 1) =>
          numericReadMemberFormula stateCount tapeCount T configBase tapeIndex
            symbolIndex position.val)) =
      readFormulaSchedule stateCount tapeCount T configBase available
        tapeIndex symbolIndex := by
  let formulaAt := fun position =>
    numericReadMemberFormula stateCount tapeCount T configBase tapeIndex
      symbolIndex position
  let blockAt := fun position =>
    readFormulaMemberBlock stateCount tapeCount T configBase available
      tapeIndex symbolIndex position
  rw [compileRaw_disjs_eq_indexed]
  have hmembers := compileRawOutputs_fixedWidth (T + 1) 3 available
    formulaAt blockAt
    (by
      intro position _
      exact numericReadMemberFormula_size stateCount tapeCount T configBase
        tapeIndex symbolIndex position)
    (by
      intro position _
      exact compileRaw_numericReadMemberFormula stateCount tapeCount T
        configBase available tapeIndex symbolIndex position)
  have hsizes := formulaSizeAt_ofFn_fixedWidth (T + 1) 3 formulaAt (by
    intro position _
    exact numericReadMemberFormula_size stateCount tapeCount T configBase
      tapeIndex symbolIndex position)
  unfold readFormulaSchedule readFormulaMemberGates
  rw [hmembers, hsizes]
  simp [blockAt]

private theorem compileRaw_numericPredecessorHeadFormula
    (stateCount T configBase available tapeIndex target directionCode : ℕ) :
    BoolFormula.compileRaw available
        (BoolFormula.disjs (List.ofFn fun source : Fin (T + 1) =>
          numericPredecessorHeadMemberFormula stateCount T configBase
            tapeIndex target directionCode source.val)) =
      predecessorHeadFormulaSchedule stateCount T configBase available
        tapeIndex target directionCode := by
  let formulaAt := fun source =>
    numericPredecessorHeadMemberFormula stateCount T configBase tapeIndex
      target directionCode source
  let blockAt := fun source =>
    [predecessorHeadMemberGate stateCount T configBase tapeIndex target
      directionCode source]
  rw [compileRaw_disjs_eq_indexed]
  have hmembers := compileRawOutputs_fixedWidth (T + 1) 1 available
    formulaAt blockAt
    (by
      intro source _
      exact numericPredecessorHeadMemberFormula_size stateCount T configBase
        tapeIndex target directionCode source)
    (by
      intro source _
      simpa only [Nat.one_mul] using
        compileRaw_numericPredecessorHeadMemberFormula stateCount T configBase
          available tapeIndex target directionCode source)
  have hsizes := formulaSizeAt_ofFn_fixedWidth (T + 1) 1 formulaAt (by
    intro source _
    exact numericPredecessorHeadMemberFormula_size stateCount T configBase
      tapeIndex target directionCode source)
  unfold predecessorHeadFormulaSchedule predecessorHeadMemberGates
  rw [hmembers, hsizes]
  simp [blockAt]

private theorem readFormula_eq_numeric
    (tm : NTM k) (T configBase : ℕ) (tape : TapeSlot k) (symbol : Γ) :
    readFormula tm T configBase tape symbol =
      BoolFormula.disjs (List.ofFn fun position : Fin (T + 1) =>
        numericReadMemberFormula (Fintype.card tm.Q) (k + 2) T configBase
          tape.index.val (symbolIndex symbol).val position.val) := by
  unfold readFormula
  apply congrArg BoolFormula.disjs
  apply congrArg List.ofFn
  funext position
  simp [numericReadMemberFormula, configVar, configWire, transitionHeadRef,
    transitionCellRef, headCellPosition]

private theorem predecessorHeadFormula_eq_numeric
    (tm : NTM k) (T configBase : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (direction : Dir3) (directionCode : ℕ)
    (hmove : ∀ source,
      movedHeadPosition source direction =
        movedHeadPositionCode source directionCode) :
    predecessorHeadFormula tm T configBase tape target direction =
      BoolFormula.disjs (List.ofFn fun source : Fin (T + 1) =>
        numericPredecessorHeadMemberFormula (Fintype.card tm.Q) T configBase
          tape.index.val target.val directionCode source.val) := by
  unfold predecessorHeadFormula
  apply congrArg BoolFormula.disjs
  apply congrArg List.ofFn
  funext source
  rw [hmove]
  simp [numericPredecessorHeadMemberFormula, configVar, configWire,
    transitionHeadRef]

theorem compileRaw_readFormula_eq_schedule_internal
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (symbol : Γ) :
    BoolFormula.compileRaw available
        (readFormula tm T configBase tape symbol) =
      readFormulaSchedule (Fintype.card tm.Q) (k + 2) T configBase available
        tape.index.val (symbolIndex symbol).val := by
  rw [readFormula_eq_numeric]
  exact compileRaw_numericReadFormula (Fintype.card tm.Q) (k + 2) T
    configBase available tape.index.val (symbolIndex symbol).val

theorem compileRaw_predecessorHeadFormula_eq_schedule_internal
    (tm : NTM k) (T configBase available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) (direction : Dir3) :
    BoolFormula.compileRaw available
        (predecessorHeadFormula tm T configBase tape target direction) =
      predecessorHeadFormulaSchedule (Fintype.card tm.Q) T configBase
        available tape.index.val target.val
          (match direction with
          | .left => 0
          | .right => 1
          | .stay => 2) := by
  cases direction with
  | left =>
      rw [predecessorHeadFormula_eq_numeric tm T configBase tape target .left 0
        (by intro source; simp [movedHeadPosition, movedHeadPositionCode])]
      exact compileRaw_numericPredecessorHeadFormula (Fintype.card tm.Q) T
        configBase available tape.index.val target.val 0
  | right =>
      rw [predecessorHeadFormula_eq_numeric tm T configBase tape target .right 1
        (by intro source; simp [movedHeadPosition, movedHeadPositionCode])]
      exact compileRaw_numericPredecessorHeadFormula (Fintype.card tm.Q) T
        configBase available tape.index.val target.val 1
  | stay =>
      rw [predecessorHeadFormula_eq_numeric tm T configBase tape target .stay 2
        (by intro source; simp [movedHeadPosition, movedHeadPositionCode])]
      exact compileRaw_numericPredecessorHeadFormula (Fintype.card tm.Q) T
        configBase available tape.index.val target.val 2

end Serializer

end CircuitUnrolling

end Complexity
