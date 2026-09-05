/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Atomic
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Defs

/-!
# Numeric written-cell schedules -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

theorem length_writtenCellSuffixGates_internal
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize : ℕ) :
    (writtenCellSuffixGates stateCount tapeCount T configBase available
      tapeIndex position symbolIndex effectSize).length = 6 := by
  unfold writtenCellSuffixGates
  rw [length_indexedGateBlocks 6 1]
  simp

theorem getElem_writtenCellSuffixGates_internal
    (stateCount tapeCount T configBase available tapeIndex position symbolIndex
      effectSize : ℕ) (phase : Fin 6) :
    (writtenCellSuffixGates stateCount tapeCount T configBase available
      tapeIndex position symbolIndex effectSize)[phase.val]'(by
        rw [length_writtenCellSuffixGates_internal]
        exact phase.isLt) =
      writtenCellSuffixGate stateCount tapeCount T configBase available
        tapeIndex position symbolIndex effectSize phase.val := by
  unfold writtenCellSuffixGates
  have hget := getElem_indexedGateBlocks 6 1
    (fun phase =>
      [writtenCellSuffixGate stateCount tapeCount T configBase available
        tapeIndex position symbolIndex effectSize phase]) (by simp)
      phase.val 0 phase.isLt (by omega)
  simp only [Nat.mul_one, Nat.add_zero, List.getElem_cons_zero] at hget
  exact hget

theorem length_writtenCellSchedule_internal
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
      workSymbolIndexAt).length =
        writtenCellScheduleSize caseCount workCount T selectedAt choiceAt := by
  simp [writtenCellSchedule, writtenCellScheduleSize, writtenCellEffectSize,
    length_writtenCellSuffixGates_internal]

theorem getElem_writtenCellSchedule_head_internal
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        0]'(by
          rw [length_writtenCellSchedule_internal]
          simp [writtenCellScheduleSize]
          ) =
      headAtCellFormulaGate stateCount T configBase tapeIndex position := by
  simp [writtenCellSchedule]

theorem getElem_writtenCellSchedule_effect_internal
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ)
    (offset : Fin (writtenCellEffectSize caseCount workCount T selectedAt
      choiceAt)) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        offset.val + 1]'(by
          rw [length_writtenCellSchedule_internal]
          simp [writtenCellScheduleSize]
          omega) =
      (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire (available + 1) selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[offset.val]'(by
          rw [length_effectFormulaSchedule]
          exact offset.isLt) := by
  unfold writtenCellSchedule
  erw [List.getElem_append_right]
  · simp only [List.length_singleton]
    have hindex : offset.val + 1 - 1 = offset.val := by omega
    simp only [hindex]
    rw [List.getElem_append_left]
  · simp

theorem getElem_writtenCellSchedule_suffix_internal
    (caseCount stateCount workCount T configBase choiceWire available tapeIndex
      position symbolIndex : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (phase : Fin 6) :
    (writtenCellSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex position symbolIndex selectedAt choiceAt
      stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        writtenCellEffectSize caseCount workCount T selectedAt choiceAt + 1 +
          phase.val]'(by
            rw [length_writtenCellSchedule_internal]
            simp [writtenCellScheduleSize]
            omega) =
      writtenCellSuffixGate stateCount (workCount + 2) T configBase available
        tapeIndex position symbolIndex
        (writtenCellEffectSize caseCount workCount T selectedAt choiceAt)
        phase.val := by
  have heffectLength :
      (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire (available + 1) selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        writtenCellEffectSize caseCount workCount T selectedAt choiceAt := by
    simp only [writtenCellEffectSize]
    exact length_effectFormulaSchedule caseCount stateCount workCount T
      configBase choiceWire (available + 1) selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
  unfold writtenCellSchedule
  erw [List.getElem_append_right]
  · simp only [List.length_singleton]
    rw [List.getElem_append_right]
    · simp only [heffectLength]
      have hindex :
          writtenCellEffectSize caseCount workCount T selectedAt choiceAt + 1 +
                phase.val -
                1 -
              writtenCellEffectSize caseCount workCount T selectedAt choiceAt =
            phase.val := by omega
      simp only [hindex]
      exact getElem_writtenCellSuffixGates_internal stateCount (workCount + 2)
        T configBase available tapeIndex position symbolIndex
        (writtenCellEffectSize caseCount workCount T selectedAt choiceAt) phase
    · simp only [heffectLength]
      omega
  · simp
    omega

private theorem size_headAtCellFormula_eq_one
    (tm : NTM k) (T configBase : ℕ) (tape : TapeSlot k)
    (position : Fin (T + 2)) :
    (headAtCellFormula tm T configBase tape position).size = 1 := by
  have hlength := congrArg List.length
    (compileRaw_headAtCellFormula_eq_gate tm T configBase 0 tape position)
  simpa only [BoolFormula.length_compileRaw, List.length_singleton] using
    hlength

private theorem size_writtenCellEffectFormula_eq_effectSize
    (tm : NTM k) (T configBase choiceWire : ℕ) (tape : WritableSlot k)
    (symbol : Γ) :
    (effectFormula tm T configBase choiceWire fun effect =>
      decide ((effect.write tape).toΓ = symbol)).size =
      writtenCellEffectSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm) := by
  let selects : TransitionEffect tm → Bool := fun effect =>
    decide ((effect.write tape).toΓ = symbol)
  have hlength := congrArg List.length
    (compileRaw_effectFormula_eq_schedule tm T configBase choiceWire 0 selects)
  simp only [BoolFormula.length_compileRaw, length_effectFormulaSchedule] at hlength ⊢
  exact hlength

theorem compileRaw_writtenCellFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ) :
    BoolFormula.compileRaw available
        (writtenCellFormula tm T configBase choiceWire tape position symbol) =
      writtenCellSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available tape.toTapeSlot.index.val position.val
        (symbolIndex symbol).val (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  let selects : TransitionEffect tm → Bool := fun effect =>
    decide ((effect.write tape).toΓ = symbol)
  have heffectSize := size_writtenCellEffectFormula_eq_effectSize tm T
    configBase choiceWire tape symbol
  have heffectPositive :
      1 ≤ writtenCellEffectSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) := by
    unfold writtenCellEffectSize effectFormulaScheduleSize
    omega
  simp only [writtenCellFormula, selectedWriteFormula,
    BoolFormula.compileRaw]
  simp only [BoolFormula.size, size_headAtCellFormula_eq_one]
  simp only [BoolFormula.rawOutputWire]
  rw [heffectSize]
  rw [compileRaw_headAtCellFormula_eq_gate]
  rw [compileRaw_effectFormula_eq_schedule tm T configBase choiceWire
    (available + 1) selects]
  rw [compileRaw_headAtCellFormula_eq_gate]
  unfold writtenCellEffectSize writtenCellEffectSelectedAt at heffectSize
  unfold writtenCellEffectSize writtenCellEffectSelectedAt at heffectPositive
  simp only [Γw.toΓ] at heffectSize heffectPositive
  simp [writtenCellSchedule, writtenCellEffectSelectedAt, selects,
    writtenCellEffectSize, writtenCellSuffixGates, writtenCellSuffixGate,
    writtenCellLeftAndGate, writtenCellNegatedHeadGate,
    writtenCellOldValueGate, writtenCellRightAndGate,
    writtenCellFinalOrGate, indexedGateBlocks, BoolFormula.compileRaw,
    BoolFormula.size, CircuitCode.RawGate.copy, configVar, configWire,
    configIndex_cell, transitionCellRef, WritableSlot.toTapeSlot,
    TapeSlot.index, List.append_assoc, Nat.add_assoc]
  all_goals omega

end Serializer

end CircuitUnrolling

end Complexity
