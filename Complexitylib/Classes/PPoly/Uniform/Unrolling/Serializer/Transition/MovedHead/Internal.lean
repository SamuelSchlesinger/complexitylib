/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Defs

/-!
# Numeric moved-head schedules -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

private theorem movedHead_prefixSize_shift (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt (count + 1) =
      sizeAt 0 + prefixSize (fun index => sizeAt (index + 1)) count := by
  induction count with
  | zero => simp
  | succ count ih =>
      calc
        prefixSize sizeAt (count + 1 + 1) =
            prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
              rw [prefixSize_succ]
        _ = sizeAt 0 +
            prefixSize (fun index => sizeAt (index + 1)) count +
              sizeAt (count + 1) := by rw [ih]
        _ = sizeAt 0 +
            prefixSize (fun index => sizeAt (index + 1)) (count + 1) := by
              rw [prefixSize_succ]
              omega

theorem prefixSize_mono_movedHead_internal
    (sizeAt : ℕ → ℕ) {first second : ℕ} (hbound : first ≤ second) :
    prefixSize sizeAt first ≤ prefixSize sizeAt second := by
  induction second with
  | zero =>
      have hfirst : first = 0 := by omega
      subst hfirst
      exact le_rfl
  | succ second ih =>
      by_cases heq : first = second + 1
      · subst heq
        exact le_rfl
      · have hle : first ≤ second := by omega
        exact le_trans (ih hle) (by
          rw [prefixSize_succ]
          omega)

private theorem length_indexedGateBlocks_variable_movedHead
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (sizeAt : ℕ → ℕ)
    (hlen : ∀ index < count, (blockAt index).length = sizeAt index) :
    (indexedGateBlocks count blockAt).length = prefixSize sizeAt count := by
  induction count generalizing blockAt sizeAt with
  | zero => rfl
  | succ count ih =>
      rw [indexedGateBlocks, List.length_append, hlen 0 (by omega)]
      have htail : ∀ index < count,
          (blockAt (index + 1)).length = sizeAt (index + 1) := by
        intro index hindex
        exact hlen (index + 1) (by omega)
      rw [ih (fun index => blockAt (index + 1))
        (fun index => sizeAt (index + 1)) htail]
      rw [movedHead_prefixSize_shift]

private theorem getElem_indexedGateBlocks_variable_movedHead
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (sizeAt : ℕ → ℕ)
    (hlen : ∀ index < count, (blockAt index).length = sizeAt index)
    (index offset : ℕ) (hindex : index < count)
    (hoffset : offset < sizeAt index) :
    (indexedGateBlocks count blockAt)[prefixSize sizeAt index + offset]'(by
      rw [length_indexedGateBlocks_variable_movedHead count blockAt sizeAt hlen]
      exact lt_of_lt_of_le (Nat.add_lt_add_left hoffset _) (by
        rw [← prefixSize_succ]
        exact prefixSize_mono_movedHead_internal sizeAt (by omega))) =
      (blockAt index)[offset]'(by
        rw [hlen index hindex]
        exact hoffset) := by
  induction count generalizing blockAt sizeAt index with
  | zero => omega
  | succ count ih =>
      unfold indexedGateBlocks
      cases index with
      | zero =>
          simp only [prefixSize_zero, Nat.zero_add]
          rw [List.getElem_append_left (by
            rw [hlen 0 (by omega)]
            exact hoffset)]
      | succ index =>
          have htail : ∀ next < count,
              (blockAt (next + 1)).length = sizeAt (next + 1) := by
            intro next hnext
            exact hlen (next + 1) (by omega)
          rw [List.getElem_append_right (by
            rw [hlen 0 (by omega), movedHead_prefixSize_shift]
            omega)]
          have hoffsetIndex :
              prefixSize sizeAt (index + 1) + offset - (blockAt 0).length =
                prefixSize (fun next => sizeAt (next + 1)) index +
                  offset := by
            rw [hlen 0 (by omega), movedHead_prefixSize_shift]
            omega
          simp only [hoffsetIndex]
          exact ih (fun next => blockAt (next + 1))
            (fun next => sizeAt (next + 1)) htail index (by omega) hoffset

theorem length_movedHeadMemberBlock_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    (movedHeadMemberBlock caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
      directionCode).length =
        movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt
          directionCode := by
  simp [movedHeadMemberBlock, movedHeadMemberSizeAt, hdirection,
    movedHeadEffectSizeAt, movedHeadPredecessorSize]
  omega

theorem length_movedHeadMemberGates_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (movedHeadMemberGates caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        prefixSize
          (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
          movedHeadDirectionCount := by
  unfold movedHeadMemberGates
  apply length_indexedGateBlocks_variable_movedHead
  intro directionCode hdirection
  exact length_movedHeadMemberBlock_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    directionCode hdirection

theorem getElem_movedHeadMemberGates_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ)
    (directionCode offset : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount)
    (hoffset : offset < movedHeadMemberSizeAt caseCount workCount T selectedAt
      choiceAt directionCode) :
    (movedHeadMemberGates caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
            (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
            directionCode +
          offset]'(by
            rw [length_movedHeadMemberGates_internal]
            exact lt_of_lt_of_le (Nat.add_lt_add_left hoffset _) (by
              rw [← prefixSize_succ]
              exact prefixSize_mono_movedHead_internal _ (by omega))) =
      (movedHeadMemberBlock caseCount stateCount workCount T configBase
        choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
        directionCode)[offset]'(by
          rw [length_movedHeadMemberBlock_internal _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ directionCode hdirection]
          exact hoffset) := by
  unfold movedHeadMemberGates
  exact getElem_indexedGateBlocks_variable_movedHead movedHeadDirectionCount
    (fun directionCode =>
      movedHeadMemberBlock caseCount stateCount workCount T configBase
        choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt directionCode)
    (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
    (by
      intro index hindex
      exact length_movedHeadMemberBlock_internal caseCount stateCount workCount
        T configBase choiceWire available tapeIndex target selectedAt choiceAt
        stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
        index hindex)
    directionCode offset hdirection hoffset

theorem getElem_movedHeadMemberBlock_effect_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (directionCode offset : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount)
    (hoffset : offset < movedHeadEffectSizeAt caseCount workCount T selectedAt
      choiceAt directionCode) :
    (movedHeadMemberBlock caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt directionCode)[
        offset]'(by
          rw [length_movedHeadMemberBlock_internal _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ directionCode hdirection]
          simp [movedHeadMemberSizeAt, hdirection]
          omega) =
      (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire
        (movedHeadMemberAvailable caseCount workCount T available selectedAt
          choiceAt directionCode)
        (selectedAt directionCode) choiceAt stateIndexAt inputSymbolIndexAt
        outputSymbolIndexAt workSymbolIndexAt)[offset]'(by
          rw [length_effectFormulaSchedule]
          exact hoffset) := by
  change offset < effectFormulaScheduleSize caseCount workCount T
    (selectedAt directionCode) choiceAt at hoffset
  unfold movedHeadMemberBlock
  erw [List.getElem_append_left (by
    simp
    omega)]
  rw [List.getElem_append_left (by
    rw [length_effectFormulaSchedule]
    exact hoffset)]

theorem getElem_movedHeadMemberBlock_predecessor_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (directionCode offset : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount)
    (hoffset : offset < movedHeadPredecessorSize T) :
    (movedHeadMemberBlock caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt directionCode)[
        movedHeadEffectSizeAt caseCount workCount T selectedAt choiceAt
            directionCode +
          offset]'(by
            rw [length_movedHeadMemberBlock_internal _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ directionCode hdirection]
            simp [movedHeadMemberSizeAt, hdirection]
            omega) =
      (predecessorHeadFormulaSchedule stateCount T configBase
        (movedHeadPredecessorAvailable caseCount workCount T available
          selectedAt choiceAt directionCode)
        tapeIndex target directionCode)[offset]'(by
          rw [length_predecessorHeadFormulaSchedule]
          exact hoffset) := by
  change offset < 2 * (T + 1) + 1 at hoffset
  unfold movedHeadMemberBlock
  erw [List.getElem_append_left (by
    simp [movedHeadEffectSizeAt]
    omega)]
  rw [List.getElem_append_right (by
    simp [movedHeadEffectSizeAt])]
  simp [movedHeadEffectSizeAt]

theorem getElem_movedHeadMemberBlock_conjunction_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    (movedHeadMemberBlock caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt directionCode)[
        movedHeadEffectSizeAt caseCount workCount T selectedAt choiceAt
            directionCode +
          movedHeadPredecessorSize T]'(by
            rw [length_movedHeadMemberBlock_internal _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ directionCode hdirection]
            simp [movedHeadMemberSizeAt, hdirection]) =
      movedHeadConjunctionGate caseCount workCount T available selectedAt
        choiceAt directionCode := by
  unfold movedHeadMemberBlock
  erw [List.getElem_append_right (by
    simp [movedHeadEffectSizeAt, movedHeadPredecessorSize])]
  simp [movedHeadEffectSizeAt, movedHeadPredecessorSize]

theorem length_movedHeadFormulaSchedule_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (movedHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        movedHeadFormulaScheduleSize caseCount workCount T selectedAt
          choiceAt := by
  simp [movedHeadFormulaSchedule, movedHeadFormulaScheduleSize,
    length_movedHeadMemberGates_internal]
  omega

theorem getElem_movedHeadFormulaSchedule_identity_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (movedHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
          (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
          movedHeadDirectionCount]'(by
            rw [length_movedHeadFormulaSchedule_internal]
            simp [movedHeadFormulaScheduleSize]
            omega) = CircuitCode.RawGate.constant 0 false := by
  unfold movedHeadFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_right]
    all_goals simp [length_movedHeadMemberGates_internal]
  · simp [length_movedHeadMemberGates_internal]

theorem getElem_movedHeadFormulaSchedule_connector_internal
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ)
    (rank : Fin movedHeadDirectionCount) :
    (movedHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
            (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
            movedHeadDirectionCount +
          1 + rank.val]'(by
            rw [length_movedHeadFormulaSchedule_internal]
            simp [movedHeadFormulaScheduleSize]) =
      indexedRightFoldConnector .or available movedHeadDirectionCount
        (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
        rank.val := by
  unfold movedHeadFormulaSchedule
  erw [List.getElem_append_right]
  · have hoffset :
        prefixSize
              (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
              movedHeadDirectionCount +
            1 + rank.val -
              (movedHeadMemberGates caseCount stateCount workCount T configBase
                choiceWire available tapeIndex target selectedAt choiceAt
                stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
                workSymbolIndexAt ++
                [CircuitCode.RawGate.constant 0 false]).length = rank.val := by
        simp [length_movedHeadMemberGates_internal]
    simp only [hoffset]
    exact getElem_indexedRightFoldConnectors .or available
      movedHeadDirectionCount
      (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt) rank
  · simp [length_movedHeadMemberGates_internal]

private def movedHeadDirectionAt : ℕ → Dir3
  | 0 => .left
  | 1 => .right
  | _ => .stay

private noncomputable def movedHeadMemberFormulaAt
    (tm : NTM k) (T configBase choiceWire : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (directionCode : ℕ) : BoolFormula :=
  .conj
    (selectedMoveFormula tm T configBase choiceWire tape
      (movedHeadDirectionAt directionCode))
    (predecessorHeadFormula tm T configBase tape target
      (movedHeadDirectionAt directionCode))

private theorem movedHeadFormulaList_eq_indexed
    (tm : NTM k) (T configBase choiceWire : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) :
    [.conj (selectedMoveFormula tm T configBase choiceWire tape .left)
        (predecessorHeadFormula tm T configBase tape target .left),
      .conj (selectedMoveFormula tm T configBase choiceWire tape .right)
        (predecessorHeadFormula tm T configBase tape target .right),
      .conj (selectedMoveFormula tm T configBase choiceWire tape .stay)
        (predecessorHeadFormula tm T configBase tape target .stay)] =
      List.ofFn fun direction : Fin movedHeadDirectionCount =>
        movedHeadMemberFormulaAt tm T configBase choiceWire tape target
          direction.val := by
  simp [movedHeadDirectionCount, List.ofFn_succ, movedHeadMemberFormulaAt,
    movedHeadDirectionAt]

private theorem movedHeadCaseSelectedAt_eq
    (tm : NTM k) (tape : TapeSlot k) (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    movedHeadCaseSelectedAt tm tape directionCode =
      effectCaseSelectedAt tm (fun effect =>
        decide (effect.move tape = movedHeadDirectionAt directionCode)) := by
  change directionCode < 3 at hdirection
  interval_cases directionCode <;> rfl

private theorem movedHeadDirectionAt_code
    (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    (match movedHeadDirectionAt directionCode with
      | .left => 0
      | .right => 1
      | .stay => 2) = directionCode := by
  change directionCode < 3 at hdirection
  interval_cases directionCode <;> rfl

private theorem size_effectFormula_eq_scheduleSize_movedHead
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) :
    (effectFormula tm T configBase choiceWire selects).size =
      effectFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) := by
  have hlength := congrArg List.length
    (compileRaw_effectFormula_eq_schedule tm T configBase choiceWire 0 selects)
  simpa using hlength

private theorem size_predecessorHeadFormula_eq_movedHeadPredecessorSize
    (tm : NTM k) (T configBase : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (direction : Dir3) :
    (predecessorHeadFormula tm T configBase tape target direction).size =
      movedHeadPredecessorSize T := by
  have hlength := congrArg List.length
    (compileRaw_predecessorHeadFormula_eq_schedule tm T configBase 0 tape
      target direction)
  simpa [movedHeadPredecessorSize] using hlength

private theorem size_movedHeadMemberFormulaAt
    (tm : NTM k) (T configBase choiceWire : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    (movedHeadMemberFormulaAt tm T configBase choiceWire tape target
      directionCode).size =
      movedHeadMemberSizeAt (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        directionCode := by
  unfold movedHeadMemberFormulaAt selectedMoveFormula
  rw [BoolFormula.size]
  rw [size_effectFormula_eq_scheduleSize_movedHead]
  rw [size_predecessorHeadFormula_eq_movedHeadPredecessorSize]
  rw [movedHeadMemberSizeAt, ite_eq_left hdirection, movedHeadEffectSizeAt]
  rw [movedHeadCaseSelectedAt_eq tm tape directionCode hdirection]

private theorem compileRaw_movedHeadMemberFormulaAt
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) (directionCode : ℕ)
    (hdirection : directionCode < movedHeadDirectionCount) :
    BoolFormula.compileRaw
        (movedHeadMemberAvailable (transitionCases tm).length k T available
          (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
          directionCode)
        (movedHeadMemberFormulaAt tm T configBase choiceWire tape target
          directionCode) =
      movedHeadMemberBlock (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available tape.index.val target.val
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
        directionCode := by
  let selects := fun effect : TransitionEffect tm =>
    decide (effect.move tape = movedHeadDirectionAt directionCode)
  let effectChild := selectedMoveFormula tm T configBase choiceWire tape
    (movedHeadDirectionAt directionCode)
  let predecessorChild := predecessorHeadFormula tm T configBase tape target
    (movedHeadDirectionAt directionCode)
  let memberAvailable :=
    movedHeadMemberAvailable (transitionCases tm).length k T available
      (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) directionCode
  have hcode : (match movedHeadDirectionAt directionCode with
      | .left => 0
      | .right => 1
      | .stay => 2) = directionCode := by
    exact movedHeadDirectionAt_code directionCode hdirection
  have hselected : movedHeadCaseSelectedAt tm tape directionCode =
      effectCaseSelectedAt tm selects := by
    exact movedHeadCaseSelectedAt_eq tm tape directionCode hdirection
  have heffectSize : effectChild.size =
      movedHeadEffectSizeAt (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        directionCode := by
    unfold effectChild selectedMoveFormula movedHeadEffectSizeAt
    rw [hselected]
    exact size_effectFormula_eq_scheduleSize_movedHead tm T configBase
      choiceWire selects
  have hpredecessorSize : predecessorChild.size =
      movedHeadPredecessorSize T := by
    exact size_predecessorHeadFormula_eq_movedHeadPredecessorSize tm T
      configBase tape target (movedHeadDirectionAt directionCode)
  have heffectCompile : BoolFormula.compileRaw memberAvailable effectChild =
      effectFormulaSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire memberAvailable
        (movedHeadCaseSelectedAt tm tape directionCode)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
    unfold effectChild selectedMoveFormula
    have hcompile := compileRaw_effectFormula_eq_schedule tm T configBase
      choiceWire memberAvailable selects
    rw [← hselected] at hcompile
    exact hcompile
  have hpredecessorCompile : BoolFormula.compileRaw
        (memberAvailable + movedHeadEffectSizeAt (transitionCases tm).length k
          T (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
          directionCode)
        predecessorChild =
      predecessorHeadFormulaSchedule (Fintype.card tm.Q) T configBase
        (movedHeadPredecessorAvailable (transitionCases tm).length k T
          available (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
          directionCode)
        tape.index.val target.val directionCode := by
    have hcompile := compileRaw_predecessorHeadFormula_eq_schedule tm T
      configBase
      (movedHeadPredecessorAvailable (transitionCases tm).length k T available
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) directionCode)
      tape target (movedHeadDirectionAt directionCode)
    calc
      BoolFormula.compileRaw
          (memberAvailable +
            movedHeadEffectSizeAt (transitionCases tm).length k T
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
              directionCode)
          predecessorChild =
        predecessorHeadFormulaSchedule (Fintype.card tm.Q) T configBase
          (movedHeadPredecessorAvailable (transitionCases tm).length k T
            available (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm) directionCode)
          tape.index.val target.val
          (match movedHeadDirectionAt directionCode with
          | .left => 0
          | .right => 1
          | .stay => 2) := by
            simp [memberAvailable, predecessorChild, movedHeadPredecessorAvailable]
            exact hcompile
      _ = _ := congrArg (fun code =>
        predecessorHeadFormulaSchedule (Fintype.card tm.Q) T configBase
          (movedHeadPredecessorAvailable (transitionCases tm).length k T
            available (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm) directionCode)
          tape.index.val target.val code) hcode
  change BoolFormula.compileRaw memberAvailable
    (.conj effectChild predecessorChild) = _
  simp only [BoolFormula.compileRaw]
  rw [heffectCompile, heffectSize, hpredecessorCompile]
  unfold movedHeadMemberBlock
  simp [memberAvailable, movedHeadConjunctionGate,
    movedHeadPredecessorAvailable, BoolFormula.rawOutputWire, heffectSize,
    hpredecessorSize, List.append_assoc]

private theorem compileRawOutputs_eq_movedHeadMemberGates
    (count available : ℕ) (formulaAt : ℕ → BoolFormula)
    (blockAt : ℕ → CircuitCode.RawCircuit) (sizeAt : ℕ → ℕ)
    (hsize : ∀ index < count, (formulaAt index).size = sizeAt index)
    (hcompile : ∀ index < count,
      BoolFormula.compileRaw (available + prefixSize sizeAt index)
          (formulaAt index) = blockAt index) :
    (BoolFormula.compileRawOutputs available
      (List.ofFn fun index : Fin count => formulaAt index.val)).circuit =
        indexedGateBlocks count blockAt := by
  induction count generalizing available formulaAt blockAt sizeAt with
  | zero => simp [BoolFormula.compileRawOutputs, indexedGateBlocks]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [BoolFormula.compileRawOutputs, indexedGateBlocks,
        Fin.val_zero]
      have hsizeZero := hsize 0 (by omega)
      have hcompileZero := hcompile 0 (by omega)
      simp only [prefixSize_zero, Nat.add_zero] at hcompileZero
      rw [hcompileZero]
      have htailSize : ∀ index < count,
          (formulaAt (index + 1)).size = sizeAt (index + 1) := by
        intro index hindex
        exact hsize (index + 1) (by omega)
      have htailCompile : ∀ index < count,
          BoolFormula.compileRaw
              ((available + sizeAt 0) +
                prefixSize (fun next => sizeAt (next + 1)) index)
              (formulaAt (index + 1)) = blockAt (index + 1) := by
        intro index hindex
        have h := hcompile (index + 1) (by omega)
        rw [movedHead_prefixSize_shift sizeAt index] at h
        simpa [Nat.add_assoc] using h
      have htail := ih (available + sizeAt 0)
        (fun index => formulaAt (index + 1))
        (fun index => blockAt (index + 1))
        (fun index => sizeAt (index + 1)) htailSize htailCompile
      rw [hsizeZero]
      exact congrArg (fun tail => blockAt 0 ++ tail) htail

private theorem movedHeadFormulaSizeLookup_eq
    (tm : NTM k) (T configBase choiceWire : ℕ) (tape : TapeSlot k)
    (target : Fin (T + 1)) :
    (fun index =>
      ((((List.ofFn fun direction : Fin movedHeadDirectionCount =>
        movedHeadMemberFormulaAt tm T configBase choiceWire tape target
          direction.val).map BoolFormula.size)[index]?).getD 0)) =
      movedHeadMemberSizeAt (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) := by
  funext index
  by_cases hindex : index < movedHeadDirectionCount
  · rw [List.getElem?_eq_getElem (by simp [hindex])]
    simp only [List.getElem_map, List.getElem_ofFn, Option.getD_some]
    exact size_movedHeadMemberFormulaAt tm T configBase choiceWire tape target
      index hindex
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [movedHeadMemberSizeAt, hindex]

theorem compileRaw_movedHeadFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) :
    BoolFormula.compileRaw available
        (movedHeadFormula tm T configBase choiceWire tape target) =
      movedHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available tape.index.val
        target.val (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  let formulaAt : ℕ → BoolFormula :=
    movedHeadMemberFormulaAt tm T configBase choiceWire tape target
  let sizeAt : ℕ → ℕ :=
    movedHeadMemberSizeAt (transitionCases tm).length k T
      (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
  let blockAt : ℕ → CircuitCode.RawCircuit :=
    movedHeadMemberBlock (transitionCases tm).length (Fintype.card tm.Q) k T
      configBase choiceWire available tape.index.val target.val
      (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
      (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
      (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
  unfold movedHeadFormula
  rw [compileRaw_disjs_eq_indexed]
  rw [movedHeadFormulaList_eq_indexed]
  have hmembers := compileRawOutputs_eq_movedHeadMemberGates
    movedHeadDirectionCount available formulaAt blockAt sizeAt
    (by
      intro directionCode hdirection
      exact size_movedHeadMemberFormulaAt tm T configBase choiceWire tape
        target directionCode hdirection)
    (by
      intro directionCode hdirection
      exact compileRaw_movedHeadMemberFormulaAt tm T configBase choiceWire
        available tape target directionCode hdirection)
  have hsizes := movedHeadFormulaSizeLookup_eq tm T configBase choiceWire tape
    target
  unfold movedHeadFormulaSchedule movedHeadMemberGates
  rw [hmembers, hsizes]
  simp only [List.length_ofFn]
  simp only [blockAt]

end Serializer

end CircuitUnrolling

end Complexity
