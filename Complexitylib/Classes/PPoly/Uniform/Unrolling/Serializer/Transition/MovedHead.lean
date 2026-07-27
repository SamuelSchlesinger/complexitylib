/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.MovedHead.Internal

/-!
# Numeric moved-head schedules

This module exposes a natural-index stream for `movedHeadFormula`. The three
direction members are compiled forward; each contains an effect phase, a
predecessor-head phase, and one conjunction gate. A false identity and three
reverse disjunction connectors complete the stream.

## Main results

- `length_movedHeadFormulaSchedule` gives the exact total gate count.
- The member and child-phase lookup theorems expose the streaming boundaries.
- `compileRaw_movedHeadFormula_eq_schedule` proves literal raw-list equality.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- One in-range direction block has its advertised numeric size. -/
@[simp] theorem length_movedHeadMemberBlock
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
          directionCode :=
  length_movedHeadMemberBlock_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    directionCode hdirection

/-- The complete forward member phase is the prefix sum of its three sizes. -/
@[simp] theorem length_movedHeadMemberGates
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
          movedHeadDirectionCount :=
  length_movedHeadMemberGates_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- A natural direction counter and in-block offset recover the corresponding
member gate. -/
theorem getElem_movedHeadMemberGates
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
            rw [length_movedHeadMemberGates]
            exact lt_of_lt_of_le (Nat.add_lt_add_left hoffset _) (by
              rw [← prefixSize_succ]
              exact prefixSize_mono_movedHead_internal _ (by omega))) =
      (movedHeadMemberBlock caseCount stateCount workCount T configBase
        choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
        inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
        directionCode)[offset]'(by
          rw [length_movedHeadMemberBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            directionCode hdirection]
          exact hoffset) :=
  getElem_movedHeadMemberGates_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    directionCode offset hdirection hoffset

/-- Offsets before the effect-size boundary select the effect child stream. -/
theorem getElem_movedHeadMemberBlock_effect
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
          rw [length_movedHeadMemberBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            directionCode hdirection]
          simp [movedHeadMemberSizeAt, hdirection]
          omega) =
      (effectFormulaSchedule caseCount stateCount workCount T configBase
        choiceWire
        (movedHeadMemberAvailable caseCount workCount T available selectedAt
          choiceAt directionCode)
        (selectedAt directionCode) choiceAt stateIndexAt inputSymbolIndexAt
        outputSymbolIndexAt workSymbolIndexAt)[offset]'(by
          rw [length_effectFormulaSchedule]
          exact hoffset) :=
  getElem_movedHeadMemberBlock_effect_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    directionCode offset hdirection hoffset

/-- The next fixed-width offsets select the predecessor-head child stream. -/
theorem getElem_movedHeadMemberBlock_predecessor
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
            rw [length_movedHeadMemberBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              directionCode hdirection]
            simp [movedHeadMemberSizeAt, hdirection]
            omega) =
      (predecessorHeadFormulaSchedule stateCount T configBase
        (movedHeadPredecessorAvailable caseCount workCount T available
          selectedAt choiceAt directionCode)
        tapeIndex target directionCode)[offset]'(by
          rw [length_predecessorHeadFormulaSchedule]
          exact hoffset) :=
  getElem_movedHeadMemberBlock_predecessor_internal caseCount stateCount
    workCount T configBase choiceWire available tapeIndex target selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt directionCode offset hdirection hoffset

/-- The final offset of each direction block is its conjunction gate. -/
theorem getElem_movedHeadMemberBlock_conjunction
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
            rw [length_movedHeadMemberBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              directionCode hdirection]
            simp [movedHeadMemberSizeAt, hdirection]) =
      movedHeadConjunctionGate caseCount workCount T available selectedAt
        choiceAt directionCode :=
  getElem_movedHeadMemberBlock_conjunction_internal caseCount stateCount
    workCount T configBase choiceWire available tapeIndex target selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt directionCode hdirection

/-- The complete stream is members, one false identity, and three connectors. -/
@[simp] theorem length_movedHeadFormulaSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      tapeIndex target : ℕ)
    (selectedAt : ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (movedHeadFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available tapeIndex target selectedAt choiceAt stateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        movedHeadFormulaScheduleSize caseCount workCount T selectedAt
          choiceAt :=
  length_movedHeadFormulaSchedule_internal caseCount stateCount workCount T
    configBase choiceWire available tapeIndex target selectedAt choiceAt
    stateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- The gate after the forward member phase is the false identity. -/
theorem getElem_movedHeadFormulaSchedule_identity
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
            rw [length_movedHeadFormulaSchedule]
            simp [movedHeadFormulaScheduleSize]
            omega) = CircuitCode.RawGate.constant 0 false :=
  getElem_movedHeadFormulaSchedule_identity_internal caseCount stateCount
    workCount T configBase choiceWire available tapeIndex target selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt

/-- Connector rank is a natural upward counter visiting direction members in
reverse order. -/
theorem getElem_movedHeadFormulaSchedule_connector
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
            rw [length_movedHeadFormulaSchedule]
            simp [movedHeadFormulaScheduleSize]) =
      indexedRightFoldConnector .or available movedHeadDirectionCount
        (movedHeadMemberSizeAt caseCount workCount T selectedAt choiceAt)
        rank.val :=
  getElem_movedHeadFormulaSchedule_connector_internal caseCount stateCount
    workCount T configBase choiceWire available tapeIndex target selectedAt
    choiceAt stateIndexAt inputSymbolIndexAt outputSymbolIndexAt
    workSymbolIndexAt rank

/-- Exact raw compilation order of a non-halted moved-head formula. -/
theorem compileRaw_movedHeadFormula_eq_schedule
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) :
    BoolFormula.compileRaw available
        (movedHeadFormula tm T configBase choiceWire tape target) =
      movedHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available tape.index.val
        target.val (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  compileRaw_movedHeadFormula_eq_schedule_internal tm T configBase choiceWire
    available tape target

end Serializer

end CircuitUnrolling

end Complexity
