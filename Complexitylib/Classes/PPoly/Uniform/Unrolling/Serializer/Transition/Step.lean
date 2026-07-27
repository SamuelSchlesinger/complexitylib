/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Step.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Step.Internal

/-!
# Numeric schedules for one packed transition step

This module exposes the canonical whole-step schedule. It streams one numeric
`nextFormula` block per configuration atom in explicit wire order, then emits
one packed-output copy per atom in that same order.

## Main results

- `length_stepFormulaBlock` and `length_stepFormulaGates` expose exact formula
  block and prefix sizes.
- `getElem_stepPackedCopies` identifies every delayed output reference.
- `length_stepSchedule` gives the exact whole-step gate count.
- `stepFragment_eq_stepSchedule` proves literal equality with the existing
  packed transition fragment.
- `stepOutputBase_eq_stepScheduleOutputBase` and
  `stepScheduleOutputRef_configIndex` connect numeric output references to the
  public successor-configuration layout.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- An in-range atom block has exactly its advertised numeric size. -/
@[simp] theorem length_stepFormulaBlock
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (atomIndex : ℕ)
    (hindex : atomIndex < stepAtomCount stateCount workCount T) :
    (stepFormulaBlock caseCount stateCount workCount T configBase choiceWire
      available haltStateIndex kindAt atomStateIndexAt atomTapeIndexAt
      atomPositionAt atomSymbolIndexAt selectedAt choiceAt caseStateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
      atomIndex).length =
        stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
          choiceAt atomIndex :=
  length_stepFormulaBlock_internal caseCount stateCount workCount T configBase
    choiceWire available haltStateIndex kindAt atomStateIndexAt
    atomTapeIndexAt atomPositionAt atomSymbolIndexAt selectedAt choiceAt
    caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    atomIndex hindex

/-- The complete forward formula phase is the prefix sum of all atom sizes. -/
@[simp] theorem length_stepFormulaGates
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (stepFormulaGates caseCount stateCount workCount T configBase choiceWire
      available haltStateIndex kindAt atomStateIndexAt atomTapeIndexAt
      atomPositionAt atomSymbolIndexAt selectedAt choiceAt caseStateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        prefixSize
          (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
            choiceAt) (stepAtomCount stateCount workCount T) :=
  length_stepFormulaGates_internal caseCount stateCount workCount T configBase
    choiceWire available haltStateIndex kindAt atomStateIndexAt
    atomTapeIndexAt atomPositionAt atomSymbolIndexAt selectedAt choiceAt
    caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- The packed suffix contains exactly one copy gate per atom. -/
@[simp] theorem length_stepPackedCopies
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    (stepPackedCopies caseCount stateCount workCount T available kindAt
      selectedAt choiceAt).length = stepAtomCount stateCount workCount T :=
  length_stepPackedCopies_internal caseCount stateCount workCount T available
    kindAt selectedAt choiceAt

/-- Packed-copy index recovers the formula-output reference computed by the
numeric prefix oracle. -/
theorem getElem_stepPackedCopies
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : Fin (stepAtomCount stateCount workCount T)) :
    (stepPackedCopies caseCount stateCount workCount T available kindAt
      selectedAt choiceAt)[atomIndex.val]'(by
        rw [length_stepPackedCopies]
        exact atomIndex.isLt) =
      stepPackedCopyGate caseCount stateCount workCount T available kindAt
        selectedAt choiceAt atomIndex.val :=
  getElem_stepPackedCopies_internal caseCount stateCount workCount T available
    kindAt selectedAt choiceAt atomIndex

/-- Exact gate count of the complete numeric packed step. -/
@[simp] theorem length_stepSchedule
    (caseCount stateCount workCount T configBase choiceWire available
      haltStateIndex : ℕ)
    (kindAt atomStateIndexAt atomTapeIndexAt atomPositionAt
      atomSymbolIndexAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (stepSchedule caseCount stateCount workCount T configBase choiceWire
      available haltStateIndex kindAt atomStateIndexAt atomTapeIndexAt
      atomPositionAt atomSymbolIndexAt selectedAt choiceAt caseStateIndexAt
      inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt).length =
        stepScheduleSize caseCount stateCount workCount T kindAt selectedAt
          choiceAt :=
  length_stepSchedule_internal caseCount stateCount workCount T configBase
    choiceWire available haltStateIndex kindAt atomStateIndexAt
    atomTapeIndexAt atomPositionAt atomSymbolIndexAt selectedAt choiceAt
    caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt

/-- Literal equality between the existing packed transition fragment and the
canonical numeric whole-step schedule. -/
theorem stepFragment_eq_stepSchedule
    (tm : NTM k) (T configBase choiceWire available : ℕ) :
    stepFragment tm T configBase choiceWire available =
      stepSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available (nextHaltStateIndex tm)
        (stepAtomKindAt tm T) (stepAtomStateIndexAt tm T)
        (stepAtomTapeIndexAt tm T) (stepAtomPositionAt tm T)
        (stepAtomSymbolIndexAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) :=
  stepFragment_eq_stepSchedule_internal tm T configBase choiceWire available

/-- The existing packed fragment size is exactly the numeric schedule count. -/
theorem stepFragmentSize_eq_stepScheduleSize
    (tm : NTM k) (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire =
      stepScheduleSize (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) :=
  stepFragmentSize_eq_stepScheduleSize_internal tm T configBase choiceWire

/-- The numeric prefix total is exactly the existing packed successor base. -/
theorem stepOutputBase_eq_stepScheduleOutputBase
    (tm : NTM k) (T configBase choiceWire available : ℕ) :
    stepOutputBase tm T configBase choiceWire available =
      stepScheduleOutputBase (transitionCases tm).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm T)
        (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm) :=
  stepOutputBase_eq_stepScheduleOutputBase_internal tm T configBase choiceWire
    available

/-- A numeric packed-output reference at an atom's explicit index is exactly
its successor-configuration wire. -/
theorem stepScheduleOutputRef_configIndex
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (atom : ConfigAtom tm T) :
    stepScheduleOutputRef (transitionCases tm).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm T)
        (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm)
        (configIndex tm T atom) =
      configWire tm T (stepOutputBase tm T configBase choiceWire available)
        atom :=
  stepScheduleOutputRef_configIndex_internal tm T configBase choiceWire
    available atom

end Serializer

end CircuitUnrolling

end Complexity
