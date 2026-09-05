/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Next
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Step.Defs

/-!
# Numeric packed-step schedules -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

private theorem step_prefixSize_shift (sizeAt : ℕ → ℕ) (count : ℕ) :
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

private theorem length_indexedGateBlocks_variable_step
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
      rw [step_prefixSize_shift]

private theorem compileRawOutputs_eq_indexedGateBlocks_step
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
        rw [step_prefixSize_shift sizeAt index] at h
        simpa [Nat.add_assoc] using h
      have htail := ih (available + sizeAt 0)
        (fun index => formulaAt (index + 1))
        (fun index => blockAt (index + 1))
        (fun index => sizeAt (index + 1)) htailSize htailCompile
      rw [hsizeZero]
      exact congrArg (fun tail => blockAt 0 ++ tail) htail

private noncomputable def stepSourceFormulaAt
    (tm : NTM k) (T configBase choiceWire index : ℕ) : BoolFormula :=
  nextFormula tm T configBase choiceWire (stepConfigAtomAt tm T index)

private theorem stepFormulas_eq_ofFn_source
    (tm : NTM k) (T configBase choiceWire : ℕ) :
    stepFormulas tm T configBase choiceWire =
      List.ofFn fun index : Fin
        (stepAtomCount (Fintype.card tm.Q) k T) =>
          stepSourceFormulaAt tm T configBase choiceWire index.val := by
  simp [stepFormulas, configAtoms, stepSourceFormulaAt, stepConfigAtomAt,
    stepAtomCount, configWidth, Function.comp_def]
  and_intros <;> rfl

private theorem size_stepSourceFormulaAt
    (tm : NTM k) (T configBase choiceWire index : ℕ)
    (hindex : index < stepAtomCount (Fintype.card tm.Q) k T) :
    (stepSourceFormulaAt tm T configBase choiceWire index).size =
      stepFormulaSizeAt (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) index := by
  unfold stepSourceFormulaAt
  rw [size_nextFormula_eq_scheduleSize]
  simp only [stepFormulaSizeAt, ite_eq_left hindex]
  unfold stepAtomKindAt stepAtomEffectSelectedAt
  rfl

private theorem compileRaw_stepSourceFormulaAt
    (tm : NTM k) (T configBase choiceWire available index : ℕ) :
    BoolFormula.compileRaw
        (stepFormulaAvailable (transitionCases tm).length
          (Fintype.card tm.Q) k T available (stepAtomKindAt tm T)
          (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm) index)
        (stepSourceFormulaAt tm T configBase choiceWire index) =
      stepFormulaBlock (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available (nextHaltStateIndex tm)
        (stepAtomKindAt tm T) (stepAtomStateIndexAt tm T)
        (stepAtomTapeIndexAt tm T) (stepAtomPositionAt tm T)
        (stepAtomSymbolIndexAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) index := by
  unfold stepSourceFormulaAt stepFormulaBlock stepAtomKindAt
    stepAtomStateIndexAt stepAtomTapeIndexAt stepAtomPositionAt
    stepAtomSymbolIndexAt stepAtomEffectSelectedAt
  exact compileRaw_nextFormula_eq_schedule tm T configBase choiceWire
    (stepFormulaAvailable (transitionCases tm).length (Fintype.card tm.Q) k T
      available (fun index => nextAtomKind (stepConfigAtomAt tm T index))
      (fun atomIndex phase caseIndex =>
        nextAtomEffectSelectedAt tm (stepConfigAtomAt tm T atomIndex) phase
          caseIndex)
      (effectCaseChoiceAt tm) index)
    (stepConfigAtomAt tm T index)

theorem length_stepFormulaBlock_internal
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
          choiceAt atomIndex := by
  unfold stepFormulaBlock
  rw [length_nextFormulaSchedule]
  simp [stepFormulaSizeAt, hindex]

theorem length_stepFormulaGates_internal
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
            choiceAt) (stepAtomCount stateCount workCount T) := by
  unfold stepFormulaGates
  apply length_indexedGateBlocks_variable_step
  intro atomIndex hindex
  exact length_stepFormulaBlock_internal caseCount stateCount workCount T
    configBase choiceWire available haltStateIndex kindAt atomStateIndexAt
    atomTapeIndexAt atomPositionAt atomSymbolIndexAt selectedAt choiceAt
    caseStateIndexAt inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt
    atomIndex hindex

theorem length_stepPackedCopies_internal
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool) :
    (stepPackedCopies caseCount stateCount workCount T available kindAt
      selectedAt choiceAt).length = stepAtomCount stateCount workCount T := by
  simp [stepPackedCopies]

theorem getElem_stepPackedCopies_internal
    (caseCount stateCount workCount T available : ℕ) (kindAt : ℕ → ℕ)
    (selectedAt : ℕ → ℕ → ℕ → Bool) (choiceAt : ℕ → Bool)
    (atomIndex : Fin (stepAtomCount stateCount workCount T)) :
    (stepPackedCopies caseCount stateCount workCount T available kindAt
      selectedAt choiceAt)[atomIndex.val]'(by
        rw [length_stepPackedCopies_internal]
        exact atomIndex.isLt) =
      stepPackedCopyGate caseCount stateCount workCount T available kindAt
        selectedAt choiceAt atomIndex.val := by
  unfold stepPackedCopies stepPackedCopyGate stepFormulaOutputRef
  exact getElem_indexedBatchCopies available
    (stepAtomCount stateCount workCount T)
    (stepFormulaSizeAt caseCount stateCount workCount T kindAt selectedAt
      choiceAt) atomIndex

theorem length_stepSchedule_internal
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
          choiceAt := by
  simp [stepSchedule, stepScheduleSize, length_stepFormulaGates_internal,
    length_stepPackedCopies_internal]

private theorem stepFormulaSizeLookup_eq
    (tm : NTM k) (T configBase choiceWire : ℕ) :
    (fun index =>
      (((stepFormulas tm T configBase choiceWire).map
        BoolFormula.size)[index]?).getD 0) =
      stepFormulaSizeAt (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) := by
  funext index
  rw [stepFormulas_eq_ofFn_source]
  by_cases hindex :
      index < stepAtomCount (Fintype.card tm.Q) k T
  · rw [List.getElem?_eq_getElem (by simp [hindex])]
    simp only [List.getElem_map, List.getElem_ofFn, Option.getD_some]
    exact size_stepSourceFormulaAt tm T configBase choiceWire index hindex
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [stepFormulaSizeAt, hindex]

private theorem compileRawOutputs_stepFormulas_eq_formulaGates
    (tm : NTM k) (T configBase choiceWire available : ℕ) :
    (BoolFormula.compileRawOutputs available
      (stepFormulas tm T configBase choiceWire)).circuit =
      stepFormulaGates (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available (nextHaltStateIndex tm)
        (stepAtomKindAt tm T) (stepAtomStateIndexAt tm T)
        (stepAtomTapeIndexAt tm T) (stepAtomPositionAt tm T)
        (stepAtomSymbolIndexAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  rw [stepFormulas_eq_ofFn_source]
  unfold stepFormulaGates
  apply compileRawOutputs_eq_indexedGateBlocks_step
  · intro index hindex
    exact size_stepSourceFormulaAt tm T configBase choiceWire index hindex
  · intro index _hindex
    simpa [stepFormulaAvailable] using
      compileRaw_stepSourceFormulaAt tm T configBase choiceWire available index

theorem stepFragment_eq_stepSchedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ) :
    stepFragment tm T configBase choiceWire available =
      stepSchedule (transitionCases tm).length (Fintype.card tm.Q) k T
        configBase choiceWire available (nextHaltStateIndex tm)
        (stepAtomKindAt tm T) (stepAtomStateIndexAt tm T)
        (stepAtomTapeIndexAt tm T) (stepAtomPositionAt tm T)
        (stepAtomSymbolIndexAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold stepFragment
  rw [compileRawBatch_eq_indexed]
  rw [compileRawOutputs_stepFormulas_eq_formulaGates]
  rw [stepFormulaSizeLookup_eq]
  simp only [stepSchedule, stepPackedCopies, length_stepFormulas, stepAtomCount,
    configWidth]

theorem stepFragmentSize_eq_stepScheduleSize_internal
    (tm : NTM k) (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire =
      stepScheduleSize (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) := by
  have hlength := congrArg List.length
    (stepFragment_eq_stepSchedule_internal tm T configBase choiceWire 0)
  simpa only [length_stepFragment, length_stepSchedule_internal] using hlength

theorem stepOutputBase_eq_stepScheduleOutputBase_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ) :
    stepOutputBase tm T configBase choiceWire available =
      stepScheduleOutputBase (transitionCases tm).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm T)
        (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm) := by
  unfold stepOutputBase BoolFormula.rawBatchOutputBase
    stepScheduleOutputBase
  rw [← prefixSize_formulaSizes]
  rw [stepFormulaSizeLookup_eq]
  rw [length_stepFormulas]
  simp [stepAtomCount, configWidth]

theorem stepScheduleOutputRef_configIndex_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (atom : ConfigAtom tm T) :
    stepScheduleOutputRef (transitionCases tm).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm T)
        (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm)
        (configIndex tm T atom) =
      configWire tm T (stepOutputBase tm T configBase choiceWire available)
        atom := by
  unfold stepScheduleOutputRef
  rw [configWire_stepOutputBase]
  rw [stepOutputBase_eq_stepScheduleOutputBase_internal]

end Serializer

end CircuitUnrolling

end Complexity
