/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Effect.Defs

/-!
# Numeric transition-effect schedules -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

private theorem prefixSize_shift (sizeAt : ℕ → ℕ) (count : ℕ) :
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

private theorem length_indexedGateBlocks_variable
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
      rw [prefixSize_shift]

theorem length_effectFormulaCaseBlock_internal
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (caseIndex : ℕ)
    (hcase : caseIndex < caseCount) :
    (effectFormulaCaseBlock caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt caseIndex).length =
        effectFormulaSizeAt caseCount workCount T selectedAt choiceAt
          caseIndex := by
  unfold effectFormulaCaseBlock effectFormulaSizeAt effectFormulaCaseSize
  rw [ite_eq_left hcase]
  by_cases hselected : selectedAt caseIndex
  · simp [hselected, length_caseFormulaSchedule]
  · simp [hselected]

theorem length_effectFormulaCaseGates_internal
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaCaseGates caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        prefixSize
          (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
          caseCount := by
  unfold effectFormulaCaseGates
  apply length_indexedGateBlocks_variable
  intro caseIndex hcase
  exact length_effectFormulaCaseBlock_internal caseCount stateCount workCount T
    configBase choiceWire available selectedAt choiceAt stateIndexAt
    inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt caseIndex hcase

theorem length_effectFormulaSchedule_internal
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt).length =
        effectFormulaScheduleSize caseCount workCount T selectedAt choiceAt := by
  simp [effectFormulaSchedule, effectFormulaScheduleSize,
    length_effectFormulaCaseGates_internal]
  omega

theorem getElem_effectFormulaSchedule_identity_internal
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
          (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
          caseCount]'(by
            rw [length_effectFormulaSchedule_internal]
            simp [effectFormulaScheduleSize]
            omega) = CircuitCode.RawGate.constant 0 false := by
  unfold effectFormulaSchedule
  erw [List.getElem_append_left]
  · rw [List.getElem_append_right]
    all_goals simp [length_effectFormulaCaseGates_internal]
  · simp [length_effectFormulaCaseGates_internal]

theorem getElem_effectFormulaSchedule_connector_internal
    (caseCount stateCount workCount T configBase choiceWire available : ℕ)
    (selectedAt choiceAt : ℕ → Bool)
    (stateIndexAt inputSymbolIndexAt outputSymbolIndexAt : ℕ → ℕ)
    (workSymbolIndexAt : ℕ → ℕ → ℕ) (rank : Fin caseCount) :
    (effectFormulaSchedule caseCount stateCount workCount T configBase
      choiceWire available selectedAt choiceAt stateIndexAt inputSymbolIndexAt
      outputSymbolIndexAt workSymbolIndexAt)[
        prefixSize
            (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
            caseCount +
          1 + rank.val]'(by
            rw [length_effectFormulaSchedule_internal]
            simp [effectFormulaScheduleSize]
            ) =
      indexedRightFoldConnector .or available caseCount
        (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
        rank.val := by
  unfold effectFormulaSchedule
  erw [List.getElem_append_right]
  · have hindex :
        prefixSize
              (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt)
              caseCount +
            1 + rank.val -
              (effectFormulaCaseGates caseCount stateCount workCount T
                configBase choiceWire available selectedAt choiceAt stateIndexAt
                inputSymbolIndexAt outputSymbolIndexAt workSymbolIndexAt ++
                [CircuitCode.RawGate.constant 0 false]).length = rank.val := by
        simp [length_effectFormulaCaseGates_internal]
    simp only [hindex]
    exact getElem_indexedRightFoldConnectors .or available caseCount
      (effectFormulaSizeAt caseCount workCount T selectedAt choiceAt) rank
  · simp [length_effectFormulaCaseGates_internal]

private theorem compileRawOutputs_eq_indexedGateBlocks
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
      simp only [BoolFormula.compileRawOutputs, indexedGateBlocks, Fin.val_zero]
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
        rw [prefixSize_shift sizeAt index] at h
        simpa [Nat.add_assoc] using h
      have htail := ih (available + sizeAt 0)
        (fun index => formulaAt (index + 1))
        (fun index => blockAt (index + 1))
        (fun index => sizeAt (index + 1)) htailSize htailCompile
      rw [hsizeZero]
      exact congrArg (fun tail => blockAt 0 ++ tail) htail

private noncomputable def effectFormulaAt
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ) : BoolFormula :=
  if hcase : caseIndex < (transitionCases tm).length then
    let view := (transitionCases tm)[caseIndex]'hcase
    if selects view.effect then caseFormula tm T configBase choiceWire view
    else .fls
  else .fls

private theorem effectFormulaList_eq_indexed
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) :
    (transitionCases tm).map (fun view =>
        if selects view.effect then caseFormula tm T configBase choiceWire view
        else .fls) =
      List.ofFn fun index : Fin (transitionCases tm).length =>
        effectFormulaAt tm T configBase choiceWire selects index.val := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hcase : index < (transitionCases tm).length := by
      simpa using hleft
    simp only [List.getElem_map, List.getElem_ofFn]
    simp [effectFormulaAt, hcase]

private theorem size_caseFormula_eq_scheduleSize
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (view : TransitionCase tm) :
    (caseFormula tm T configBase choiceWire view).size =
      caseFormulaScheduleSize k T view.choice := by
  have hlength := congrArg List.length
    (compileRaw_caseFormula_eq_schedule tm T configBase choiceWire 0
      view)
  simpa using hlength

private theorem size_effectFormulaAt
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (hcase : caseIndex < (transitionCases tm).length) :
    (effectFormulaAt tm T configBase choiceWire selects caseIndex).size =
      effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) caseIndex := by
  let view := (transitionCases tm)[caseIndex]'hcase
  by_cases hselected : selects view.effect
  · simp [effectFormulaAt, effectFormulaSizeAt, effectFormulaCaseSize,
      effectCaseSelectedAt, effectCaseChoiceAt, hcase, view, hselected,
      size_caseFormula_eq_scheduleSize]
  · simp [effectFormulaAt, effectFormulaSizeAt, effectFormulaCaseSize,
      effectCaseSelectedAt, hcase, view, hselected, BoolFormula.size]

private theorem compileRaw_effectFormulaAt
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (hcase : caseIndex < (transitionCases tm).length) :
    BoolFormula.compileRaw
        (available + prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k T
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          caseIndex)
        (effectFormulaAt tm T configBase choiceWire selects caseIndex) =
      effectFormulaCaseBlock (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
        caseIndex := by
  let view := (transitionCases tm)[caseIndex]'hcase
  by_cases hselected : selects view.effect
  · have hcompile := compileRaw_caseFormula_eq_schedule tm T
      configBase choiceWire
      (effectFormulaCaseAvailable (transitionCases tm).length k T available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) caseIndex)
      view
    have hwork :
        (fun index => if hindex : index < k then
          (symbolIndex (view.workRead ⟨index, hindex⟩)).val else 0) =
          effectCaseWorkSymbolIndexAt tm caseIndex := by
      funext workIndex
      by_cases hworkIndex : workIndex < k
      · simp only [effectCaseWorkSymbolIndexAt, dite_eq_left hcase,
          dite_eq_left hworkIndex]
        dsimp only [view]
      · simp [effectCaseWorkSymbolIndexAt, hcase, hworkIndex]
    rw [hwork] at hcompile
    simpa [effectFormulaAt, effectFormulaCaseBlock,
      effectFormulaCaseAvailable, effectCaseSelectedAt, effectCaseChoiceAt,
      effectCaseStateIndexAt, effectCaseInputSymbolIndexAt,
      effectCaseOutputSymbolIndexAt, hcase, view, hselected] using hcompile
  · simp [effectFormulaAt, effectFormulaCaseBlock, effectCaseSelectedAt,
      hcase, view, hselected, BoolFormula.compileRaw]

private theorem effectFormulaSizeLookup_eq
    (tm : NTM k) (T configBase choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) :
    (fun index =>
      ((((List.ofFn fun caseIndex : Fin (transitionCases tm).length =>
        effectFormulaAt tm T configBase choiceWire selects caseIndex.val).map
          BoolFormula.size)[index]?).getD 0)) =
      effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) := by
  funext index
  by_cases hindex : index < (transitionCases tm).length
  · rw [List.getElem?_eq_getElem (by simp [hindex])]
    simp only [List.getElem_map, List.getElem_ofFn, Option.getD_some]
    exact size_effectFormulaAt tm T configBase choiceWire selects index hindex
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [effectFormulaSizeAt, hindex]

theorem compileRaw_effectFormula_eq_schedule_internal
    (tm : NTM k) (T configBase choiceWire available : ℕ)
    (selects : TransitionEffect tm → Bool) :
    BoolFormula.compileRaw available
        (effectFormula tm T configBase choiceWire selects) =
      effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase choiceWire available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm) := by
  let formulaAt := effectFormulaAt tm T configBase choiceWire selects
  let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
    (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
  let blockAt := effectFormulaCaseBlock (transitionCases tm).length
    (Fintype.card tm.Q) k T configBase choiceWire available
    (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
    (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
  unfold effectFormula
  rw [compileRaw_disjs_eq_indexed]
  rw [effectFormulaList_eq_indexed]
  have hmembers := compileRawOutputs_eq_indexedGateBlocks
    (transitionCases tm).length available formulaAt blockAt sizeAt
    (by
      intro caseIndex hcase
      exact size_effectFormulaAt tm T configBase choiceWire selects caseIndex
        hcase)
    (by
      intro caseIndex hcase
      exact compileRaw_effectFormulaAt tm T configBase choiceWire available
        selects caseIndex hcase)
  have hsizes := effectFormulaSizeLookup_eq tm T configBase choiceWire selects
  unfold effectFormulaSchedule effectFormulaCaseGates
  rw [hmembers, hsizes]
  simp only [List.length_ofFn]
  simp only [blockAt]

end Serializer

end CircuitUnrolling

end Complexity
