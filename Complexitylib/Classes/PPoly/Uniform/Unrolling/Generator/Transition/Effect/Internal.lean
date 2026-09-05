/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect.Defs

/-!
# Direct-unrolling transition-effect generator -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Scratch invariant while a rolling effect-member output reference moves
backward through the variable-width case stream. -/
structure EffectConnectorClean
    (values : BinaryValues WorkCount) : Prop where
  reference₁ : values Work.reference₁ = 0
  loop₃ : values Work.loop₃ = 0
  temporary₂ : values Work.temporary₂ = 0
  temporary₃ : values Work.temporary₃ = 0
  emitCounter : values Work.emitCounter = 0
  copyCounter : values Work.copyCounter = 0
  multiplyCounter : values Work.multiplyCounter = 0
  addCounter : values Work.addCounter = 0

private theorem CaseFormulaClean.updateAvailable
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (available : ℕ) :
    CaseFormulaClean (Function.update values Work.available available) := by
  refine
    { toReadFormulaClean :=
        { position := ?_
          loop₀ := ?_
          limit₀ := ?_
          reference₀ := ?_
          reference₁ := ?_
          emitCounter := ?_
          copyCounter := ?_
          multiplyCounter := ?_
          addCounter := ?_
          temporary₀ := ?_
          temporary₁ := ?_
          temporary₂ := ?_ }
      loop₃ := ?_
      temporary₃ := ?_
      polynomialScratch := ?_
      tapeIndex := ?_
      symbolIndex := ?_ }
  all_goals
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide)]
  · exact hclean.position
  · exact hclean.loop₀
  · exact hclean.limit₀
  · exact hclean.reference₀
  · exact hclean.reference₁
  · exact hclean.emitCounter
  · exact hclean.copyCounter
  · exact hclean.multiplyCounter
  · exact hclean.addCounter
  · exact hclean.temporary₀
  · exact hclean.temporary₁
  · exact hclean.temporary₂
  · exact hclean.loop₃
  · exact hclean.temporary₃
  · exact hclean.polynomialScratch
  · exact hclean.tapeIndex
  · exact hclean.symbolIndex

private theorem CaseFormulaClean.effectConnectorClean
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    EffectConnectorClean values :=
  { reference₁ := hclean.reference₁
    loop₃ := hclean.loop₃
    temporary₂ := hclean.temporary₂
    temporary₃ := hclean.temporary₃
    emitCounter := hclean.emitCounter
    copyCounter := hclean.copyCounter
    multiplyCounter := hclean.multiplyCounter
    addCounter := hclean.addCounter }

private theorem EffectConnectorClean.updateReference₀
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (reference : ℕ) :
    EffectConnectorClean
      (Function.update values Work.reference₀ reference) := by
  refine
    { reference₁ := ?_
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.reference₀, Work.reference₁] using hclean.reference₁
  · simpa [Work.reference₀, Work.loop₃] using hclean.loop₃
  · simpa [Work.reference₀, Work.temporary₂] using hclean.temporary₂
  · simpa [Work.reference₀, Work.temporary₃] using hclean.temporary₃
  · simpa [Work.reference₀, Work.emitCounter] using hclean.emitCounter
  · simpa [Work.reference₀, Work.copyCounter] using hclean.copyCounter
  · simpa [Work.reference₀, Work.multiplyCounter] using
      hclean.multiplyCounter
  · simpa [Work.reference₀, Work.addCounter] using hclean.addCounter

private theorem EffectConnectorClean.afterReadConnector
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values) :
    EffectConnectorClean (emitReadConnector.effect values) := by
  rw [emitReadConnector_effect_internal]
  refine
    { reference₁ := by simp
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.available, Work.reference₁, Work.loop₃] using
      hclean.loop₃
  · simpa [Work.available, Work.reference₁, Work.temporary₂] using
      hclean.temporary₂
  · simpa [Work.available, Work.reference₁, Work.temporary₃] using
      hclean.temporary₃
  · simpa [Work.available, Work.reference₁, Work.emitCounter] using
      hclean.emitCounter
  · simpa [Work.available, Work.reference₁, Work.copyCounter] using
      hclean.copyCounter
  · simpa [Work.available, Work.reference₁, Work.multiplyCounter] using
      hclean.multiplyCounter
  · simpa [Work.available, Work.reference₁, Work.addCounter] using
      hclean.addCounter

private theorem emitReadConnector_sound_for_effect :
    emitReadConnector.Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember
  · subst member
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst member
    exact BinaryRoutine.emitRawGateStep_sound .or false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst member
    exact BinaryRoutine.clear_sound Work.reference₁

theorem emitEffectCaseAt_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ) :
    (emitEffectCaseAt tm selects caseIndex).Sound := by
  rw [emitEffectCaseAt]
  split
  · exact emitCaseFormula_sound_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex)
  · exact emitConstantGate_sound_internal false

theorem emitEffectCaseAt_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectCaseAt tm selects caseIndex).requires values := by
  rw [emitEffectCaseAt]
  split
  · exact emitCaseFormula_requires_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean
  · exact emitConstantGate_requires_internal false values
      hclean.emitCounter

@[simp] theorem emitEffectCaseAt_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectCaseAt tm selects caseIndex).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaCaseSize k (values Work.horizon)
            (effectCaseSelectedAt tm selects caseIndex)
            (effectCaseChoiceAt tm caseIndex)) := by
  rw [emitEffectCaseAt]
  by_cases hselected : effectCaseSelectedAt tm selects caseIndex
  · rw [ite_eq_left hselected]
    rw [emitCaseFormula_effect_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean]
    simp [effectFormulaCaseSize, hselected]
  · rw [ite_eq_right hselected, emitConstantGate_effect_internal]
    simp [effectFormulaCaseSize, hselected]

theorem emitEffectCaseAt_emitted_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (caseIndex available : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : values Work.available =
      effectFormulaCaseAvailable (transitionCases tm).length k
        (values Work.horizon) available (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) caseIndex) :
    (emitEffectCaseAt tm selects caseIndex).emitted values =
      (effectFormulaCaseBlock (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀) available
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
        caseIndex).flatMap CircuitCode.RawGate.encode := by
  rw [emitEffectCaseAt]
  by_cases hselected : effectCaseSelectedAt tm selects caseIndex
  · rw [ite_eq_left hselected]
    rw [emitCaseFormula_emitted_internal (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex) values hclean]
    simp [effectFormulaCaseBlock, hselected, havailable]
  · rw [ite_eq_right hselected,
      emitConstantGate_emitted_internal false values hclean.reference₀]
    simp [effectFormulaCaseBlock, hselected, directInitConstant]

private theorem emitEffectMembersFrom_sound (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (start count : ℕ) :
    (emitEffectMembersFrom tm selects start count).Sound := by
  induction count generalizing start with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitEffectCaseAt_sound_internal tm selects start).seq
        (ih (start + 1))

theorem emitEffectMembers_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectMembers tm selects).Sound :=
  emitEffectMembersFrom_sound tm selects 0 (transitionCases tm).length

private theorem emitEffectMembersFrom_requires (tm : NTM k)
    (selects : TransitionEffect tm → Bool) (start count : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembersFrom tm selects start count).requires values := by
  induction count generalizing start values with
  | zero =>
      simp [emitEffectMembersFrom, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      refine ⟨emitEffectCaseAt_requires_internal tm selects start values
        hclean, ?_⟩
      rw [emitEffectCaseAt_effect_internal tm selects start values hclean]
      exact ih (start + 1) _
        (CaseFormulaClean.updateAvailable values hclean _)

theorem emitEffectMembers_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).requires values :=
  emitEffectMembersFrom_requires tm selects 0 (transitionCases tm).length
    values hclean

private theorem emitEffectMembersFrom_effect
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (start count base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values)
    (hbound : start + count ≤ (transitionCases tm).length)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)) start) :
    (emitEffectMembersFrom tm selects start count).effect values =
      Function.update values Work.available
        (base + prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k T
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (start + count)) := by
  induction count generalizing start values with
  | zero =>
      rw [emitEffectMembersFrom]
      change values = _
      funext i
      by_cases havailableIndex : i = Work.available
      · subst i
        simpa using havailable
      · simp [havailableIndex]
  | succ count ih =>
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : start < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt start =
          effectFormulaCaseSize k T
            (effectCaseSelectedAt tm selects start)
            (effectCaseChoiceAt tm start) := by
        simp [sizeAt, effectFormulaSizeAt, hindex]
      let current := (emitEffectCaseAt tm selects start).effect values
      have hcurrent := emitEffectCaseAt_effect_internal tm selects start values
        hclean
      have hcurrentClean : CaseFormulaClean current := by
        dsimp [current]
        rw [hcurrent]
        exact CaseFormulaClean.updateAvailable values hclean _
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.horizon] using hhorizon
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (start + 1) := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.available]
        rw [ite_eq_left True.intro]
        change values Work.available + _ = _
        rw [havailable, hhorizon, ← hsizeAt]
        simp [prefixSize]
        dsimp [sizeAt]
        omega
      have htail := ih (start + 1) current hcurrentClean (by omega)
        hcurrentHorizon hcurrentAvailable
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      change
        (emitEffectMembersFrom tm selects (start + 1) count).effect current = _
      rw [htail]
      dsimp [current]
      rw [hcurrent]
      funext i
      simp only [Function.update_apply]
      split_ifs
      · congr 2
        all_goals omega
      · rfl

@[simp] theorem emitEffectMembers_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).effect values =
      Function.update values Work.available
        (values Work.available + prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) (transitionCases tm).length) := by
  simpa [emitEffectMembers, prefixSize] using
    emitEffectMembersFrom_effect tm selects 0 (transitionCases tm).length
      (values Work.available) (values Work.horizon) values hclean (by omega)
      rfl (by simp [prefixSize])

private theorem emitEffectMembersFrom_emitted
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (start count base T configBase choiceWire : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hbound : start + count ≤ (transitionCases tm).length)
    (hhorizon : values Work.horizon = T)
    (hconfigBase : values Work.configBase = configBase)
    (hchoiceWire : values Work.reference₀ = choiceWire)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)) start) :
    (emitEffectMembersFrom tm selects start count).emitted values =
      (indexedGateBlocks count fun offset =>
        effectFormulaCaseBlock (transitionCases tm).length
          (Fintype.card tm.Q) k T configBase choiceWire base
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
          (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
          (start + offset)).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing start values with
  | zero =>
      simp [emitEffectMembersFrom, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : start < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt start =
          effectFormulaCaseSize k T
            (effectCaseSelectedAt tm selects start)
            (effectCaseChoiceAt tm start) := by
        simp [sizeAt, effectFormulaSizeAt, hindex]
      have hcaseAvailable : values Work.available =
          effectFormulaCaseAvailable (transitionCases tm).length k
            (values Work.horizon) base (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) start := by
        rw [hhorizon]
        simpa [effectFormulaCaseAvailable, sizeAt] using havailable
      let current := (emitEffectCaseAt tm selects start).effect values
      have hcurrent := emitEffectCaseAt_effect_internal tm selects start values
        hclean
      have hcurrentClean : CaseFormulaClean current := by
        dsimp [current]
        rw [hcurrent]
        exact CaseFormulaClean.updateAvailable values hclean _
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.horizon] using hhorizon
      have hcurrentConfigBase : current Work.configBase = configBase := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.configBase] using hconfigBase
      have hcurrentChoiceWire : current Work.reference₀ = choiceWire := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.available, Work.reference₀] using hchoiceWire
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (start + 1) := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.available]
        rw [ite_eq_left True.intro]
        change values Work.available + _ = _
        rw [havailable, hhorizon, ← hsizeAt]
        simp [prefixSize]
        dsimp [sizeAt]
        omega
      have htail := ih (start + 1) current hcurrentClean (by omega)
        hcurrentHorizon hcurrentConfigBase hcurrentChoiceWire (by
          simpa [sizeAt] using hcurrentAvailable)
      rw [emitEffectMembersFrom, BinaryRoutine.seq]
      change (emitEffectCaseAt tm selects start).emitted values ++
        (emitEffectMembersFrom tm selects (start + 1) count).emitted current = _
      rw [emitEffectCaseAt_emitted_internal tm selects start base values
        hclean hcaseAvailable, htail]
      rw [hhorizon, hconfigBase, hchoiceWire]
      simp only [indexedGateBlocks, List.flatMap_append, Nat.add_zero]
      congr 1
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply congrArg (indexedGateBlocks count)
      funext offset
      exact congrArg
        (effectFormulaCaseBlock (transitionCases tm).length
          (Fintype.card tm.Q) k T configBase choiceWire base
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
          (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm))
        (by omega)

@[simp] theorem emitEffectMembers_emitted_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitEffectMembers tm selects).emitted values =
      (effectFormulaCaseGates (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  simpa [emitEffectMembers, effectFormulaCaseGates, prefixSize] using
    emitEffectMembersFrom_emitted tm selects 0 (transitionCases tm).length
      (values Work.available) (values Work.horizon) (values Work.configBase)
      (values Work.reference₀) values hclean (by omega) rfl rfl rfl
      (by simp [prefixSize])

theorem prepareEffectCaseSize_sound_internal (workCount : ℕ)
    (selected choiceValue : Bool) :
    (prepareEffectCaseSize workCount selected choiceValue).Sound := by
  cases selected <;> simp only [prepareEffectCaseSize]
  · exact BinaryRoutine.set_sound Work.temporary₃ 1
  · apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₃
        (6 * workCount + 16 + caseChoiceLiteralSize choiceValue)
    · subst member
      exact BinaryRoutine.set_sound Work.temporary₂ (4 * (workCount + 2))
    · subst member
      exact BinaryRoutine.mulAdd_sound Work.horizon Work.temporary₂
        Work.temporary₃ Work.multiplyCounter Work.addCounter
    · subst member
      exact BinaryRoutine.clear_sound Work.temporary₂

theorem prepareEffectCaseSize_requires_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hmultiply : values Work.multiplyCounter = 0)
    (hadd : values Work.addCounter = 0) :
    (prepareEffectCaseSize workCount selected choiceValue).requires values := by
  cases selected
  · simp [prepareEffectCaseSize, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst]
  · simp only [prepareEffectCaseSize, BinaryRoutine.seqList,
      BinaryRoutine.seq, BinaryRoutine.set, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.mulAdd, BinaryRoutine.identity,
      BinaryRoutine.emitBits, true_and]
    refine ⟨?_, True.intro⟩
    refine ⟨by constructor <;> decide, ?_, ?_⟩
    · simpa [Work.temporary₂, Work.temporary₃,
        Work.multiplyCounter] using hmultiply
    · simpa [Work.temporary₂, Work.temporary₃,
        Work.addCounter] using hadd

@[simp] theorem prepareEffectCaseSize_effect_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (htemporary₂ : values Work.temporary₂ = 0) :
    (prepareEffectCaseSize workCount selected choiceValue).effect values =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue))
        Work.temporary₂ 0 := by
  cases selected
  · simp only [prepareEffectCaseSize, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
      effectFormulaCaseSize]
    funext i
    by_cases htemporary₃Index : i = Work.temporary₃
    · subst i
      simp [Work.temporary₂, Work.temporary₃]
    by_cases htemporary₂Index : i = Work.temporary₂
    · subst i
      simpa [Work.temporary₂, Work.temporary₃] using htemporary₂
    · simp [htemporary₃Index, htemporary₂Index]
  · have hsize :
        6 * workCount + 16 + caseChoiceLiteralSize choiceValue +
            values Work.horizon * (4 * (workCount + 2)) =
          effectFormulaCaseSize workCount (values Work.horizon) true
            choiceValue := by
      cases choiceValue <;>
        simp [effectFormulaCaseSize, caseFormulaScheduleSize,
          caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize,
          caseChoiceLiteralSize] <;>
        ring
    simp only [prepareEffectCaseSize, BinaryRoutine.seqList,
      BinaryRoutine.seq, BinaryRoutine.set, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.mulAdd, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
    funext i
    by_cases htemporary₃Index : i = Work.temporary₃
    · subst i
      simpa [Work.horizon, Work.temporary₂, Work.temporary₃] using hsize
    by_cases htemporary₂Index : i = Work.temporary₂
    · subst i
      simp [Work.temporary₂, Work.temporary₃]
    · simp [htemporary₃Index, htemporary₂Index]

@[simp] theorem prepareEffectCaseSize_emitted_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount) :
    (prepareEffectCaseSize workCount selected choiceValue).emitted values = [] := by
  cases selected <;>
    simp [prepareEffectCaseSize, BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
      BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits]

theorem emitPreviousEffectConnector_sound_internal (workCount : ℕ)
    (selected choiceValue : Bool) :
    (emitPreviousEffectConnector workCount selected choiceValue).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember
  · subst member
    exact prepareEffectCaseSize_sound_internal workCount selected choiceValue
  · subst member
    exact decrementReferenceBy_sound Work.reference₀ Work.temporary₃
      Work.loop₃
  · subst member
    exact emitReadConnector_sound_for_effect
  · subst member
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitPreviousEffectConnector_requires_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values)
    (hsize : effectFormulaCaseSize workCount (values Work.horizon) selected
      choiceValue ≤ values Work.reference₀)
    (havailable : 1 ≤ values Work.available) :
    (emitPreviousEffectConnector workCount selected choiceValue).requires
      values := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hprepare :
      (prepareEffectCaseSize workCount selected choiceValue).requires values :=
    prepareEffectCaseSize_requires_internal workCount selected choiceValue
      values hclean.multiplyCounter hclean.addCounter
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  have hsizeValue : afterSize Work.temporary₃ ≤
      afterSize Work.reference₀ := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.reference₀] using
      hsize
  have hdecrement :
      (decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).requires afterSize := by
    rw [decrementReferenceBy_requires]
    exact ⟨⟨by decide, by decide, by decide⟩, hloopSize, hsizeValue⟩
  let afterDecrement :=
    (decrementReferenceBy Work.reference₀ Work.temporary₃
      Work.loop₃).effect afterSize
  have hafterDecrement : afterDecrement =
      Function.update
        (Function.update afterSize Work.reference₀
          (afterSize Work.reference₀ - afterSize Work.temporary₃))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize
  have hconnector : emitReadConnector.requires afterDecrement := by
    apply emitReadConnector_requires_internal
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.copyCounter] using hclean.copyCounter
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.available] using havailable
    · rw [hafterDecrement, hafterSize]
      simpa [Work.reference₀, Work.temporary₃, Work.temporary₂,
        Work.loop₃, Work.emitCounter] using hclean.emitCounter
  simp only [emitPreviousEffectConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨hprepare, hdecrement, hconnector, trivial, trivial⟩

@[simp] theorem emitPreviousEffectConnector_effect_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values) :
    (emitPreviousEffectConnector workCount selected choiceValue).effect
        values =
      Function.update
        (Function.update values Work.reference₀
          (values Work.reference₀ -
            effectFormulaCaseSize workCount (values Work.horizon) selected
              choiceValue))
        Work.available (values Work.available + 1) := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  let afterDecrement :=
    (decrementReferenceBy Work.reference₀ Work.temporary₃
      Work.loop₃).effect afterSize
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  have hafterDecrement : afterDecrement =
      Function.update
        (Function.update afterSize Work.reference₀
          (afterSize Work.reference₀ - afterSize Work.temporary₃))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize
  rw [emitPreviousEffectConnector]
  change (BinaryRoutine.clear Work.temporary₃).effect
      (emitReadConnector.effect afterDecrement) = _
  rw [emitReadConnector_effect_internal, hafterDecrement, hafterSize]
  simp only [BinaryRoutine.clear]
  have htemporary₂ : values (24 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htemporary₃ : values (25 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  have hreference₁ : values (8 : Fin WorkCount) = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.reference₀, Work.reference₁, Work.temporary₂,
      Work.temporary₃, Work.loop₃, Work.available]

@[simp] theorem emitPreviousEffectConnector_emitted_internal (workCount : ℕ)
    (selected choiceValue : Bool) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values) :
    (emitPreviousEffectConnector workCount selected choiceValue).emitted
        values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.reference₀ -
            effectFormulaCaseSize workCount (values Work.horizon) selected
              choiceValue
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  let afterSize :=
    (prepareEffectCaseSize workCount selected choiceValue).effect values
  have hafterSize : afterSize =
      Function.update
        (Function.update values Work.temporary₃
          (effectFormulaCaseSize workCount (values Work.horizon) selected
            choiceValue)) Work.temporary₂ 0 :=
    prepareEffectCaseSize_effect_internal workCount selected choiceValue values
      hclean.temporary₂
  have hloopSize : afterSize Work.loop₃ = 0 := by
    rw [hafterSize]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      hclean.loop₃
  simp only [emitPreviousEffectConnector, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [prepareEffectCaseSize_emitted_internal, decrementReferenceBy_emitted,
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ afterSize ⟨by decide, by decide, by decide⟩ hloopSize,
    emitReadConnector_emitted_internal, hafterSize]
  simp [BinaryRoutine.clear, Work.reference₀, Work.temporary₃,
    Work.temporary₂, Work.loop₃, Work.available]

private theorem EffectConnectorClean.afterPrevious
    (workCount : ℕ) (selected choiceValue : Bool)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values) :
    EffectConnectorClean
      ((emitPreviousEffectConnector workCount selected choiceValue).effect
        values) := by
  rw [emitPreviousEffectConnector_effect_internal workCount selected
    choiceValue values hclean]
  refine
    { reference₁ := ?_
      loop₃ := ?_
      temporary₂ := ?_
      temporary₃ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_ }
  · simpa [Work.reference₀, Work.reference₁, Work.available] using
      hclean.reference₁
  · simpa [Work.reference₀, Work.loop₃, Work.available] using
      hclean.loop₃
  · simpa [Work.reference₀, Work.temporary₂, Work.available] using
      hclean.temporary₂
  · simpa [Work.reference₀, Work.temporary₃, Work.available] using
      hclean.temporary₃
  · simpa [Work.reference₀, Work.emitCounter, Work.available] using
      hclean.emitCounter
  · simpa [Work.reference₀, Work.copyCounter, Work.available] using
      hclean.copyCounter
  · simpa [Work.reference₀, Work.multiplyCounter, Work.available] using
      hclean.multiplyCounter
  · simpa [Work.reference₀, Work.addCounter, Work.available] using
      hclean.addCounter

private theorem effectFormulaCaseSize_pos (workCount T : ℕ)
    (selected choiceValue : Bool) :
    1 ≤ effectFormulaCaseSize workCount T selected choiceValue := by
  cases selected
  · simp [effectFormulaCaseSize]
  · simp [effectFormulaCaseSize, caseFormulaScheduleSize,
      caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize]
    omega

private theorem emitPreviousEffectConnectorsCount_requires
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count base : ℕ)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (hcount : count + 1 ≤ (transitionCases tm).length) (hbase : 1 ≤ base)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (count + 1) - 1)
    (havailable : 1 ≤ values Work.available) :
    (emitPreviousEffectConnectorsCount tm selects count).requires values := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousEffectConnectorsCount, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
        (values Work.horizon) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k (values Work.horizon) selected
            choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      have hsize : effectFormulaCaseSize k (values Work.horizon) selected
          choiceValue ≤ values Work.reference₀ := by
        rw [hreference]
        change _ ≤ base + prefixSize sizeAt (count + 2) - 1
        rw [hprefix, ← hsizeAt]
        omega
      have hhead := emitPreviousEffectConnector_requires_internal k selected
        choiceValue values hclean hsize havailable
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hhorizon : current Work.horizon = values Work.horizon := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available, Work.horizon]
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_right (by decide), ite_eq_left True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have hcurrentAvailable : 1 ≤ current Work.available := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available]
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      refine ⟨hhead, ih current hcurrentClean (by omega) ?_
        hcurrentAvailable⟩
      rw [hhorizon]
      exact hcurrentReference

private theorem emitPreviousEffectConnectorsCount_effect
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count base : ℕ)
    (values : BinaryValues WorkCount) (hclean : EffectConnectorClean values)
    (hcount : count + 1 ≤ (transitionCases tm).length) (hbase : 1 ≤ base)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (count + 1) - 1) :
    (emitPreviousEffectConnectorsCount tm selects count).effect values =
      Function.update
        (Function.update values Work.reference₀
          (base + effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) 0 - 1))
        Work.available (values Work.available + count) := by
  induction count generalizing values with
  | zero =>
      have hreferenceZero : values Work.reference₀ =
          base + effectFormulaSizeAt (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm) 0 - 1 := by
        simpa [prefixSize] using hreference
      rw [emitPreviousEffectConnectorsCount]
      change values = _
      funext i
      by_cases havailableIndex : i = Work.available
      · subst i
        simp [Work.reference₀, Work.available]
      by_cases hreferenceIndex : i = Work.reference₀
      · subst i
        simpa [Work.reference₀, Work.available] using hreferenceZero
      · simp [havailableIndex, hreferenceIndex]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
        (values Work.horizon) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k (values Work.horizon) selected
            choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hhorizon : current Work.horizon = values Work.horizon := by
        dsimp [current]
        rw [hcurrent]
        simp [Work.reference₀, Work.available, Work.horizon]
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_right (by decide), ite_eq_left True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have htail := ih current hcurrentClean (by omega) (by
        rw [hhorizon]
        exact hcurrentReference)
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      change
        (emitPreviousEffectConnectorsCount tm selects count).effect current = _
      rw [htail]
      rw [hhorizon]
      dsimp [current]
      rw [hcurrent]
      funext i
      simp only [Function.update_apply]
      split_ifs <;>
        simp_all [Work.reference₀, Work.available, Work.horizon]
      all_goals omega

private theorem emitPreviousEffectConnectorsCount_emitted
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (count nextRank base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : EffectConnectorClean values)
    (hranks : nextRank + count = (transitionCases tm).length)
    (hnextRank : 1 ≤ nextRank) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + nextRank + 1)
    (hreference : values Work.reference₀ =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (count + 1) - 1) :
    (emitPreviousEffectConnectorsCount tm selects count).emitted values =
      ((List.range count).map fun offset =>
        indexedRightFoldConnector .or base (transitionCases tm).length
          (effectFormulaSizeAt (transitionCases tm).length k T
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (nextRank + offset)).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing nextRank values with
  | zero =>
      simp [emitPreviousEffectConnectorsCount, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hsizeAt : sizeAt (count + 1) =
          effectFormulaCaseSize k T selected choiceValue := by
        simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
      have hprefix : prefixSize sizeAt (count + 2) =
          prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
        simp [prefixSize]
      let current :=
        (emitPreviousEffectConnector k selected choiceValue).effect values
      have hcurrent := emitPreviousEffectConnector_effect_internal k selected
        choiceValue values hclean
      have hcurrentClean := hclean.afterPrevious k selected choiceValue values
      have hcurrentHorizon : current Work.horizon = T := by
        dsimp [current]
        rw [hcurrent]
        simpa [Work.reference₀, Work.available, Work.horizon] using hhorizon
      have hcurrentAvailable : current Work.available =
          base + prefixSize sizeAt (transitionCases tm).length +
            (nextRank + 1) + 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_left True.intro]
        change values Work.available + 1 = _
        rw [havailable]
        dsimp [sizeAt]
        omega
      have hcurrentReference : current Work.reference₀ =
          base + prefixSize sizeAt (count + 1) - 1 := by
        dsimp [current]
        rw [hcurrent]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_right (by decide), ite_eq_left True.intro]
        change values Work.reference₀ - _ = _
        rw [hreference, hhorizon]
        change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
        rw [hprefix, ← hsizeAt]
        omega
      have htail := ih (nextRank + 1) current hcurrentClean (by omega)
        (by omega) hcurrentHorizon hcurrentAvailable hcurrentReference
      rw [emitPreviousEffectConnectorsCount, BinaryRoutine.seq]
      change
        (emitPreviousEffectConnector k selected choiceValue).emitted values ++
          (emitPreviousEffectConnectorsCount tm selects count).emitted current =
            _
      rw [emitPreviousEffectConnector_emitted_internal k selected choiceValue
        values hclean, htail]
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
        List.flatMap_cons]
      have hgate :
          { op := AndOrOp.or
            input₀ := values Work.reference₀ -
              effectFormulaCaseSize k (values Work.horizon) selected
                choiceValue
            input₁ := values Work.available - 1
            negated₀ := false
            negated₁ := false } =
          indexedRightFoldConnector .or base (transitionCases tm).length
            sizeAt nextRank := by
        have hmember :
            (transitionCases tm).length - nextRank - 1 = count := by
          omega
        have hinput₀ : values Work.reference₀ -
              effectFormulaCaseSize k (values Work.horizon) selected
                choiceValue =
            base + prefixSize sizeAt (count + 1) - 1 := by
          rw [hhorizon, hreference]
          change (base + prefixSize sizeAt (count + 2) - 1) - _ = _
          rw [← hsizeAt, hprefix]
          omega
        have hinput₁ : values Work.available - 1 =
            base + prefixSize sizeAt (transitionCases tm).length +
              nextRank := by
          rw [havailable]
          dsimp [sizeAt]
        rw [hinput₀, hinput₁]
        unfold indexedRightFoldConnector reverseMember
        dsimp only
        rw [hmember]
      rw [hgate]
      congr 1
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply List.map_congr_left
      intro offset hoffset
      exact congrArg
        (indexedRightFoldConnector .or base (transitionCases tm).length
          sizeAt) (by omega)

private theorem emitPreviousEffectConnectorsCount_sound
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count : ℕ) :
    (emitPreviousEffectConnectorsCount tm selects count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact
        (emitPreviousEffectConnector_sound_internal k
          (effectCaseSelectedAt tm selects (count + 1))
          (effectCaseChoiceAt tm (count + 1))).seq ih

theorem emitPreviousEffectConnectors_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitPreviousEffectConnectors tm selects).Sound :=
  emitPreviousEffectConnectorsCount_sound tm selects
    ((transitionCases tm).length - 1)

theorem emitEffectConnectors_requires_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).requires values := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · simp [BinaryRoutine.identity, BinaryRoutine.emitBits]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    have hlastIndex : (transitionCases tm).length - 1 <
        (transitionCases tm).length := by omega
    have hlastSize : 1 ≤ sizeAt ((transitionCases tm).length - 1) := by
      rw [show sizeAt ((transitionCases tm).length - 1) =
        effectFormulaCaseSize k T
          (effectCaseSelectedAt tm selects
            ((transitionCases tm).length - 1))
          (effectCaseChoiceAt tm ((transitionCases tm).length - 1)) by
          simp [sizeAt, effectFormulaSizeAt, hlastIndex]]
      exact effectFormulaCaseSize_pos k T _ _
    have hprefixPos : 1 ≤
        prefixSize sizeAt (transitionCases tm).length := by
      obtain ⟨caseCount, hcaseCount⟩ := Nat.exists_eq_succ_of_ne_zero hlength
      rw [hcaseCount, prefixSize_succ]
      have hlastSize' : 1 ≤ sizeAt caseCount := by
        simpa [hcaseCount] using hlastSize
      omega
    have havailableTwo : 2 ≤ values Work.available := by
      rw [havailable]
      change 2 ≤ base + prefixSize sizeAt (transitionCases tm).length + 1
      omega
    have hprepare := (prepareRecentReference_requires Work.reference₀ 2
      values (by decide) (by decide) (by decide)).2
        ⟨hclean.copyCounter, havailableTwo⟩
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    have hinitial : emitReadConnector.requires prepared := by
      apply emitReadConnector_requires_internal
      · rw [hprepared]
        simpa [Work.reference₀, Work.copyCounter] using hclean.copyCounter
      · rw [hprepared]
        simpa [Work.reference₀, Work.available] using
          show 1 ≤ values Work.available by omega
      · rw [hprepared]
        simpa [Work.reference₀, Work.emitCounter] using hclean.emitCounter
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hcurrentAvailable : 1 ≤ current Work.available := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp [Work.reference₀, Work.available, Work.reference₁]
    have hprevious :
        (emitPreviousEffectConnectors tm selects).requires current := by
      rw [emitPreviousEffectConnectors]
      apply emitPreviousEffectConnectorsCount_requires tm selects
        ((transitionCases tm).length - 1) base current hcurrentClean
        (by omega) hbase
      · rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega, hcurrentHorizon]
        simpa [sizeAt] using hcurrentReference
      · exact hcurrentAvailable
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    exact ⟨hprepare, hinitial, hprevious, trivial, trivial⟩

theorem emitEffectConnectors_effect_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).effect values =
      Function.update values Work.available
        (values Work.available + (transitionCases tm).length) := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · have hlength : (transitionCases tm).length = 0 :=
      List.isEmpty_iff_length_eq_zero.mp hempty
    simp [BinaryRoutine.identity, BinaryRoutine.emitBits, hlength]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hprevious := emitPreviousEffectConnectorsCount_effect tm selects
      ((transitionCases tm).length - 1) base current hcurrentClean
      (by omega) hbase (by
        rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega, hcurrentHorizon]
        simpa [sizeAt] using hcurrentReference)
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits]
    change (BinaryRoutine.clear Work.reference₀).effect
      ((emitPreviousEffectConnectors tm selects).effect current) = _
    rw [emitPreviousEffectConnectors, hprevious]
    dsimp [current]
    rw [emitReadConnector_effect_internal, hprepared]
    simp only [BinaryRoutine.clear]
    have hreference₀ : values (7 : Fin WorkCount) = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    have hreference₁ : values (8 : Fin WorkCount) = 0 := by
      simpa [Work.reference₁] using hclean.reference₁
    funext i
    simp only [Function.update_apply]
    split_ifs <;>
      simp_all [Work.reference₀, Work.reference₁, Work.available,
        sizeAt]
    all_goals omega

theorem emitEffectConnectors_emitted_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (base T : ℕ) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) (hbase : 1 ≤ base)
    (hhorizon : values Work.horizon = T)
    (havailable : values Work.available =
      base + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
        (transitionCases tm).length + 1) :
    (emitEffectConnectors tm selects).emitted values =
      (indexedRightFoldConnectors .or base (transitionCases tm).length
        (effectFormulaSizeAt (transitionCases tm).length k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))).flatMap
        CircuitCode.RawGate.encode := by
  rw [emitEffectConnectors]
  split_ifs with hempty
  · have hlength : (transitionCases tm).length = 0 :=
      List.isEmpty_iff_length_eq_zero.mp hempty
    simp [BinaryRoutine.identity, BinaryRoutine.emitBits,
      indexedRightFoldConnectors, hlength]
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPos : 0 < (transitionCases tm).length := by omega
    let sizeAt := effectFormulaSizeAt (transitionCases tm).length k T
      (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
    let prepared :=
      (prepareRecentReference Work.reference₀ 2).effect values
    have hprepared : prepared = Function.update values Work.reference₀
        (values Work.available - 2) :=
      prepareRecentReference_effect Work.reference₀ 2 values
    have hpreparedClean : EffectConnectorClean prepared := by
      rw [hprepared]
      exact EffectConnectorClean.updateReference₀ values
        hclean.effectConnectorClean _
    let current := emitReadConnector.effect prepared
    have hcurrentClean : EffectConnectorClean current :=
      hpreparedClean.afterReadConnector prepared
    have hcurrentHorizon : current Work.horizon = T := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simpa [Work.reference₀, Work.available, Work.reference₁,
        Work.horizon] using hhorizon
    have hcurrentAvailable : current Work.available =
        base + prefixSize sizeAt (transitionCases tm).length + 1 + 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available]
      rw [ite_eq_left True.intro]
      change values Work.available + 1 = _
      rw [havailable]
    have hcurrentReference : current Work.reference₀ =
        base + prefixSize sizeAt (transitionCases tm).length - 1 := by
      dsimp [current]
      rw [emitReadConnector_effect_internal, hprepared]
      simp only [Function.update_apply, Work.available, Work.reference₀,
        Work.reference₁]
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left True.intro]
      change values Work.available - 2 = _
      rw [havailable]
      dsimp [sizeAt]
      omega
    have hprevious := emitPreviousEffectConnectorsCount_emitted tm selects
      ((transitionCases tm).length - 1) 1 base T current hcurrentClean
      (by omega) (by omega) hbase hcurrentHorizon hcurrentAvailable (by
        rw [show (transitionCases tm).length - 1 + 1 =
          (transitionCases tm).length by omega]
        simpa [sizeAt] using hcurrentReference)
    have hinitialGate :
        ({ op := AndOrOp.or
           input₀ := prepared Work.reference₀
           input₁ := prepared Work.available - 1
           negated₀ := false
           negated₁ := false } : CircuitCode.RawGate) =
          indexedRightFoldConnector .or base (transitionCases tm).length
            sizeAt 0 := by
      have hmember : (transitionCases tm).length - 0 - 1 + 1 =
          (transitionCases tm).length := by omega
      have hinput₀ : prepared Work.reference₀ =
          base + prefixSize sizeAt (transitionCases tm).length - 1 := by
        rw [hprepared]
        simp only [Function.update_apply, Work.reference₀]
        rw [ite_eq_left True.intro]
        rw [havailable]
        dsimp [sizeAt]
        omega
      have hinput₁ : prepared Work.available - 1 =
          base + prefixSize sizeAt (transitionCases tm).length := by
        rw [hprepared]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_right (by decide)]
        change values Work.available - 1 = _
        rw [havailable]
        dsimp [sizeAt]
      rw [hinput₀, hinput₁]
      unfold indexedRightFoldConnector reverseMember
      dsimp only
      rw [hmember]
      simp
    simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits,
      prepareRecentReference_emitted, BinaryRoutine.clear,
      List.nil_append, List.append_nil]
    change emitReadConnector.emitted prepared ++
      (emitPreviousEffectConnectors tm selects).emitted current = _
    rw [emitReadConnector_emitted_internal, emitPreviousEffectConnectors,
      hprevious, hinitialGate]
    unfold indexedRightFoldConnectors
    obtain ⟨caseCount, hcaseCount⟩ := Nat.exists_eq_succ_of_ne_zero hlength
    rw [hcaseCount, Nat.add_one_sub_one, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.flatMap_cons]
    dsimp [sizeAt]
    rw [hcaseCount]
    congr 1
    apply congrArg (List.flatMap CircuitCode.RawGate.encode)
    apply List.map_congr_left
    intro rank _hrank
    exact congrArg
      (indexedRightFoldConnector .or base (caseCount + 1)
        (effectFormulaSizeAt (caseCount + 1) k T
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)))
      (show 1 + rank = Nat.succ rank by omega)

theorem emitEffectConnectors_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectConnectors tm selects).Sound := by
  rw [emitEffectConnectors]
  split_ifs
  · exact BinaryRoutine.identity_sound
  · apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember
    · subst member
      exact prepareRecentReference_sound Work.reference₀ 2
    · subst member
      exact emitReadConnector_sound_for_effect
    · subst member
      exact emitPreviousEffectConnectors_sound_internal tm selects
    · subst member
      exact BinaryRoutine.clear_sound Work.reference₀

theorem emitEffectFormula_sound_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine
  · subst routine
    exact emitEffectMembers_sound_internal tm selects
  · subst routine
    exact emitConstantGate_sound_internal false
  · subst routine
    exact emitEffectConnectors_sound_internal tm selects

theorem emitEffectFormula_requires_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).requires values := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hidentityRequires : (emitConstantGate false).requires afterMembers :=
    emitConstantGate_requires_internal false afterMembers
      hafterMembersClean.emitCounter
  have hconnectorsRequires :
      (emitEffectConnectors tm selects).requires afterIdentity := by
    apply emitEffectConnectors_requires_internal tm selects
      (values Work.available) (values Work.horizon) afterIdentity
      hafterIdentityClean havailable
    · rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]
    · rw [hafterIdentity, hafterMembers]
      simp [Work.available]
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨emitEffectMembers_requires_internal tm selects values hclean,
    hidentityRequires, hconnectorsRequires, trivial⟩

theorem emitEffectFormula_effect_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).effect values =
      Function.update values Work.available
        (values Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (effectCaseSelectedAt tm selects)
            (effectCaseChoiceAt tm)) := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hconnectors := emitEffectConnectors_effect_internal tm selects
    (values Work.available) (values Work.horizon) afterIdentity
    hafterIdentityClean havailable (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]) (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available])
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  change (emitEffectConnectors tm selects).effect afterIdentity = _
  rw [hconnectors, hafterIdentity, hafterMembers]
  funext i
  simp only [effectFormulaScheduleSize, Function.update_apply]
  split_ifs <;> simp_all [Work.available]
  all_goals omega

theorem emitEffectFormula_emitted_internal (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitEffectFormula tm selects).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (effectCaseSelectedAt tm selects)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let afterMembers := (emitEffectMembers tm selects).effect values
  have hafterMembers : afterMembers = Function.update values Work.available
      (values Work.available + prefixSize
        (effectFormulaSizeAt (transitionCases tm).length k
          (values Work.horizon) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)) (transitionCases tm).length) :=
    emitEffectMembers_effect_internal tm selects values hclean
  have hafterMembersClean : CaseFormulaClean afterMembers := by
    rw [hafterMembers]
    exact CaseFormulaClean.updateAvailable values hclean _
  let afterIdentity := (emitConstantGate false).effect afterMembers
  have hafterIdentity : afterIdentity = Function.update afterMembers
      Work.available (afterMembers Work.available + 1) :=
    emitConstantGate_effect_internal false afterMembers
  have hafterIdentityClean : CaseFormulaClean afterIdentity := by
    rw [hafterIdentity]
    exact CaseFormulaClean.updateAvailable afterMembers hafterMembersClean _
  have hidentityReference : afterMembers Work.reference₀ = 0 := by
    rw [hafterMembers]
    simpa [Work.available, Work.reference₀] using hclean.reference₀
  have hconnectors := emitEffectConnectors_emitted_internal tm selects
    (values Work.available) (values Work.horizon) afterIdentity
    hafterIdentityClean havailable (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available, Work.horizon]) (by
      rw [hafterIdentity, hafterMembers]
      simp [Work.available])
  simp only [emitEffectFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitEffectMembers_emitted_internal tm selects values hclean,
    emitConstantGate_emitted_internal false afterMembers hidentityReference,
    hconnectors]
  unfold effectFormulaSchedule
  simp only [directInitConstant, List.flatMap_append,
    List.flatMap_singleton]
  simp [List.append_assoc]

/-! ## Pointwise all-prefix width certificates -/

/-- One global arithmetic envelope for every machine-selected case and every
bounded read selector used by complete effect-formula emission. -/
private def EffectFormulaWidthCap (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (values : ℕ → BinaryValues WorkCount) (width : ℕ → ℕ) : Prop :=
  ∀ inputLength stateIndex tapeIndex symbolIndex position,
    stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
    symbolIndex < 4 → position ≤ values inputLength Work.horizon →
      values inputLength Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values inputLength Work.horizon)
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) +
        transitionStateRef (values inputLength Work.configBase) stateIndex +
        (transitionHeadRef (Fintype.card tm.Q)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position +
            tapeIndex + values inputLength Work.horizon + 1) +
        (transitionCellRef (Fintype.card tm.Q) (k + 2)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position
              symbolIndex +
            (tapeIndex * (values inputLength Work.horizon + 2) + position) +
            (values inputLength Work.horizon + 2) + (k + 2) + tapeIndex +
            4) +
        caseReadSize (values inputLength Work.horizon) +
        values inputLength Work.horizon ≤ width inputLength

private theorem EffectFormulaWidthCap.frontier
    {tm : NTM k} {selects : TransitionEffect tm → Bool}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcap : EffectFormulaWidthCap tm selects values width) :
    ∀ inputLength,
      values inputLength Work.available +
          effectFormulaScheduleSize (transitionCases tm).length k
            (values inputLength Work.horizon)
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) ≤
        width inputLength := by
  intro inputLength
  have hstate : stateIndex tm tm.qstart < Fintype.card tm.Q :=
    (Fintype.equivFin tm.Q tm.qstart).isLt
  have hbound := hcap inputLength (stateIndex tm tm.qstart) 0 0 0
    hstate (by omega) (by omega) (Nat.zero_le _)
  omega

private theorem effectCaseStateIndexAt_lt (tm : NTM k) (caseIndex : ℕ)
    (hcase : caseIndex < (transitionCases tm).length) :
    effectCaseStateIndexAt tm caseIndex < Fintype.card tm.Q := by
  rw [effectCaseStateIndexAt, dite_eq_left hcase]
  exact (Fintype.equivFin tm.Q _).isLt

private theorem effectCaseInputSymbolIndexAt_lt (tm : NTM k)
    (caseIndex : ℕ) (hcase : caseIndex < (transitionCases tm).length) :
    effectCaseInputSymbolIndexAt tm caseIndex < 4 := by
  rw [effectCaseInputSymbolIndexAt, dite_eq_left hcase]
  exact (symbolIndex _).isLt

private theorem effectCaseOutputSymbolIndexAt_lt (tm : NTM k)
    (caseIndex : ℕ) (hcase : caseIndex < (transitionCases tm).length) :
    effectCaseOutputSymbolIndexAt tm caseIndex < 4 := by
  rw [effectCaseOutputSymbolIndexAt, dite_eq_left hcase]
  exact (symbolIndex _).isLt

private theorem effectCaseWorkSymbolIndexAt_lt (tm : NTM k)
    (caseIndex workIndex : ℕ)
    (hcase : caseIndex < (transitionCases tm).length)
    (hwork : workIndex < k) :
    effectCaseWorkSymbolIndexAt tm caseIndex workIndex < 4 := by
  rw [effectCaseWorkSymbolIndexAt, dite_eq_left hcase, dite_eq_left hwork]
  exact (symbolIndex _).isLt

private theorem prefixSize_mono_effect
    (sizeAt : ℕ → ℕ) {first second : ℕ} (hle : first ≤ second) :
    prefixSize sizeAt first ≤ prefixSize sizeAt second := by
  induction second with
  | zero => simp_all
  | succ second ih =>
      by_cases heq : first = second + 1
      · subst first
        exact Nat.le_refl _
      · have hfirst : first ≤ second := by omega
        exact (ih hfirst).trans (by rw [prefixSize_succ]; omega)

private theorem EffectFormulaWidthCap.caseSize
    {tm : NTM k} {selects : TransitionEffect tm → Bool}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcap : EffectFormulaWidthCap tm selects values width)
    (inputLength caseIndex : ℕ)
    (hcase : caseIndex < (transitionCases tm).length) :
    effectFormulaCaseSize k (values inputLength Work.horizon)
          (effectCaseSelectedAt tm selects caseIndex)
          (effectCaseChoiceAt tm caseIndex) +
        values inputLength Work.horizon ≤
      width inputLength := by
  let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
    (values inputLength Work.horizon) (effectCaseSelectedAt tm selects)
    (effectCaseChoiceAt tm)
  have hsizeAt : sizeAt caseIndex =
      effectFormulaCaseSize k (values inputLength Work.horizon)
        (effectCaseSelectedAt tm selects caseIndex)
        (effectCaseChoiceAt tm caseIndex) := by
    simp [sizeAt, effectFormulaSizeAt, hcase]
  have hprefix := prefixSize_mono_effect sizeAt
    (show caseIndex + 1 ≤ (transitionCases tm).length by omega)
  rw [prefixSize_succ, hsizeAt] at hprefix
  have hstate : stateIndex tm tm.qstart < Fintype.card tm.Q :=
    (Fintype.equivFin tm.Q tm.qstart).isLt
  have hbound := hcap inputLength (stateIndex tm tm.qstart) 0 0 0
    hstate (by omega) (by omega) (Nat.zero_le _)
  simp only [effectFormulaScheduleSize] at hbound
  change _ ≤ _ at hprefix
  dsimp only [sizeAt] at hprefix
  omega

private theorem emitEffectCaseAt_spaceBoundByWidthAt
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (caseIndex : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcase : caseIndex < (transitionCases tm).length)
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength tapeIndex symbolIndex position,
      tapeIndex ≤ k + 1 → symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            effectFormulaCaseSize k (values inputLength Work.horizon)
              (effectCaseSelectedAt tm selects caseIndex)
              (effectCaseChoiceAt tm caseIndex) +
          transitionStateRef (values inputLength Work.configBase)
            (effectCaseStateIndexAt tm caseIndex) +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitEffectCaseAt tm selects caseIndex)
      initialSpace values width := by
  rw [emitEffectCaseAt]
  by_cases hselected : effectCaseSelectedAt tm selects caseIndex
  · rw [ite_eq_left hselected]
    apply emitCaseFormula_spaceBoundByWidth
    · exact hclean
    · exact hvalues
    · exact effectCaseInputSymbolIndexAt_lt tm caseIndex hcase
    · exact effectCaseOutputSymbolIndexAt_lt tm caseIndex hcase
    · exact fun index hindex =>
        effectCaseWorkSymbolIndexAt_lt tm caseIndex index hcase hindex
    · intro inputLength tapeIndex symbolIndex position htape hsymbol
        hposition
      have hbound := hcap inputLength tapeIndex symbolIndex position htape
        hsymbol hposition
      simpa [effectFormulaCaseSize, hselected] using hbound
  · rw [ite_eq_right hselected]
    exact emitConstantGate_spaceBoundByWidth false
      (fun inputLength => hvalues inputLength Work.available)
      (fun inputLength => hvalues inputLength Work.reference₀)

private theorem emitEffectMembersFrom_spaceBoundByWidthAt
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    (start count : ℕ) {initialSpace : ℕ → ℕ}
    {source values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hbound : start + count ≤ (transitionCases tm).length)
    (hsourceClean : ∀ inputLength,
      CaseFormulaClean (source inputLength))
    (hsourceValues : ∀ inputLength index,
      source inputLength index ≤ width inputLength)
    (htrajectory : ∀ inputLength,
      values inputLength =
        Function.update (source inputLength) Work.available
          (source inputLength Work.available +
            prefixSize
              (effectFormulaSizeAt (transitionCases tm).length k
                (source inputLength Work.horizon)
                (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
              start))
    (hcap : EffectFormulaWidthCap tm selects source width) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitEffectMembersFrom tm selects start count)
      initialSpace values width := by
  induction count generalizing start values with
  | zero =>
      simpa [emitEffectMembersFrom] using
        (BinaryRoutine.SpaceBoundByWidthAt.identity (n := WorkCount)
          (initialSpace := initialSpace) (values := values) (width := width))
  | succ count ih =>
      have hcase : start < (transitionCases tm).length := by omega
      have hcurrentClean : ∀ inputLength,
          CaseFormulaClean (values inputLength) := by
        intro inputLength
        rw [htrajectory inputLength]
        exact CaseFormulaClean.updateAvailable (source inputLength)
          (hsourceClean inputLength) _
      have hcurrentValues : ∀ inputLength index,
          values inputLength index ≤ width inputLength := by
        intro inputLength
        rw [htrajectory inputLength]
        apply BinaryRoutine.values_update_le Work.available
          (hsourceValues inputLength)
        have hprefix := prefixSize_mono_effect
          (effectFormulaSizeAt (transitionCases tm).length k
            (source inputLength Work.horizon)
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (show start ≤ (transitionCases tm).length by omega)
        have hfrontier := hcap.frontier inputLength
        simp only [effectFormulaScheduleSize] at hfrontier
        omega
      have hlocalCap : ∀ inputLength tapeIndex symbolIndex position,
          tapeIndex ≤ k + 1 → symbolIndex < 4 →
          position ≤ values inputLength Work.horizon →
            values inputLength Work.available +
                effectFormulaCaseSize k
                  (values inputLength Work.horizon)
                  (effectCaseSelectedAt tm selects start)
                  (effectCaseChoiceAt tm start) +
              transitionStateRef (values inputLength Work.configBase)
                (effectCaseStateIndexAt tm start) +
              (transitionHeadRef (Fintype.card tm.Q)
                    (values inputLength Work.horizon)
                    (values inputLength Work.configBase) tapeIndex position +
                  tapeIndex + values inputLength Work.horizon + 1) +
              (transitionCellRef (Fintype.card tm.Q) (k + 2)
                    (values inputLength Work.horizon)
                    (values inputLength Work.configBase) tapeIndex position
                    symbolIndex +
                  (tapeIndex * (values inputLength Work.horizon + 2) +
                    position) +
                  (values inputLength Work.horizon + 2) + (k + 2) +
                  tapeIndex + 4) +
              caseReadSize (values inputLength Work.horizon) +
              values inputLength Work.horizon ≤ width inputLength := by
        intro inputLength tapeIndex symbolIndex position htape hsymbol
          hposition
        let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
          (source inputLength Work.horizon)
          (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
        have hpositionSource :
            position ≤ source inputLength Work.horizon := by
          rw [htrajectory inputLength] at hposition
          simpa [Work.available, Work.horizon] using hposition
        have hglobal := hcap inputLength
          (effectCaseStateIndexAt tm start) tapeIndex symbolIndex position
          (effectCaseStateIndexAt_lt tm start hcase) htape hsymbol
          hpositionSource
        have hprefix := prefixSize_mono_effect sizeAt
          (show start + 1 ≤ (transitionCases tm).length by omega)
        rw [prefixSize_succ] at hprefix
        have hsizeAt : sizeAt start =
            effectFormulaCaseSize k (source inputLength Work.horizon)
              (effectCaseSelectedAt tm selects start)
              (effectCaseChoiceAt tm start) := by
          simp [sizeAt, effectFormulaSizeAt, hcase]
        rw [hsizeAt] at hprefix
        simp only [effectFormulaScheduleSize] at hglobal
        rw [htrajectory inputLength]
        dsimp only [sizeAt] at hprefix
        simp [Work.available, Work.horizon, Work.configBase]
          at hglobal hprefix ⊢
        omega
      have hhead : BinaryRoutine.SpaceBoundByWidthAt
          (emitEffectCaseAt tm selects start) initialSpace values width :=
        emitEffectCaseAt_spaceBoundByWidthAt tm selects start hcase
          hcurrentClean hcurrentValues hlocalCap
      let nextValues : ℕ → BinaryValues WorkCount := fun inputLength =>
        (emitEffectCaseAt tm selects start).effect (values inputLength)
      have hnextTrajectory : ∀ inputLength,
          nextValues inputLength =
            Function.update (source inputLength) Work.available
              (source inputLength Work.available +
                prefixSize
                  (effectFormulaSizeAt (transitionCases tm).length k
                    (source inputLength Work.horizon)
                    (effectCaseSelectedAt tm selects)
                    (effectCaseChoiceAt tm))
                  (start + 1)) := by
        intro inputLength
        dsimp only [nextValues]
        rw [emitEffectCaseAt_effect_internal tm selects start _
          (hcurrentClean inputLength), htrajectory inputLength]
        funext index
        by_cases hindex : index = Work.available
        · subst index
          simp [prefixSize_succ, effectFormulaSizeAt, hcase,
            Work.available, Work.horizon, Nat.add_assoc]
        · simp [Function.update_apply, hindex]
      have htail : BinaryRoutine.SpaceBoundByWidthAt
          (emitEffectMembersFrom tm selects (start + 1) count)
          initialSpace nextValues width :=
        ih (start + 1) (values := nextValues) (by omega) hnextTrajectory
      have hseq := BinaryRoutine.SpaceBoundByWidthAt.seq hhead htail
      simpa [emitEffectMembersFrom, nextValues] using hseq

private theorem emitEffectMembers_spaceBoundByWidthAt
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : EffectFormulaWidthCap tm selects values width) :
    BinaryRoutine.SpaceBoundByWidthAt (emitEffectMembers tm selects)
      initialSpace values width := by
  apply emitEffectMembersFrom_spaceBoundByWidthAt tm selects 0
    (transitionCases tm).length (by omega) hclean hvalues
  · intro inputLength
    funext index
    by_cases hindex : index = Work.available
    · subst index
      simp [prefixSize, Work.available]
    · simp [prefixSize, hindex]
  · exact hcap

private theorem prepareEffectCaseSize_spaceBoundByWidthAt
    (workCount : ℕ) (selected choiceValue : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      effectFormulaCaseSize workCount (values inputLength Work.horizon)
            selected choiceValue +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareEffectCaseSize workCount selected choiceValue)
      initialSpace values width := by
  cases selected with
  | false =>
      simpa [prepareEffectCaseSize] using
        (BinaryRoutine.SpaceBoundByWidthAt.set Work.temporary₃ 1
          (fun inputLength => hvalues inputLength Work.temporary₃)
          (fun inputLength => by
            have := hcap inputLength
            simp [effectFormulaCaseSize] at this
            omega))
  | true =>
      have hsize (T : ℕ) :
          effectFormulaCaseSize workCount T true choiceValue =
            (6 * workCount + 16 + caseChoiceLiteralSize choiceValue) +
              T * (4 * (workCount + 2)) := by
        simp [effectFormulaCaseSize, caseFormulaScheduleSize,
          caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize]
        ring
      have htotal : ∀ inputLength,
          (6 * workCount + 16 + caseChoiceLiteralSize choiceValue) +
                values inputLength Work.horizon * (4 * (workCount + 2)) +
              values inputLength Work.horizon ≤
            width inputLength := by
        intro inputLength
        rw [← hsize]
        exact hcap inputLength
      have hconstant : ∀ inputLength,
          6 * workCount + 16 + caseChoiceLiteralSize choiceValue ≤
            width inputLength := by
        intro inputLength
        have := htotal inputLength
        omega
      have hfactor : ∀ inputLength,
          4 * (workCount + 2) ≤ width inputLength := by
        intro inputLength
        have hconstantBound := hconstant inputLength
        omega
      apply BinaryRoutine.SpaceBoundByWidthAt.seqList
      simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
      constructor
      · apply BinaryRoutine.SpaceBoundByWidthAt.set
        · exact fun inputLength => hvalues inputLength Work.temporary₃
        · exact hconstant
      constructor
      · apply BinaryRoutine.SpaceBoundByWidthAt.set
        · intro inputLength
          simpa [BinaryRoutine.set, BinaryRoutine.seq,
            BinaryRoutine.clear, BinaryRoutine.addConst, Work.temporary₂,
            Work.temporary₃] using hvalues inputLength Work.temporary₂
        · exact hfactor
      constructor
      · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd
        · intro inputLength
          simpa [BinaryRoutine.set, BinaryRoutine.seq,
            BinaryRoutine.clear, BinaryRoutine.addConst, Work.horizon,
            Work.temporary₂, Work.temporary₃] using
              hvalues inputLength Work.horizon
        · intro inputLength
          simpa [BinaryRoutine.set, BinaryRoutine.seq,
            BinaryRoutine.clear, BinaryRoutine.addConst, Work.temporary₂,
            Work.temporary₃] using hfactor inputLength
        · intro inputLength
          simpa [BinaryRoutine.set, BinaryRoutine.seq,
            BinaryRoutine.clear, BinaryRoutine.addConst, Work.horizon,
            Work.temporary₂, Work.temporary₃, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
              htotal inputLength
      constructor
      · apply BinaryRoutine.SpaceBoundByWidthAt.clear
        intro inputLength
        simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
          BinaryRoutine.addConst, BinaryRoutine.mulAdd, Work.horizon,
          Work.temporary₂, Work.temporary₃] using hfactor inputLength
      · trivial

private theorem emitPreviousEffectConnector_spaceBoundByWidthAt
    (workCount : ℕ) (selected choiceValue : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hclean : ∀ inputLength, EffectConnectorClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      effectFormulaCaseSize workCount (values inputLength Work.horizon)
            selected choiceValue +
          values inputLength Work.horizon ≤ width inputLength)
    (hfit : ∀ inputLength,
      effectFormulaCaseSize workCount (values inputLength Work.horizon)
          selected choiceValue ≤ values inputLength Work.reference₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPreviousEffectConnector workCount selected choiceValue)
      initialSpace values width := by
  let prepare := prepareEffectCaseSize workCount selected choiceValue
  let decrement := decrementReferenceBy Work.reference₀ Work.temporary₃
    Work.loop₃
  let prepared : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let decremented : ℕ → BinaryValues WorkCount := fun inputLength =>
    decrement.effect (prepared inputLength)
  let connected : ℕ → BinaryValues WorkCount := fun inputLength =>
    emitReadConnector.effect (decremented inputLength)
  have hsize : ∀ inputLength,
      effectFormulaCaseSize workCount (values inputLength Work.horizon)
          selected choiceValue ≤ width inputLength := by
    intro inputLength
    exact (Nat.le_add_right _ _).trans (hcap inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width :=
    prepareEffectCaseSize_spaceBoundByWidthAt workCount selected choiceValue
      hvalues hcap
  have hpreparedEffect : ∀ inputLength,
      prepared inputLength =
        Function.update
          (Function.update (values inputLength) Work.temporary₃
            (effectFormulaCaseSize workCount
              (values inputLength Work.horizon) selected choiceValue))
          Work.temporary₂ 0 := by
    intro inputLength
    exact prepareEffectCaseSize_effect_internal workCount selected choiceValue
      (values inputLength) (hclean inputLength).temporary₂
  have hpreparedValues : ∀ inputLength index,
      prepared inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hpreparedEffect inputLength]
    exact BinaryRoutine.values_update_le Work.temporary₂
      (BinaryRoutine.values_update_le Work.temporary₃
        (hvalues inputLength) (hsize inputLength)) (Nat.zero_le _)
  have hpreparedLoop : ∀ inputLength,
      prepared inputLength Work.loop₃ = 0 := by
    intro inputLength
    rw [hpreparedEffect inputLength]
    simpa [Work.temporary₃, Work.temporary₂, Work.loop₃] using
      (hclean inputLength).loop₃
  have hdecrement : BinaryRoutine.SpaceBoundByWidthAt decrement initialSpace
      prepared width := by
    apply decrementReferenceBy_spaceBoundByWidth Work.reference₀
      Work.temporary₃ Work.loop₃ ⟨by decide, by decide, by decide⟩
    · intro inputLength
      rw [hpreparedLoop inputLength]
      omega
    · intro inputLength
      rw [hpreparedLoop inputLength, hpreparedEffect inputLength]
      simpa [Work.temporary₃, Work.temporary₂, Work.reference₀]
        using hfit inputLength
    · exact fun inputLength => hpreparedValues inputLength Work.reference₀
    · exact fun inputLength => hpreparedValues inputLength Work.temporary₃
  have hdecrementedEffect : ∀ inputLength,
      decremented inputLength =
        Function.update
          (Function.update (prepared inputLength) Work.reference₀
            (prepared inputLength Work.reference₀ -
              prepared inputLength Work.temporary₃))
          Work.loop₃ 0 := by
    intro inputLength
    exact decrementReferenceBy_effect Work.reference₀ Work.temporary₃
      Work.loop₃ (prepared inputLength) ⟨by decide, by decide, by decide⟩
        (hpreparedLoop inputLength)
  have hdecrementedValues : ∀ inputLength index,
      decremented inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hdecrementedEffect inputLength]
    apply BinaryRoutine.values_update_le Work.loop₃
    · apply BinaryRoutine.values_update_le Work.reference₀
        (hpreparedValues inputLength)
      exact (Nat.sub_le _ _).trans
        (hpreparedValues inputLength Work.reference₀)
    · exact Nat.zero_le _
  have hconnector : BinaryRoutine.SpaceBoundByWidthAt emitReadConnector
      initialSpace decremented width := by
    apply emitReadConnector_spaceBoundByWidth
    · exact fun inputLength =>
        hdecrementedValues inputLength Work.available
    · intro inputLength
      rw [hdecrementedEffect inputLength, hpreparedEffect inputLength]
      simpa [Work.reference₀, Work.loop₃, Work.temporary₃,
        Work.temporary₂, Work.available] using
          havailablePositive inputLength
    · exact fun inputLength =>
        hdecrementedValues inputLength Work.reference₀
    · exact fun inputLength =>
        hdecrementedValues inputLength Work.reference₁
  have hconnectedValues : ∀ inputLength index,
      connected inputLength index ≤ width inputLength := by
    intro inputLength
    rw [show connected inputLength =
        emitReadConnector.effect (decremented inputLength) by rfl,
      emitReadConnector_effect_internal]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.available
        (hdecrementedValues inputLength)
      rw [hdecrementedEffect inputLength, hpreparedEffect inputLength]
      simpa [Work.reference₀, Work.loop₃, Work.temporary₃,
        Work.temporary₂, Work.available] using havailable inputLength
    · exact Nat.zero_le _
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace connected width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      (fun inputLength => hconnectedValues inputLength Work.temporary₃)
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength =>
        (BinaryRoutine.clear Work.temporary₃).effect
          (connected inputLength)) width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hprepare
    (BinaryRoutine.SpaceBoundByWidthAt.seq hdecrement
      (BinaryRoutine.SpaceBoundByWidthAt.seq hconnector
        (BinaryRoutine.SpaceBoundByWidthAt.seq hclear hid)))
  simpa [emitPreviousEffectConnector, BinaryRoutine.seqList, prepare,
    decrement, prepared, decremented, connected] using hroutine

private theorem emitPreviousEffectConnectorsCount_spaceBoundByWidthAt
    (tm : NTM k) (selects : TransitionEffect tm → Bool) (count : ℕ)
    (base horizon : ℕ → ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, EffectConnectorClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcount : count + 1 ≤ (transitionCases tm).length)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon = horizon inputLength)
    (hreference : ∀ inputLength,
      values inputLength Work.reference₀ =
        base inputLength +
          prefixSize
            (effectFormulaSizeAt (transitionCases tm).length k
              (horizon inputLength) (effectCaseSelectedAt tm selects)
              (effectCaseChoiceAt tm))
            (count + 1) -
          1)
    (havailable : ∀ inputLength,
      values inputLength Work.available + count ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hcaseCap : ∀ inputLength caseIndex,
      caseIndex < (transitionCases tm).length →
        effectFormulaCaseSize k (horizon inputLength)
              (effectCaseSelectedAt tm selects caseIndex)
              (effectCaseChoiceAt tm caseIndex) +
            horizon inputLength ≤
          width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
        (emitPreviousEffectConnectorsCount tm selects count)
        initialSpace values width ∧
      ∀ inputLength index,
        (emitPreviousEffectConnectorsCount tm selects count).effect
            (values inputLength) index ≤
          width inputLength := by
  induction count generalizing values with
  | zero =>
      constructor
      · simpa [emitPreviousEffectConnectorsCount] using
          (BinaryRoutine.SpaceBoundByWidthAt.identity (n := WorkCount)
            (initialSpace := initialSpace) (values := values)
            (width := width))
      · intro inputLength index
        simp [emitPreviousEffectConnectorsCount, BinaryRoutine.identity]
        exact hvalues inputLength index
  | succ count ih =>
      let selected := effectCaseSelectedAt tm selects (count + 1)
      let choiceValue := effectCaseChoiceAt tm (count + 1)
      have hindex : count + 1 < (transitionCases tm).length := by omega
      have hfit : ∀ inputLength,
          effectFormulaCaseSize k (values inputLength Work.horizon)
              selected choiceValue ≤
            values inputLength Work.reference₀ := by
        intro inputLength
        let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
          (horizon inputLength) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)
        have hsizeAt : sizeAt (count + 1) =
            effectFormulaCaseSize k (horizon inputLength) selected
              choiceValue := by
          simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
        have hsizeZero : 1 ≤ sizeAt 0 := by
          have hzero : 0 < (transitionCases tm).length := by omega
          rw [show sizeAt 0 =
            effectFormulaCaseSize k (horizon inputLength)
              (effectCaseSelectedAt tm selects 0)
              (effectCaseChoiceAt tm 0) by
                simp [sizeAt, effectFormulaSizeAt, hzero]]
          exact effectFormulaCaseSize_pos k (horizon inputLength) _ _
        have hprefixPositive :
            1 ≤ prefixSize sizeAt (count + 1) := by
          calc
            1 ≤ prefixSize sizeAt 1 := by
              simpa [prefixSize] using hsizeZero
            _ ≤ prefixSize sizeAt (count + 1) :=
              prefixSize_mono_effect sizeAt (by omega)
        have hprefix : prefixSize sizeAt (count + 2) =
            prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
          rw [show count + 2 = (count + 1) + 1 by omega,
            prefixSize_succ]
        rw [hhorizon inputLength, hreference inputLength]
        change _ ≤ base inputLength + prefixSize sizeAt (count + 2) - 1
        rw [hprefix, hsizeAt]
        omega
      have hhead : BinaryRoutine.SpaceBoundByWidthAt
          (emitPreviousEffectConnector k selected choiceValue)
          initialSpace values width := by
        apply emitPreviousEffectConnector_spaceBoundByWidthAt k selected
          choiceValue hclean hvalues
        · intro inputLength
          rw [hhorizon inputLength]
          exact hcaseCap inputLength (count + 1) hindex
        · exact hfit
        · intro inputLength
          have hbound := havailable inputLength
          omega
        · exact havailablePositive
      let current : ℕ → BinaryValues WorkCount := fun inputLength =>
        (emitPreviousEffectConnector k selected choiceValue).effect
          (values inputLength)
      have hcurrentEffect : ∀ inputLength,
          current inputLength =
            Function.update
              (Function.update (values inputLength) Work.reference₀
                (values inputLength Work.reference₀ -
                  effectFormulaCaseSize k
                    (values inputLength Work.horizon) selected choiceValue))
              Work.available (values inputLength Work.available + 1) := by
        intro inputLength
        exact emitPreviousEffectConnector_effect_internal k selected
          choiceValue (values inputLength) (hclean inputLength)
      have hcurrentClean : ∀ inputLength,
          EffectConnectorClean (current inputLength) := by
        intro inputLength
        exact EffectConnectorClean.afterPrevious k selected choiceValue
          (values inputLength) (hclean inputLength)
      have hcurrentValues : ∀ inputLength index,
          current inputLength index ≤ width inputLength := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        apply BinaryRoutine.values_update_le Work.available
        · apply BinaryRoutine.values_update_le Work.reference₀
              (hvalues inputLength)
          exact (Nat.sub_le _ _).trans
            (hvalues inputLength Work.reference₀)
        · have hbound := havailable inputLength
          omega
      have hcurrentHorizon : ∀ inputLength,
          current inputLength Work.horizon = horizon inputLength := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simpa [Work.reference₀, Work.available, Work.horizon] using
          hhorizon inputLength
      have hcurrentReference : ∀ inputLength,
          current inputLength Work.reference₀ =
            base inputLength +
              prefixSize
                (effectFormulaSizeAt (transitionCases tm).length k
                  (horizon inputLength) (effectCaseSelectedAt tm selects)
                  (effectCaseChoiceAt tm))
                (count + 1) -
              1 := by
        intro inputLength
        let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
          (horizon inputLength) (effectCaseSelectedAt tm selects)
          (effectCaseChoiceAt tm)
        have hsizeAt : sizeAt (count + 1) =
            effectFormulaCaseSize k (horizon inputLength) selected
              choiceValue := by
          simp [sizeAt, effectFormulaSizeAt, selected, choiceValue, hindex]
        have hprefix : prefixSize sizeAt (count + 2) =
            prefixSize sizeAt (count + 1) + sizeAt (count + 1) := by
          rw [show count + 2 = (count + 1) + 1 by omega,
            prefixSize_succ]
        have hsizeZero : 1 ≤ sizeAt 0 := by
          have hzero : 0 < (transitionCases tm).length := by omega
          rw [show sizeAt 0 =
            effectFormulaCaseSize k (horizon inputLength)
              (effectCaseSelectedAt tm selects 0)
              (effectCaseChoiceAt tm 0) by
                simp [sizeAt, effectFormulaSizeAt, hzero]]
          exact effectFormulaCaseSize_pos k (horizon inputLength) _ _
        have hprefixPositive :
            1 ≤ prefixSize sizeAt (count + 1) := by
          calc
            1 ≤ prefixSize sizeAt 1 := by
              simpa [prefixSize] using hsizeZero
            _ ≤ prefixSize sizeAt (count + 1) :=
              prefixSize_mono_effect sizeAt (by omega)
        rw [hcurrentEffect inputLength]
        simp only [Function.update_apply, Work.reference₀, Work.available]
        rw [ite_eq_right (by decide), ite_eq_left True.intro]
        change values inputLength Work.reference₀ - _ = _
        rw [hreference inputLength, hhorizon inputLength]
        change (base inputLength + prefixSize sizeAt (count + 2) - 1) -
            _ = _
        rw [hprefix, hsizeAt]
        rw [← Nat.add_assoc,
          Nat.sub_add_comm (show 1 ≤
            base inputLength + prefixSize sizeAt (count + 1) by omega),
          Nat.add_sub_cancel]
      have hcurrentAvailable : ∀ inputLength,
          current inputLength Work.available + count ≤
            width inputLength := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₀, Work.available]
        have hbound := havailable inputLength
        simp only [Work.available] at hbound
        omega
      have hcurrentAvailablePositive : ∀ inputLength,
          1 ≤ current inputLength Work.available := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₀, Work.available]
      obtain ⟨htail, htailValues⟩ :=
        ih (values := current) hcurrentClean hcurrentValues (by omega)
          hcurrentHorizon hcurrentReference hcurrentAvailable
          hcurrentAvailablePositive
      constructor
      · have hseq := BinaryRoutine.SpaceBoundByWidthAt.seq hhead htail
        simpa [emitPreviousEffectConnectorsCount, current] using hseq
      · intro inputLength index
        simpa [emitPreviousEffectConnectorsCount, BinaryRoutine.seq, current]
          using htailValues inputLength index

private theorem emitEffectConnectors_spaceBoundByWidthAt
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    {initialSpace : ℕ → ℕ}
    {source values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hsourceClean : ∀ inputLength,
      CaseFormulaClean (source inputLength))
    (hsourceValues : ∀ inputLength index,
      source inputLength index ≤ width inputLength)
    (htrajectory : ∀ inputLength,
      values inputLength =
        Function.update (source inputLength) Work.available
          (source inputLength Work.available +
            prefixSize
              (effectFormulaSizeAt (transitionCases tm).length k
                (source inputLength Work.horizon)
                (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
              (transitionCases tm).length +
            1))
    (hcap : EffectFormulaWidthCap tm selects source width) :
    BinaryRoutine.SpaceBoundByWidthAt (emitEffectConnectors tm selects)
        initialSpace values width ∧
      ∀ inputLength index,
        (emitEffectConnectors tm selects).effect (values inputLength) index ≤
          width inputLength := by
  have hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength := by
    intro inputLength
    rw [htrajectory inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hsourceValues inputLength)
    have hfrontier := hcap.frontier inputLength
    simp only [effectFormulaScheduleSize] at hfrontier
    omega
  have hclean : ∀ inputLength,
      CaseFormulaClean (values inputLength) := by
    intro inputLength
    rw [htrajectory inputLength]
    exact CaseFormulaClean.updateAvailable (source inputLength)
      (hsourceClean inputLength) _
  rw [emitEffectConnectors]
  split_ifs with hempty
  · constructor
    · exact BinaryRoutine.SpaceBoundByWidthAt.identity
    · intro inputLength index
      simp [BinaryRoutine.identity]
      exact hvalues inputLength index
  · have hlength : (transitionCases tm).length ≠ 0 := by
      intro hzero
      exact hempty (List.isEmpty_iff_length_eq_zero.mpr hzero)
    have hlengthPositive : 0 < (transitionCases tm).length := by omega
    have hprefixPositive : ∀ inputLength,
        1 ≤ prefixSize
          (effectFormulaSizeAt (transitionCases tm).length k
            (source inputLength Work.horizon)
            (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
          (transitionCases tm).length := by
      intro inputLength
      let sizeAt := effectFormulaSizeAt (transitionCases tm).length k
        (source inputLength Work.horizon)
        (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm)
      have hsizeZero : 1 ≤ sizeAt 0 := by
        rw [show sizeAt 0 =
          effectFormulaCaseSize k (source inputLength Work.horizon)
            (effectCaseSelectedAt tm selects 0)
            (effectCaseChoiceAt tm 0) by
              simp [sizeAt, effectFormulaSizeAt, hlengthPositive]]
        exact effectFormulaCaseSize_pos k
          (source inputLength Work.horizon) _ _
      calc
        1 ≤ prefixSize sizeAt 1 := by
          simpa [prefixSize] using hsizeZero
        _ ≤ prefixSize sizeAt (transitionCases tm).length :=
          prefixSize_mono_effect sizeAt hlengthPositive
    have havailableTwo : ∀ inputLength,
        2 ≤ values inputLength Work.available := by
      intro inputLength
      rw [htrajectory inputLength]
      simp [Work.available]
      have hprefix := hprefixPositive inputLength
      omega
    let prepare := prepareRecentReference Work.reference₀ 2
    let prepared : ℕ → BinaryValues WorkCount := fun inputLength =>
      prepare.effect (values inputLength)
    have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
        values width := by
      apply prepareRecentReference_spaceBoundByWidth Work.reference₀ 2
      · exact fun inputLength => hvalues inputLength Work.available
      · exact fun inputLength => hvalues inputLength Work.reference₀
      · exact havailableTwo
    have hpreparedEffect : ∀ inputLength,
        prepared inputLength =
          Function.update (values inputLength) Work.reference₀
            (values inputLength Work.available - 2) := by
      intro inputLength
      exact prepareRecentReference_effect Work.reference₀ 2
        (values inputLength)
    have hpreparedValues : ∀ inputLength index,
        prepared inputLength index ≤ width inputLength := by
      intro inputLength
      rw [hpreparedEffect inputLength]
      exact BinaryRoutine.values_update_le Work.reference₀
        (hvalues inputLength)
        ((Nat.sub_le _ _).trans (hvalues inputLength Work.available))
    have hpreparedClean : ∀ inputLength,
        EffectConnectorClean (prepared inputLength) := by
      intro inputLength
      rw [hpreparedEffect inputLength]
      exact EffectConnectorClean.updateReference₀ (values inputLength)
        (hclean inputLength).effectConnectorClean _
    have hinitial : BinaryRoutine.SpaceBoundByWidthAt emitReadConnector
        initialSpace prepared width := by
      apply emitReadConnector_spaceBoundByWidth
      · exact fun inputLength =>
          hpreparedValues inputLength Work.available
      · exact fun inputLength => (havailableTwo inputLength).trans'
          (by omega)
      · exact fun inputLength =>
          hpreparedValues inputLength Work.reference₀
      · exact fun inputLength =>
          hpreparedValues inputLength Work.reference₁
    let connected : ℕ → BinaryValues WorkCount := fun inputLength =>
      emitReadConnector.effect (prepared inputLength)
    have hconnectedEffect : ∀ inputLength,
        connected inputLength =
          Function.update
            (Function.update (prepared inputLength) Work.available
              (prepared inputLength Work.available + 1))
            Work.reference₁ 0 := by
      intro inputLength
      exact emitReadConnector_effect_internal (prepared inputLength)
    have havailableNext : ∀ inputLength,
        prepared inputLength Work.available + 1 ≤ width inputLength := by
      intro inputLength
      rw [hpreparedEffect inputLength, htrajectory inputLength]
      simp [Work.reference₀, Work.available]
      have hfrontier := hcap.frontier inputLength
      simp only [effectFormulaScheduleSize] at hfrontier
      simp only [Work.available] at hfrontier
      omega
    have hconnectedValues : ∀ inputLength index,
        connected inputLength index ≤ width inputLength := by
      intro inputLength
      rw [hconnectedEffect inputLength]
      exact BinaryRoutine.values_update_le Work.reference₁
        (BinaryRoutine.values_update_le Work.available
          (hpreparedValues inputLength) (havailableNext inputLength))
        (Nat.zero_le _)
    have hconnectedClean : ∀ inputLength,
        EffectConnectorClean (connected inputLength) := by
      intro inputLength
      exact EffectConnectorClean.afterReadConnector (prepared inputLength)
        (hpreparedClean inputLength)
    have hconnectedHorizon : ∀ inputLength,
        connected inputLength Work.horizon =
          source inputLength Work.horizon := by
      intro inputLength
      rw [hconnectedEffect inputLength, hpreparedEffect inputLength,
        htrajectory inputLength]
      simp [Work.reference₀, Work.reference₁, Work.available,
        Work.horizon]
    have hconnectedReference : ∀ inputLength,
        connected inputLength Work.reference₀ =
          source inputLength Work.available +
              prefixSize
                (effectFormulaSizeAt (transitionCases tm).length k
                  (source inputLength Work.horizon)
                  (effectCaseSelectedAt tm selects)
                  (effectCaseChoiceAt tm))
                (transitionCases tm).length -
            1 := by
      intro inputLength
      rw [hconnectedEffect inputLength, hpreparedEffect inputLength,
        htrajectory inputLength]
      simp [Work.reference₀, Work.reference₁, Work.available]
    have hconnectedAvailable : ∀ inputLength,
        connected inputLength Work.available +
            ((transitionCases tm).length - 1) ≤
          width inputLength := by
      intro inputLength
      rw [hconnectedEffect inputLength, hpreparedEffect inputLength,
        htrajectory inputLength]
      simp [Work.reference₀, Work.reference₁, Work.available]
      have hfrontier := hcap.frontier inputLength
      simp only [effectFormulaScheduleSize] at hfrontier
      simp only [Work.available] at hfrontier
      omega
    have hconnectedAvailablePositive : ∀ inputLength,
        1 ≤ connected inputLength Work.available := by
      intro inputLength
      rw [hconnectedEffect inputLength]
      simp [Work.reference₁, Work.available]
    obtain ⟨hprevious, hpreviousValues⟩ :=
      emitPreviousEffectConnectorsCount_spaceBoundByWidthAt tm selects
        ((transitionCases tm).length - 1)
        (fun inputLength => source inputLength Work.available)
        (fun inputLength => source inputLength Work.horizon)
        hconnectedClean hconnectedValues (by omega) hconnectedHorizon
        (by
          intro inputLength
          rw [show (transitionCases tm).length - 1 + 1 =
            (transitionCases tm).length by omega]
          exact hconnectedReference inputLength)
        hconnectedAvailable hconnectedAvailablePositive
        (fun inputLength caseIndex hcase => hcap.caseSize inputLength
          caseIndex hcase)
    let afterPrevious : ℕ → BinaryValues WorkCount :=
      fun inputLength =>
        (emitPreviousEffectConnectorsCount tm selects
          ((transitionCases tm).length - 1)).effect
            (connected inputLength)
    have hclear : BinaryRoutine.SpaceBoundByWidthAt
        (BinaryRoutine.clear Work.reference₀) initialSpace afterPrevious
        width :=
      BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₀
        (fun inputLength => hpreviousValues inputLength Work.reference₀)
    have hfinalValues : ∀ inputLength index,
        (BinaryRoutine.clear Work.reference₀).effect
            (afterPrevious inputLength) index ≤
          width inputLength := by
      intro inputLength
      exact BinaryRoutine.values_update_le Work.reference₀
        (hpreviousValues inputLength) (Nat.zero_le _)
    constructor
    · apply BinaryRoutine.SpaceBoundByWidthAt.seqList
      simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
      exact ⟨hprepare, hinitial, hprevious, hclear, trivial⟩
    · intro inputLength index
      simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
        BinaryRoutine.identity]
      exact hfinalValues inputLength index

theorem emitEffectFormula_spaceBoundByWidth_internal
    (tm : NTM k) (selects : TransitionEffect tm → Bool)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            effectFormulaScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm) +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (k + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitEffectFormula tm selects)
      initialSpace values width := by
  have hwidthCap : EffectFormulaWidthCap tm selects values width := hcap
  let members := emitEffectMembers tm selects
  let afterMembers : ℕ → BinaryValues WorkCount := fun inputLength =>
    members.effect (values inputLength)
  have hmembers : BinaryRoutine.SpaceBoundByWidthAt members initialSpace
      values width :=
    emitEffectMembers_spaceBoundByWidthAt tm selects hclean hvalues hwidthCap
  have hafterMembersEffect : ∀ inputLength,
      afterMembers inputLength =
        Function.update (values inputLength) Work.available
          (values inputLength Work.available +
            prefixSize
              (effectFormulaSizeAt (transitionCases tm).length k
                (values inputLength Work.horizon)
                (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
              (transitionCases tm).length) := by
    intro inputLength
    exact emitEffectMembers_effect_internal tm selects (values inputLength)
      (hclean inputLength)
  have hafterMembersValues : ∀ inputLength index,
      afterMembers inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hafterMembersEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hvalues inputLength)
    have hfrontier := hwidthCap.frontier inputLength
    simp only [effectFormulaScheduleSize] at hfrontier
    omega
  have hafterMembersClean : ∀ inputLength,
      CaseFormulaClean (afterMembers inputLength) := by
    intro inputLength
    rw [hafterMembersEffect inputLength]
    exact CaseFormulaClean.updateAvailable (values inputLength)
      (hclean inputLength) _
  let identityGate := emitConstantGate false
  let afterIdentity : ℕ → BinaryValues WorkCount :=
    fun inputLength => identityGate.effect (afterMembers inputLength)
  have hidentity : BinaryRoutine.SpaceBoundByWidthAt identityGate
      initialSpace afterMembers width := by
    apply emitConstantGate_spaceBoundByWidth false
    · exact fun inputLength =>
        hafterMembersValues inputLength Work.available
    · exact fun inputLength =>
        hafterMembersValues inputLength Work.reference₀
  have hafterIdentityTrajectory : ∀ inputLength,
      afterIdentity inputLength =
        Function.update (values inputLength) Work.available
          (values inputLength Work.available +
            prefixSize
              (effectFormulaSizeAt (transitionCases tm).length k
                (values inputLength Work.horizon)
                (effectCaseSelectedAt tm selects) (effectCaseChoiceAt tm))
              (transitionCases tm).length +
            1) := by
    intro inputLength
    dsimp only [afterIdentity, identityGate]
    rw [emitConstantGate_effect_internal false,
      hafterMembersEffect inputLength]
    funext index
    by_cases hindex : index = Work.available
    · subst index
      simp [Work.available]
    · simp [hindex]
  obtain ⟨hconnectors, _hfinalValues⟩ :=
    emitEffectConnectors_spaceBoundByWidthAt tm selects hclean hvalues
      hafterIdentityTrajectory hwidthCap
  rw [emitEffectFormula]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hmembers, hidentity, hconnectors, trivial⟩

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
