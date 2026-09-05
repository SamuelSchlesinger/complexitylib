/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Effect
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.WrittenCell.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.WrittenCell.Defs

/-!
# Direct-unrolling written-cell generator -- proof internals

This dependency-independent layer verifies the bounded numeric head test used
on both sides of a written-cell formula. The enclosing effect-formula proof is
intentionally deferred until that generator's public contracts are available.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem WrittenCellFormulaClean.headAtCurrentCellClean_internal
    {values : BinaryValues WorkCount}
    (hclean : WrittenCellFormulaClean values) :
    HeadAtCurrentCellClean values := by
  refine
    { loop₃ := ?_
      temporary₃ := ?_
      reference₀ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_
      temporary₀ := ?_ }
  · simpa [Work.position, Work.loop₃] using hclean.caseClean.loop₃
  · simpa [Work.position, Work.temporary₃] using
      hclean.caseClean.temporary₃
  · simpa [Work.position, Work.reference₀] using
      hclean.caseClean.reference₀
  · simpa [Work.position, Work.emitCounter] using
      hclean.caseClean.emitCounter
  · simpa [Work.position, Work.copyCounter] using
      hclean.caseClean.copyCounter
  · simpa [Work.position, Work.multiplyCounter] using
      hclean.caseClean.multiplyCounter
  · simpa [Work.position, Work.addCounter] using hclean.caseClean.addCounter
  · simpa [Work.position, Work.temporary₀] using
      hclean.caseClean.temporary₀

theorem emitHeadAtCurrentCellGate_sound_internal (stateCount : ℕ) :
    (emitHeadAtCurrentCellGate stateCount).Sound :=
  (emitConstantGate_sound false).branchZero
    (emitHeadReference_sound stateCount false) Work.temporary₃

theorem emitHeadAtCurrentCellGate_requires_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitHeadAtCurrentCellGate stateCount).requires values := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp only [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      ite_true]
    exact emitConstantGate_requires_internal false values hemit
  · simp only [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      ite_false]
    exact emitHeadReference_requires stateCount false values hadd hmultiply
      hemit

@[simp] theorem emitHeadAtCurrentCellGate_effect_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (htemporary : values Work.temporary₀ = 0)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadAtCurrentCellGate stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitConstantGate, BinaryRoutine.emitRawGateStep]
  · rw [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero]
    simp only [hzero, ite_false, emitHeadReference_effect]
    funext i
    simp only [Function.update_apply]
    split_ifs <;>
      simp_all [Work.temporary₀, Work.reference₀, Work.available]

@[simp] theorem emitHeadAtCurrentCellGate_emitted_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    (emitHeadAtCurrentCellGate stateCount).emitted values =
      CircuitCode.RawGate.encode
        (if values Work.temporary₃ = 0 then
          CircuitCode.RawGate.constant 0 false
        else
          CircuitCode.RawGate.copy
            (transitionHeadRef stateCount (values Work.horizon)
              (values Work.configBase) (values Work.tapeIndex)
              (values Work.position))) := by
  by_cases hzero : values Work.temporary₃ = 0
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitConstantGate, BinaryRoutine.emitRawGateStep,
      CircuitCode.RawGate.constant, hreference]
  · simp [emitHeadAtCurrentCellGate, BinaryRoutine.branchZero, hzero,
      emitHeadReference_emitted]

theorem emitHeadAtCurrentCell_sound_internal (stateCount : ℕ) :
    (emitHeadAtCurrentCell stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.horizon Work.temporary₃
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.addConst_sound Work.temporary₃ 1
  · subst routine
    exact decrementReferenceBy_sound Work.temporary₃ Work.position Work.loop₃
  · subst routine
    exact emitHeadAtCurrentCellGate_sound_internal stateCount
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitHeadAtCurrentCell_requires_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitHeadAtCurrentCell stateCount).requires values := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  let afterSucc :=
    (BinaryRoutine.addConst Work.temporary₃ 1).effect afterCopy
  let afterGap :=
    (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₃).effect afterSucc
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  have hafterSucc : afterSucc =
      Function.update afterCopy Work.temporary₃
        (afterCopy Work.temporary₃ + 1) := rfl
  have hloopSucc : afterSucc Work.loop₃ = 0 := by
    rw [hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.loop₃] using hclean.loop₃
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  have hafterGap : afterGap =
      Function.update
        (Function.update afterSucc Work.temporary₃
          (afterSucc Work.temporary₃ - afterSucc Work.position))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
      afterSucc hdistinct hloopSucc
  have hcopy :
      (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
        Work.copyCounter).requires values := by
    exact ⟨by decide, by decide, by decide, hclean.copyCounter⟩
  have hgap :
      (decrementReferenceBy Work.temporary₃ Work.position
        Work.loop₃).requires afterSucc := by
    rw [decrementReferenceBy_requires]
    refine ⟨hdistinct, hloopSucc, ?_⟩
    rw [hafterSucc, hafterCopy]
    simpa [Work.horizon, Work.temporary₃, Work.position] using hposition
  have hemitGap : afterGap Work.emitCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.emitCounter] using hclean.emitCounter
  have haddGap : afterGap Work.addCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.addCounter] using hclean.addCounter
  have hmultiplyGap : afterGap Work.multiplyCounter = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.multiplyCounter] using hclean.multiplyCounter
  have hbranch :
      (emitHeadAtCurrentCellGate stateCount).requires afterGap :=
    emitHeadAtCurrentCellGate_requires_internal stateCount afterGap haddGap
      hmultiplyGap hemitGap
  simp only [emitHeadAtCurrentCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨hcopy, trivial, hgap, hbranch, trivial, trivial⟩

@[simp] theorem emitHeadAtCurrentCell_effect_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values) :
    (emitHeadAtCurrentCell stateCount).effect values =
      Function.update values Work.available (values Work.available + 1) := by
  let afterCopy :=
    (BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
      Work.copyCounter).effect values
  let afterSucc :=
    (BinaryRoutine.addConst Work.temporary₃ 1).effect afterCopy
  let afterGap :=
    (decrementReferenceBy Work.temporary₃ Work.position
      Work.loop₃).effect afterSucc
  have hafterCopy : afterCopy =
      Function.update values Work.temporary₃ (values Work.horizon) := rfl
  have hafterSucc : afterSucc =
      Function.update afterCopy Work.temporary₃
        (afterCopy Work.temporary₃ + 1) := rfl
  have hloopSucc : afterSucc Work.loop₃ = 0 := by
    rw [hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.loop₃] using hclean.loop₃
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  have hafterGap : afterGap =
      Function.update
        (Function.update afterSucc Work.temporary₃
          (afterSucc Work.temporary₃ - afterSucc Work.position))
        Work.loop₃ 0 :=
    decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
      afterSucc hdistinct hloopSucc
  have htemporaryGap : afterGap Work.temporary₀ = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.temporary₀] using hclean.temporary₀
  have hreferenceGap : afterGap Work.reference₀ = 0 := by
    rw [hafterGap, hafterSucc, hafterCopy]
    simpa [Work.temporary₃, Work.position, Work.loop₃,
      Work.reference₀] using hclean.reference₀
  rw [emitHeadAtCurrentCell]
  change (BinaryRoutine.clear Work.temporary₃).effect
      ((emitHeadAtCurrentCellGate stateCount).effect afterGap) = _
  rw [emitHeadAtCurrentCellGate_effect_internal stateCount afterGap
    htemporaryGap hreferenceGap]
  rw [hafterGap, hafterSucc, hafterCopy]
  simp only [BinaryRoutine.clear]
  have htemporary₃ : values (25 : Fin WorkCount) = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.temporary₃, Work.position, Work.loop₃,
      Work.available]

@[simp] theorem emitHeadAtCurrentCell_emitted_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : HeadAtCurrentCellClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitHeadAtCurrentCell stateCount).emitted values =
      CircuitCode.RawGate.encode
        (headAtCellFormulaGate stateCount (values Work.horizon)
          (values Work.configBase) (values Work.tapeIndex)
          (values Work.position)) := by
  simp [emitHeadAtCurrentCell, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.addConst,
    decrementReferenceBy_emitted, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  let afterSucc := Function.update values Work.temporary₃
    (values Work.horizon + 1)
  change (emitHeadAtCurrentCellGate stateCount).emitted
      ((decrementReferenceBy Work.temporary₃ Work.position
        Work.loop₃).effect afterSucc) = _
  have hloop₃ : values (20 : Fin WorkCount) = 0 := by
    simpa [Work.loop₃] using hclean.loop₃
  have hloop : afterSucc Work.loop₃ = 0 := by
    simp [afterSucc, Work.temporary₃, Work.loop₃, hloop₃]
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  rw [decrementReferenceBy_effect Work.temporary₃ Work.position Work.loop₃
    afterSucc hdistinct hloop]
  let afterGap :=
    Function.update
      (Function.update afterSucc Work.temporary₃
        (afterSucc Work.temporary₃ - afterSucc Work.position))
      Work.loop₃ 0
  change (emitHeadAtCurrentCellGate stateCount).emitted afterGap = _
  have hreference₀ : values (7 : Fin WorkCount) = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference : afterGap Work.reference₀ = 0 := by
    simp [afterGap, afterSucc, Work.temporary₃, Work.position, Work.loop₃,
      Work.reference₀, hreference₀]
  rw [emitHeadAtCurrentCellGate_emitted_internal stateCount afterGap hreference]
  unfold headAtCellFormulaGate
  by_cases hrepresented : values Work.position < values Work.horizon + 1
  · have hrepresented' : values (30 : Fin WorkCount) < values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hrepresented
    have hgap : values (1 : Fin WorkCount) + 1 - values 30 ≠ 0 := by
      omega
    have hhead : values (30 : Fin WorkCount) ≤ values 1 := by
      omega
    simp [hgap, hhead, afterGap, afterSucc, Work.horizon,
      Work.configBase, Work.tapeIndex, Work.position, Work.temporary₃,
      Work.loop₃]
  · have hrepresented' : ¬values (30 : Fin WorkCount) < values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hrepresented
    have hposition' : values (30 : Fin WorkCount) ≤ values 1 + 1 := by
      simpa [Work.position, Work.horizon] using hposition
    have heq : values (30 : Fin WorkCount) = values 1 + 1 := by omega
    simp [afterGap, afterSucc, Work.horizon, Work.position, Work.temporary₃,
      Work.loop₃, heq]

private theorem emitCaseChoice_sound_for_writtenCell (choiceValue : Bool) :
    (emitCaseChoice choiceValue).Sound := by
  cases choiceValue with
  | false =>
      exact (emitCopyGate_sound Work.reference₀ false).seq
        (emitRecentGate_sound .and true true 1 1)
  | true => exact emitCopyGate_sound Work.reference₀ false

private theorem emitCaseRead_sound_for_writtenCell
    (stateCount workCount tapeIndex symbolIndex : ℕ) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.tapeIndex tapeIndex
  · subst routine
    exact BinaryRoutine.set_sound Work.symbolIndex symbolIndex
  · subst routine
    exact emitReadFormula_sound stateCount (workCount + 2)

private theorem emitCaseReads_sound_for_writtenCell
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ) :
    (emitCaseReads stateCount workCount count start symbolAt).Sound := by
  induction count generalizing start symbolAt with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitCaseRead_sound_for_writtenCell stateCount workCount start
        (symbolAt 0)).seq
          (ih (start := start + 1)
            (symbolAt := fun index => symbolAt (index + 1)))

private theorem emitCaseMembers_sound_for_writtenCell
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact emitCaseChoice_sound_for_writtenCell choiceValue
  · subst routine
    exact emitStateReference_sound stateIndex false
  · subst routine
    exact emitCaseRead_sound_for_writtenCell stateCount workCount 0
      inputSymbolIndex
  · subst routine
    exact emitCaseReads_sound_for_writtenCell stateCount workCount workCount 1
      workSymbolIndexAt
  · subst routine
    exact emitCaseRead_sound_for_writtenCell stateCount workCount
      (workCount + 1) outputSymbolIndex

private theorem prepareCaseReadSize_sound_for_writtenCell :
    prepareCaseReadSize.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₃ 5
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₂ 4
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.horizon Work.temporary₂
      Work.temporary₃ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₂

private theorem emitCaseConnector_sound_for_writtenCell :
    emitCaseConnector.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₁

private theorem emitPreviousCaseReadConnector_sound_for_writtenCell :
    emitPreviousCaseReadConnector.Sound :=
  (decrementReferenceBy_sound Work.reference₀ Work.temporary₃
    Work.loop₃).seq emitCaseConnector_sound_for_writtenCell

private theorem emitPreviousCaseChoiceConnector_sound_for_writtenCell :
    emitPreviousCaseChoiceConnector.Sound :=
  (BinaryRoutine.binaryPred_sound Work.reference₀).seq
    emitCaseConnector_sound_for_writtenCell

private theorem emitPreviousCaseReadConnectors_sound_for_writtenCell
    (count : ℕ) : (emitPreviousCaseReadConnectors count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact emitPreviousCaseReadConnector_sound_for_writtenCell.seq ih

private theorem emitCaseFormula_sound_for_writtenCell
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact emitCaseMembers_sound_for_writtenCell stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
  · subst routine
    exact emitConstantGate_sound true
  · subst routine
    exact prepareCaseReadSize_sound_for_writtenCell
  · subst routine
    exact prepareRecentReference_sound Work.reference₀ 2
  · subst routine
    exact emitCaseConnector_sound_for_writtenCell
  · subst routine
    exact emitPreviousCaseReadConnectors_sound_for_writtenCell (workCount + 2)
  · subst routine
    exact emitPreviousCaseChoiceConnector_sound_for_writtenCell
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

private theorem emitEffectCaseAt_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool)
    (caseIndex : Fin (transitionCases tm).length) :
    (emitEffectCaseAt tm selects caseIndex).Sound := by
  rw [emitEffectCaseAt]
  split_ifs
  · exact emitCaseFormula_sound_for_writtenCell (Fintype.card tm.Q) k
      (effectCaseStateIndexAt tm caseIndex)
      (effectCaseInputSymbolIndexAt tm caseIndex)
      (effectCaseOutputSymbolIndexAt tm caseIndex)
      (effectCaseChoiceAt tm caseIndex)
      (effectCaseWorkSymbolIndexAt tm caseIndex)
  · exact emitConstantGate_sound false

private theorem emitEffectMembers_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectMembers tm selects).Sound :=
  emitEffectMembers_sound_internal tm selects

private theorem emitEffectFormula_sound_for_writtenCell (tm : NTM k)
    (selects : TransitionEffect tm → Bool) :
    (emitEffectFormula tm selects).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember
  · subst member
    exact emitEffectMembers_sound_for_writtenCell tm selects
  · subst member
    exact emitConstantGate_sound false
  · subst member
    exact emitEffectConnectors_sound_internal tm selects

theorem emitWrittenCellEffect_sound_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitWrittenCellEffect tm tape symbol).Sound := by
  rw [emitWrittenCellEffect]
  exact emitEffectFormula_sound_for_writtenCell tm _

theorem emitWrittenCellFormula_sound_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ) :
    (emitWrittenCellFormula tm tape symbol).Sound := by
  apply BinaryRoutine.seqList_sound
  intro member hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  rcases hmember with hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember | hmember | hmember |
      hmember | hmember | hmember | hmember | hmember
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tape.toTapeSlot.index.val
  · subst member
    exact BinaryRoutine.set_sound Work.symbolIndex
      (CircuitUnrolling.symbolIndex symbol).val
  · subst member
    exact emitHeadAtCurrentCell_sound_internal (Fintype.card tm.Q)
  · subst member
    exact prepareRecentReference_sound Work.savedOutput 1
  · subst member
    exact BinaryRoutine.binaryCopy_sound Work.position Work.limit₂
      Work.copyCounter
  · subst member
    exact BinaryRoutine.clear_sound Work.position
  · subst member
    exact BinaryRoutine.clear_sound Work.tapeIndex
  · subst member
    exact BinaryRoutine.clear_sound Work.symbolIndex
  · subst member
    exact emitWrittenCellEffect_sound_internal tm tape symbol
  · subst member
    exact BinaryRoutine.binaryCopy_sound Work.limit₂ Work.position
      Work.copyCounter
  · subst member
    exact BinaryRoutine.set_sound Work.tapeIndex tape.toTapeSlot.index.val
  · subst member
    exact BinaryRoutine.set_sound Work.symbolIndex
      (CircuitUnrolling.symbolIndex symbol).val
  · subst member
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst member
    exact BinaryRoutine.emitRawGateStep_sound .and false false Work.emitCounter
      Work.available Work.savedOutput Work.reference₁
  · subst member
    exact BinaryRoutine.clear_sound Work.reference₁
  · subst member
    exact emitHeadAtCurrentCell_sound_internal (Fintype.card tm.Q)
  · subst member
    exact emitRecentGate_sound .and true true 1 1
  · subst member
    exact emitCellReference_sound (Fintype.card tm.Q) (k + 2) false
  · subst member
    exact emitRecentGate_sound .and false false 2 1
  · subst member
    exact emitRecentGate_sound .or false false 5 1
  all_goals
    subst member
    exact BinaryRoutine.clear_sound _

private theorem seqList_append_effect_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).effect values =
      (BinaryRoutine.seqList second).effect
        ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih]

private theorem seqList_append_emitted_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).emitted values =
      (BinaryRoutine.seqList first).emitted values ++
        (BinaryRoutine.seqList second).emitted
          ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih,
        List.append_assoc]

private theorem seqList_append_requires_for_writtenCell
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).requires values ↔
      (BinaryRoutine.seqList first).requires values ∧
        (BinaryRoutine.seqList second).requires
          ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil =>
      simp [BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp [BinaryRoutine.seqList, BinaryRoutine.seq, ih, and_assoc]

private theorem seqList_singleton_effect_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).effect values = routine.effect values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem seqList_singleton_emitted_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).emitted values =
      routine.emitted values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem seqList_singleton_requires_for_writtenCell
    (routine : BinaryRoutine n) (values : BinaryValues n) :
    (BinaryRoutine.seqList [routine]).requires values ↔
      routine.requires values := by
  simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private def emitWrittenCellPrefix (stateCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      emitHeadAtCurrentCell stateCount,
      prepareRecentReference Work.savedOutput 1,
      BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
      BinaryRoutine.clear Work.position,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

private def emitWrittenCellFinish
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    BinaryRoutine WorkCount :=
  BinaryRoutine.seqList
    [BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
      BinaryRoutine.set Work.tapeIndex tapeIndex,
      BinaryRoutine.set Work.symbolIndex symbolIndex,
      prepareRecentReference Work.reference₁ 1,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.savedOutput Work.reference₁,
      BinaryRoutine.clear Work.reference₁,
      emitHeadAtCurrentCell stateCount,
      emitRecentGate .and true true 1 1,
      emitCellReference stateCount tapeCount,
      emitRecentGate .and false false 2 1,
      emitRecentGate .or false false 5 1,
      BinaryRoutine.clear Work.savedOutput,
      BinaryRoutine.clear Work.limit₂,
      BinaryRoutine.clear Work.tapeIndex,
      BinaryRoutine.clear Work.symbolIndex]

private def writtenCellPrefixRoutines
    (stateCount tapeIndex symbolIndex : ℕ) :
    List (BinaryRoutine WorkCount) :=
  [BinaryRoutine.set Work.tapeIndex tapeIndex,
    BinaryRoutine.set Work.symbolIndex symbolIndex,
    emitHeadAtCurrentCell stateCount,
    prepareRecentReference Work.savedOutput 1,
    BinaryRoutine.binaryCopy Work.position Work.limit₂ Work.copyCounter,
    BinaryRoutine.clear Work.position,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private def writtenCellFinishRoutines
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    List (BinaryRoutine WorkCount) :=
  [BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
    BinaryRoutine.set Work.tapeIndex tapeIndex,
    BinaryRoutine.set Work.symbolIndex symbolIndex,
    prepareRecentReference Work.reference₁ 1,
    BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
      Work.available Work.savedOutput Work.reference₁,
    BinaryRoutine.clear Work.reference₁,
    emitHeadAtCurrentCell stateCount,
    emitRecentGate .and true true 1 1,
    emitCellReference stateCount tapeCount,
    emitRecentGate .and false false 2 1,
    emitRecentGate .or false false 5 1,
    BinaryRoutine.clear Work.savedOutput,
    BinaryRoutine.clear Work.limit₂,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private theorem emitWrittenCellPrefix_eq_seqList
    (stateCount tapeIndex symbolIndex : ℕ) :
    emitWrittenCellPrefix stateCount tapeIndex symbolIndex =
      BinaryRoutine.seqList
        (writtenCellPrefixRoutines stateCount tapeIndex symbolIndex) := rfl

private theorem emitWrittenCellFinish_eq_seqList
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex =
      BinaryRoutine.seqList
        (writtenCellFinishRoutines stateCount tapeCount tapeIndex
          symbolIndex) := rfl

private theorem emitWrittenCellFormula_eq_seqList
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ) :
    emitWrittenCellFormula tm tape symbol =
      BinaryRoutine.seqList
        (writtenCellPrefixRoutines (Fintype.card tm.Q)
            tape.toTapeSlot.index.val
            (CircuitUnrolling.symbolIndex symbol).val ++
          ([emitWrittenCellEffect tm tape symbol] ++
            writtenCellFinishRoutines (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val)) := rfl

private theorem emitWrittenCellFormula_requires_iff_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).requires values ↔
      (emitWrittenCellPrefix (Fintype.card tm.Q) tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).requires values ∧
        (emitWrittenCellEffect tm tape symbol).requires
          ((emitWrittenCellPrefix (Fintype.card tm.Q)
            tape.toTapeSlot.index.val
            (CircuitUnrolling.symbolIndex symbol).val).effect values) ∧
        (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).requires
            ((emitWrittenCellEffect tm tape symbol).effect
              ((emitWrittenCellPrefix (Fintype.card tm.Q)
                tape.toTapeSlot.index.val
                (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_requires_for_writtenCell,
    seqList_append_requires_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_requires_for_writtenCell,
    seqList_singleton_effect_for_writtenCell]

private theorem emitWrittenCellFormula_effect_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).effect values =
      (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect
          ((emitWrittenCellEffect tm tape symbol).effect
            ((emitWrittenCellPrefix (Fintype.card tm.Q)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_effect_for_writtenCell,
    seqList_append_effect_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_effect_for_writtenCell]

private theorem emitWrittenCellFormula_emitted_decompose
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) :
    (emitWrittenCellFormula tm tape symbol).emitted values =
      (emitWrittenCellPrefix (Fintype.card tm.Q) tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).emitted values ++
        (emitWrittenCellEffect tm tape symbol).emitted
            ((emitWrittenCellPrefix (Fintype.card tm.Q)
              tape.toTapeSlot.index.val
              (CircuitUnrolling.symbolIndex symbol).val).effect values) ++
        (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index.val
          (CircuitUnrolling.symbolIndex symbol).val).emitted
            ((emitWrittenCellEffect tm tape symbol).effect
              ((emitWrittenCellPrefix (Fintype.card tm.Q)
                tape.toTapeSlot.index.val
                (CircuitUnrolling.symbolIndex symbol).val).effect values)) := by
  rw [emitWrittenCellFormula_eq_seqList,
    seqList_append_emitted_for_writtenCell,
    seqList_append_emitted_for_writtenCell]
  rw [← emitWrittenCellPrefix_eq_seqList,
    ← emitWrittenCellFinish_eq_seqList]
  rw [seqList_singleton_emitted_for_writtenCell,
    seqList_singleton_effect_for_writtenCell]
  rw [List.append_assoc]

private def writtenCellSelectedValues (values : BinaryValues WorkCount)
    (tapeIndex symbolIndex : ℕ) : BinaryValues WorkCount :=
  Function.update (Function.update values Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex

private theorem writtenCellSelectedValues_eq_effect
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ) :
    writtenCellSelectedValues values tapeIndex symbolIndex =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) := by
  simp [writtenCellSelectedValues, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
    Work.symbolIndex]

private theorem HeadAtCurrentCellClean.writtenCellSelectedValues
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ)
    (hclean : HeadAtCurrentCellClean values) :
    HeadAtCurrentCellClean
      (writtenCellSelectedValues values tapeIndex symbolIndex) := by
  refine
    { loop₃ := ?_
      temporary₃ := ?_
      reference₀ := ?_
      emitCounter := ?_
      copyCounter := ?_
      multiplyCounter := ?_
      addCounter := ?_
      temporary₀ := ?_ }
  · exact hclean.loop₃
  · exact hclean.temporary₃
  · exact hclean.reference₀
  · exact hclean.emitCounter
  · exact hclean.copyCounter
  · exact hclean.multiplyCounter
  · exact hclean.addCounter
  · exact hclean.temporary₀

private def writtenCellEffectStartValues (values : BinaryValues WorkCount) :
    BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available
              (values Work.available + 1)) Work.savedOutput
              (values Work.available)) Work.limit₂ (values Work.position))
          Work.position 0) Work.tapeIndex 0) Work.symbolIndex 0

private theorem emitWrittenCellPrefix_effect
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).effect values =
      writtenCellEffectStartValues values := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected,
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean,
    prepareRecentReference_effect]
  simp [selected, writtenCellSelectedValues, writtenCellEffectStartValues,
    BinaryRoutine.binaryCopy, BinaryRoutine.clear, Work.available,
    Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
    Work.symbolIndex]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> omega

private theorem emitWrittenCellPrefix_emitted
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).emitted values =
      CircuitCode.RawGate.encode
        (headAtCellFormulaGate stateCount (values Work.horizon)
          (values Work.configBase) tapeIndex (values Work.position)) := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  have hpositionSelected :
      selected Work.position ≤ selected Work.horizon + 1 := by
    simpa [selected, writtenCellSelectedValues, Work.tapeIndex,
      Work.symbolIndex, Work.position, Work.horizon] using hposition
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected,
    emitHeadAtCurrentCell_emitted_internal stateCount selected hheadClean
      hpositionSelected,
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean,
    prepareRecentReference_emitted]
  simp [BinaryRoutine.binaryCopy, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst,
    writtenCellSelectedValues, selected, Work.horizon, Work.configBase,
    Work.tapeIndex, Work.symbolIndex, Work.position]

private theorem emitWrittenCellPrefix_requires
    (stateCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellPrefix stateCount tapeIndex symbolIndex).requires
      values := by
  let selected := writtenCellSelectedValues values tapeIndex symbolIndex
  have hselected : selected =
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    writtenCellSelectedValues_eq_effect values tapeIndex symbolIndex
  have hheadClean : HeadAtCurrentCellClean selected :=
    HeadAtCurrentCellClean.writtenCellSelectedValues values tapeIndex symbolIndex
      hclean.headAtCurrentCellClean_internal
  have hpositionSelected :
      selected Work.position ≤ selected Work.horizon + 1 := by
    simpa [selected, writtenCellSelectedValues, Work.tapeIndex,
      Work.symbolIndex, Work.position, Work.horizon] using hposition
  have hhead := emitHeadAtCurrentCell_requires_internal stateCount selected
    hheadClean hpositionSelected
  let afterHead := Function.update selected Work.available
    (selected Work.available + 1)
  have hafterHead :
      (emitHeadAtCurrentCell stateCount).effect selected = afterHead :=
    emitHeadAtCurrentCell_effect_internal stateCount selected hheadClean
  have hprepare :
      (prepareRecentReference Work.savedOutput 1).requires afterHead := by
    apply (prepareRecentReference_requires Work.savedOutput 1 afterHead
      (by decide) (by decide) (by decide)).2
    refine ⟨?_, ?_⟩
    · simpa [afterHead, Work.available, Work.copyCounter] using
        hheadClean.copyCounter
    · simp [afterHead, Work.available]
  let afterPrepare := Function.update afterHead Work.savedOutput
    (afterHead Work.available - 1)
  have hafterPrepare :
      (prepareRecentReference Work.savedOutput 1).effect afterHead =
        afterPrepare := by
    rw [prepareRecentReference_effect]
  have hcopyPosition :
      (BinaryRoutine.binaryCopy Work.position Work.limit₂
        Work.copyCounter).requires afterPrepare := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    simpa [afterPrepare, afterHead, selected, writtenCellSelectedValues,
      Work.savedOutput, Work.available, Work.copyCounter] using
      hheadClean.copyCounter
  simp only [emitWrittenCellPrefix, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [← hselected, hafterHead, hafterPrepare]
  exact ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, hhead, hprepare,
    hcopyPosition, trivial, trivial, trivial, trivial⟩

private theorem writtenCellEffectStartValues_caseClean
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    CaseFormulaClean (writtenCellEffectStartValues values) := by
  let start := writtenCellEffectStartValues values
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
  · simp [writtenCellEffectStartValues, Work.position,
      Work.tapeIndex, Work.symbolIndex]
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.loop₀] using hclean.caseClean.loop₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.limit₀] using hclean.caseClean.limit₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₀] using hclean.caseClean.reference₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.caseClean.reference₁
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.emitCounter] using hclean.caseClean.emitCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.copyCounter] using hclean.caseClean.copyCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.multiplyCounter] using
      hclean.caseClean.multiplyCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.addCounter] using hclean.caseClean.addCounter
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₀] using hclean.caseClean.temporary₀
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₁] using hclean.caseClean.temporary₁
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₂] using hclean.caseClean.temporary₂
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.loop₃] using hclean.caseClean.loop₃
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.temporary₃] using hclean.caseClean.temporary₃
  · simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.polynomialScratch] using
      hclean.caseClean.polynomialScratch
  · simp [writtenCellEffectStartValues, Work.tapeIndex,
      Work.symbolIndex]
  · simp [writtenCellEffectStartValues, Work.symbolIndex]

private theorem CaseFormulaClean.updateAvailable_for_writtenCell
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

theorem emitWrittenCellEffect_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).requires values := by
  simpa [emitWrittenCellEffect] using
    emitEffectFormula_requires_internal tm
      (fun effect => decide ((effect.write tape).toΓ = symbol)) values
      hclean havailable

@[simp] theorem emitWrittenCellEffect_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          writtenCellEffectSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) := by
  simpa [emitWrittenCellEffect, writtenCellEffectSize,
    writtenCellEffectSelectedAt] using
      emitEffectFormula_effect_internal tm
        (fun effect => decide ((effect.write tape).toΓ = symbol)) values
        hclean havailable

@[simp] theorem emitWrittenCellEffect_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellEffect tm tape symbol).emitted values =
      (effectFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm) (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  simpa [emitWrittenCellEffect, writtenCellEffectSelectedAt] using
    emitEffectFormula_emitted_internal tm
      (fun effect => decide ((effect.write tape).toΓ = symbol)) values
      hclean havailable

private theorem writtenCellLeftAnd_effect
    (values : BinaryValues WorkCount)
    (hreference₁ : values Work.reference₁ = 0) :
    (BinaryRoutine.clear Work.reference₁).effect
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).effect
          ((prepareRecentReference Work.reference₁ 1).effect values)) =
      Function.update values Work.available (values Work.available + 1) := by
  rw [prepareRecentReference_effect]
  simp [BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    Work.available, Work.reference₁]
  have hreference₁' : values 8 = 0 := by
    simpa [Work.reference₁] using hreference₁
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem writtenCellLeftAnd_emitted
    (values : BinaryValues WorkCount) :
    (prepareRecentReference Work.reference₁ 1).emitted values ++
        (BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).emitted
          ((prepareRecentReference Work.reference₁ 1).effect values) ++
        (BinaryRoutine.clear Work.reference₁).emitted
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect values)) =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.savedOutput
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  simp [prepareRecentReference_effect, prepareRecentReference_emitted,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear, Work.savedOutput,
    Work.reference₁]

private theorem writtenCellLeftAnd_emitted_append
    (values : BinaryValues WorkCount) (tail : List Bool) :
    (prepareRecentReference Work.reference₁ 1).emitted values ++
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).emitted
          ((prepareRecentReference Work.reference₁ 1).effect values) ++
        ((BinaryRoutine.clear Work.reference₁).emitted
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect values)) ++
          tail)) =
      CircuitCode.RawGate.encode
          { op := .and
            input₀ := values Work.savedOutput
            input₁ := values Work.available - 1
            negated₀ := false
            negated₁ := false } ++ tail := by
  rw [← List.append_assoc, ← List.append_assoc,
    writtenCellLeftAnd_emitted values]

private theorem writtenCellLeftAnd_requires
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    (prepareRecentReference Work.reference₁ 1).requires values ∧
      (BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.savedOutput Work.reference₁).requires
        ((prepareRecentReference Work.reference₁ 1).effect values) ∧
      (BinaryRoutine.clear Work.reference₁).requires
        ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
          Work.available Work.savedOutput Work.reference₁).effect
          ((prepareRecentReference Work.reference₁ 1).effect values)) := by
  have hprepare := (prepareRecentReference_requires Work.reference₁ 1 values
    (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  refine ⟨hprepare, ?_, trivial⟩
  rw [prepareRecentReference_effect]
  change CircuitCode.Machine.RawGateStepDistinct 9 5 26 8 ∧
    Function.update values 8 (values 5 - 1) 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter, Work.reference₁] using hemit

set_option maxHeartbeats 800000 in
private theorem emitWrittenCellFinish_effect
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).effect
        values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.position (values Work.limit₂))
            Work.available (values Work.available + 6)) Work.savedOutput 0)
        Work.limit₂ 0 := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hleft :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.loop₃] using hclean.loop₃
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.temporary₃] using
        hclean.temporary₃
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.reference₀] using
        hclean.reference₀
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.emitCounter] using
        hclean.emitCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.copyCounter] using
        hclean.copyCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.multiplyCounter] using
        hclean.multiplyCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.addCounter] using
        hclean.addCounter
    · simpa [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex, Work.temporary₀] using
        hclean.temporary₀
  have hreference₀Value : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference₁Value : values 8 = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  have htemporary₀Value : values 22 = 0 := by
    simpa [Work.temporary₀] using hclean.temporary₀
  have htemporary₁Value : values 23 = 0 := by
    simpa [Work.temporary₁] using hclean.temporary₁
  have htemporary₂Value : values 24 = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htapeIndexValue : values 29 = 0 := by
    simpa [Work.tapeIndex] using hclean.tapeIndex
  have hsymbolIndexValue : values 31 = 0 := by
    simpa [Work.symbolIndex] using hclean.symbolIndex
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect, hleft,
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean,
    emitRecentGate_effect, emitCellReference_effect, emitRecentGate_effect,
    emitRecentGate_effect]
  simp [BinaryRoutine.clear, afterLeft, selected, restored,
    Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
    Work.savedOutput, Work.limit₂, Work.reference₀, Work.reference₁,
    Work.temporary₀, Work.temporary₁, Work.temporary₂]
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.savedOutput, Work.limit₂, Work.reference₁]

private theorem emitWrittenCellFinish_emitted
    (stateCount tapeCount tapeIndex symbolIndex base effectSize : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hposition : values Work.limit₂ ≤ values Work.horizon + 1)
    (havailable : values Work.available = base + effectSize + 1)
    (hsavedOutput : values Work.savedOutput = base) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).emitted
        values =
      (writtenCellSuffixGates stateCount tapeCount (values Work.horizon)
        (values Work.configBase) base tapeIndex (values Work.limit₂)
        symbolIndex effectSize).flatMap CircuitCode.RawGate.encode := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hleftEffect :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    all_goals
      simp [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex] at *
      first | exact hclean.loop₃ | exact hclean.temporary₃ |
        exact hclean.reference₀ | exact hclean.emitCounter |
        exact hclean.copyCounter | exact hclean.multiplyCounter |
        exact hclean.addCounter | exact hclean.temporary₀
  have hpositionLeft :
      afterLeft Work.position ≤ afterLeft Work.horizon + 1 := by
    simpa [afterLeft, selected, restored, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.horizon] using hposition
  have hheadEffect :
      (emitHeadAtCurrentCell stateCount).effect afterLeft =
        Function.update afterLeft Work.available
          (afterLeft Work.available + 1) :=
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean
  have havailableValue : values 5 = base + effectSize + 1 := by
    simpa [Work.available] using havailable
  have hsavedOutputValue : values 26 = base := by
    simpa [Work.savedOutput] using hsavedOutput
  have hrightInput :
      base + (effectSize + 5) - 2 = base + (effectSize + 3) := by
    omega
  have hfinalInput :
      base + (effectSize + 6) - 5 = base + (effectSize + 1) := by
    omega
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect]
  rw [writtenCellLeftAnd_emitted_append selected, hleftEffect]
  rw [emitHeadAtCurrentCell_emitted_internal stateCount afterLeft hheadClean
    hpositionLeft, hheadEffect]
  simp [writtenCellSuffixGates, writtenCellSuffixGate, indexedGateBlocks,
    writtenCellLeftAndGate, writtenCellNegatedHeadGate,
    writtenCellOldValueGate, writtenCellRightAndGate,
    writtenCellFinalOrGate, emitRecentGate_effect,
    emitCellReference_effect, BinaryRoutine.binaryCopy, BinaryRoutine.set,
    BinaryRoutine.seq, BinaryRoutine.addConst, BinaryRoutine.clear, afterLeft,
    selected, restored, havailableValue, hsavedOutputValue, hrightInput,
    hfinalInput, Work.available,
    Work.position, Work.horizon, Work.configBase, CircuitCode.RawGate.copy,
    Nat.add_assoc,
    Work.tapeIndex, Work.symbolIndex, Work.savedOutput, Work.limit₂,
    Work.reference₀, Work.reference₁, Work.temporary₀, Work.temporary₁,
    Work.temporary₂]

private theorem emitWrittenCellFinish_requires
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values)
    (hposition : values Work.limit₂ ≤ values Work.horizon + 1)
    (havailable : 1 ≤ values Work.available) :
    (emitWrittenCellFinish stateCount tapeCount tapeIndex symbolIndex).requires
      values := by
  let restored := Function.update values Work.position (values Work.limit₂)
  let selected := Function.update
    (Function.update restored Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex
  let afterLeft := Function.update selected Work.available
    (selected Work.available + 1)
  have hrestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).effect values = restored := rfl
  have hselect :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect restored) =
        selected := by
    simp [selected, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
      Work.symbolIndex]
  have hcopyRestore :
      (BinaryRoutine.binaryCopy Work.limit₂ Work.position
        Work.copyCounter).requires values :=
    ⟨by decide, by decide, by decide, hclean.copyCounter⟩
  have hreference₁ : selected Work.reference₁ = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₁] using hclean.reference₁
  have hcopySelected : selected Work.copyCounter = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.copyCounter] using hclean.copyCounter
  have hemitSelected : selected Work.emitCounter = 0 := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.emitCounter] using hclean.emitCounter
  have havailableSelected : 1 ≤ selected Work.available := by
    simpa [selected, restored, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.available] using havailable
  have hleft := writtenCellLeftAnd_requires selected hcopySelected
    havailableSelected hemitSelected
  have hleftEffect :
      (BinaryRoutine.clear Work.reference₁).effect
          ((BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
            Work.available Work.savedOutput Work.reference₁).effect
            ((prepareRecentReference Work.reference₁ 1).effect selected)) =
        afterLeft := by
    rw [writtenCellLeftAnd_effect selected hreference₁]
  have hheadClean : HeadAtCurrentCellClean afterLeft := by
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    all_goals
      simp [afterLeft, selected, restored, Work.available, Work.position,
        Work.tapeIndex, Work.symbolIndex] at *
      first | exact hclean.loop₃ | exact hclean.temporary₃ |
        exact hclean.reference₀ | exact hclean.emitCounter |
        exact hclean.copyCounter | exact hclean.multiplyCounter |
        exact hclean.addCounter | exact hclean.temporary₀
  have hpositionLeft :
      afterLeft Work.position ≤ afterLeft Work.horizon + 1 := by
    simpa [afterLeft, selected, restored, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.horizon] using hposition
  have hhead := emitHeadAtCurrentCell_requires_internal stateCount afterLeft
    hheadClean hpositionLeft
  let afterHead := Function.update afterLeft Work.available
    (afterLeft Work.available + 1)
  have hheadEffect :
      (emitHeadAtCurrentCell stateCount).effect afterLeft = afterHead :=
    emitHeadAtCurrentCell_effect_internal stateCount afterLeft hheadClean
  have hcopy0 : values 10 = 0 := by
    simpa [Work.copyCounter] using hclean.copyCounter
  have hemit0 : values 9 = 0 := by
    simpa [Work.emitCounter] using hclean.emitCounter
  have hnegated :
      (emitRecentGate .and true true 1 1).requires afterHead := by
    apply (emitRecentGate_requires .and true true 1 1 afterHead).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [afterHead, afterLeft, Work.available]
      exact hcopySelected
    · simp [afterHead, afterLeft, selected, restored, Work.available]
    · simp [afterHead, afterLeft, selected, restored, Work.available]
    · simp [afterHead, afterLeft, Work.available]
      exact hemitSelected
  let afterNegated :=
    (emitRecentGate .and true true 1 1).effect afterHead
  have hcell :
      (emitCellReference stateCount tapeCount).requires afterNegated := by
    apply emitCellReference_requires stateCount tapeCount false afterNegated
    all_goals
      simp [afterNegated, emitRecentGate_effect, afterHead, afterLeft,
        selected, restored, Work.available, Work.position, Work.tapeIndex,
        Work.symbolIndex, Work.reference₀, Work.reference₁,
        Work.copyCounter, Work.addCounter, Work.multiplyCounter,
        Work.emitCounter]
      first | exact hclean.copyCounter | exact hclean.addCounter |
        exact hclean.multiplyCounter | exact hclean.emitCounter
  let afterCell := (emitCellReference stateCount tapeCount).effect afterNegated
  have hright :
      (emitRecentGate .and false false 2 1).requires afterCell := by
    apply (emitRecentGate_requires .and false false 2 1 afterCell).2
    simp [afterCell, emitCellReference_effect, afterNegated,
      emitRecentGate_effect, afterHead, afterLeft, selected, restored,
      Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.reference₀, Work.reference₁, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.copyCounter,
      Work.emitCounter, hcopy0, hemit0]
  let afterRight := (emitRecentGate .and false false 2 1).effect afterCell
  have hfinal :
      (emitRecentGate .or false false 5 1).requires afterRight := by
    apply (emitRecentGate_requires .or false false 5 1 afterRight).2
    simp [afterRight, emitRecentGate_effect, afterCell,
      emitCellReference_effect, afterNegated, afterHead, afterLeft, selected,
      restored, Work.available, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Work.copyCounter, Work.emitCounter, hcopy0, hemit0]
  simp only [emitWrittenCellFinish, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [hrestore, hselect, hleftEffect, hheadEffect]
  exact ⟨hcopyRestore, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    hleft.1, hleft.2.1, hleft.2.2, hhead, hnegated, hcell, hright,
    hfinal, trivial, trivial, trivial, trivial, trivial⟩

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).requires values := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefix := emitWrittenCellPrefix_requires (Fintype.card tm.Q)
    tapeIndex symbolIndex values hclean hposition
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectRequires :
      (emitWrittenCellEffect tm tape symbol).requires start :=
    emitWrittenCellEffect_requires_internal tm tape symbol start hstartClean
      hstartAvailable
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simp [afterEffect, effectSize, start, writtenCellEffectStartValues, Work.available,
      Work.horizon]
    exact emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hfinishPosition :
      afterEffect Work.limit₂ ≤ afterEffect Work.horizon + 1 := by
    simpa [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon] using hposition
  have hfinishAvailable : 1 ≤ afterEffect Work.available := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
    omega
  have hfinish := emitWrittenCellFinish_requires (Fintype.card tm.Q)
    (k + 2) tapeIndex symbolIndex afterEffect hafterEffectClean
      hfinishPosition hfinishAvailable
  apply (emitWrittenCellFormula_requires_iff_decompose tm tape symbol
    values).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [tapeIndex, symbolIndex] using hprefix
  · rw [show
      (emitWrittenCellPrefix (Fintype.card tm.Q)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
          simpa [tapeIndex, symbolIndex] using hprefixEffect]
    exact heffectRequires
  · rw [show
      (emitWrittenCellPrefix (Fintype.card tm.Q)
        tape.toTapeSlot.index.val
        (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
          simpa [tapeIndex, symbolIndex] using hprefixEffect]
    rw [heffectEffect]
    simpa [tapeIndex, symbolIndex] using hfinish

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values) :
    (emitWrittenCellFormula tm tape symbol).effect values =
      Function.update values Work.available
        (values Work.available +
          writtenCellScheduleSize (transitionCases tm).length k
            (values Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm)) := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simp [afterEffect, effectSize, start, writtenCellEffectStartValues, Work.available,
      Work.horizon]
    exact emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hsavedOutputValue : values 26 = 0 := by
    simpa [Work.savedOutput] using hclean.savedOutput
  have hlimit₂Value : values 19 = 0 := by
    simpa [Work.limit₂] using hclean.limit₂
  have htapeIndexValue : values 29 = 0 := by
    simpa [Work.position, Work.tapeIndex] using hclean.caseClean.tapeIndex
  have hsymbolIndexValue : values 31 = 0 := by
    simpa [Work.position, Work.symbolIndex] using
      hclean.caseClean.symbolIndex
  rw [emitWrittenCellFormula_effect_decompose]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
        simpa [tapeIndex, symbolIndex] using hprefixEffect]
  rw [heffectEffect]
  rw [emitWrittenCellFinish_effect (Fintype.card tm.Q) (k + 2)
    tape.toTapeSlot.index.val
    (CircuitUnrolling.symbolIndex symbol).val afterEffect hafterEffectClean]
  funext i
  by_cases havailableIndex : i = Work.available
  · subst i
    simp [afterEffect, start, writtenCellEffectStartValues,
      writtenCellScheduleSize, effectSize, Work.available, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.savedOutput, Work.limit₂]
    omega
  · by_cases hsavedOutputIndex : i = Work.savedOutput
    · subst i
      simpa [afterEffect, start, writtenCellEffectStartValues,
        Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.savedOutput, Work.limit₂] using hsavedOutputValue.symm
    · by_cases hlimit₂Index : i = Work.limit₂
      · subst i
        simpa [afterEffect, start, writtenCellEffectStartValues,
          Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
          Work.savedOutput, Work.limit₂] using hlimit₂Value.symm
      · by_cases hpositionIndex : i = Work.position
        · subst i
          simp [afterEffect, start, writtenCellEffectStartValues,
            Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
            Work.savedOutput, Work.limit₂]
        · by_cases htapeIndex : i = Work.tapeIndex
          · subst i
            simpa [afterEffect, start, writtenCellEffectStartValues,
              Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
              Work.savedOutput, Work.limit₂] using htapeIndexValue.symm
          · by_cases hsymbolIndex : i = Work.symbolIndex
            · subst i
              simpa [afterEffect, start, writtenCellEffectStartValues,
                Work.available, Work.position, Work.tapeIndex,
                Work.symbolIndex, Work.savedOutput, Work.limit₂] using
                hsymbolIndexValue.symm
            · simp [afterEffect, start, writtenCellEffectStartValues,
                writtenCellScheduleSize, Function.update_apply,
                havailableIndex, hsavedOutputIndex, hlimit₂Index,
                hpositionIndex, htapeIndex, hsymbolIndex]

set_option maxHeartbeats 800000 in
theorem emitWrittenCellFormula_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : BinaryValues WorkCount)
    (hclean : WrittenCellFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitWrittenCellFormula tm tape symbol).emitted values =
      (writtenCellSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) tape.toTapeSlot.index.val
        (values Work.position) (CircuitUnrolling.symbolIndex symbol).val
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm)).flatMap
          CircuitCode.RawGate.encode := by
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let start := writtenCellEffectStartValues values
  let effectSize := writtenCellEffectSize (transitionCases tm).length k
    (values Work.horizon) (writtenCellEffectSelectedAt tm tape symbol)
    (effectCaseChoiceAt tm)
  let afterEffect := Function.update start Work.available
    (start Work.available + effectSize)
  have hprefixEffect :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).effect values = start := by
    simpa [start] using emitWrittenCellPrefix_effect (Fintype.card tm.Q)
      tapeIndex symbolIndex values hclean
  have hprefixEmitted :
      (emitWrittenCellPrefix (Fintype.card tm.Q) tapeIndex
        symbolIndex).emitted values =
        CircuitCode.RawGate.encode
          (headAtCellFormulaGate (Fintype.card tm.Q)
            (values Work.horizon) (values Work.configBase) tapeIndex
            (values Work.position)) :=
    emitWrittenCellPrefix_emitted (Fintype.card tm.Q) tapeIndex symbolIndex
      values hclean hposition
  have hstartClean : CaseFormulaClean start := by
    simpa [start] using writtenCellEffectStartValues_caseClean values hclean
  have hstartAvailable : 1 ≤ start Work.available := by
    simp [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have heffectEffect :
      (emitWrittenCellEffect tm tape symbol).effect start = afterEffect := by
    simp [afterEffect, effectSize, start, writtenCellEffectStartValues, Work.available,
      Work.horizon]
    exact emitWrittenCellEffect_effect_internal tm tape symbol start hstartClean hstartAvailable
  have heffectEmitted :
      (emitWrittenCellEffect tm tape symbol).emitted start =
        (effectFormulaSchedule (transitionCases tm).length
          (Fintype.card tm.Q) k (values Work.horizon)
          (values Work.configBase) (values Work.reference₀)
          (values Work.available + 1)
          (writtenCellEffectSelectedAt tm tape symbol)
          (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
          (effectCaseInputSymbolIndexAt tm)
          (effectCaseOutputSymbolIndexAt tm)
          (effectCaseWorkSymbolIndexAt tm)).flatMap
            CircuitCode.RawGate.encode := by
    simpa [start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon, Work.configBase, Work.reference₀] using
        emitWrittenCellEffect_emitted_internal tm tape symbol start hstartClean
          hstartAvailable
  have hafterEffectClean : CaseFormulaClean afterEffect :=
    CaseFormulaClean.updateAvailable_for_writtenCell start hstartClean _
  have hfinishPosition :
      afterEffect Work.limit₂ ≤ afterEffect Work.horizon + 1 := by
    simpa [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex, Work.horizon] using hposition
  have hfinishAvailable :
      afterEffect Work.available = values Work.available + effectSize + 1 := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
    omega
  have hfinishSaved : afterEffect Work.savedOutput = values Work.available := by
    simp [afterEffect, start, writtenCellEffectStartValues, Work.available,
      Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have hfinishEmitted := emitWrittenCellFinish_emitted
    (Fintype.card tm.Q) (k + 2) tapeIndex symbolIndex
    (values Work.available) effectSize afterEffect hafterEffectClean
    hfinishPosition hfinishAvailable hfinishSaved
  rw [emitWrittenCellFormula_emitted_decompose]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).effect values = start by
        simpa [tapeIndex, symbolIndex] using hprefixEffect]
  rw [heffectEffect]
  rw [show
    (emitWrittenCellPrefix (Fintype.card tm.Q)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).emitted values =
        CircuitCode.RawGate.encode
          (headAtCellFormulaGate (Fintype.card tm.Q)
            (values Work.horizon) (values Work.configBase)
            tape.toTapeSlot.index.val (values Work.position)) by
        simpa [tapeIndex, symbolIndex] using hprefixEmitted]
  rw [heffectEmitted]
  rw [show
    (emitWrittenCellFinish (Fintype.card tm.Q) (k + 2)
      tape.toTapeSlot.index.val
      (CircuitUnrolling.symbolIndex symbol).val).emitted afterEffect =
        (writtenCellSuffixGates (Fintype.card tm.Q) (k + 2)
          (afterEffect Work.horizon) (afterEffect Work.configBase)
          (values Work.available) tape.toTapeSlot.index.val
          (afterEffect Work.limit₂)
          (CircuitUnrolling.symbolIndex symbol).val effectSize).flatMap
            CircuitCode.RawGate.encode by
        simpa [tapeIndex, symbolIndex] using hfinishEmitted]
  simp [writtenCellSchedule, afterEffect, start,
    writtenCellEffectStartValues, effectSize, Work.available,
    Work.savedOutput, Work.limit₂, Work.position, Work.tapeIndex,
    Work.symbolIndex, Work.horizon, Work.configBase, List.append_assoc]

/-! ## Pointwise all-prefix width certificates -/

/-- One global arithmetic envelope covering the nested selected-write effect
and both fixed written-cell wrapper phases. -/
private def WrittenCellFormulaWidthCap (tm : NTM k)
    (tape : WritableSlot k) (symbol : Γ)
    (values : ℕ → BinaryValues WorkCount) (width : ℕ → ℕ) : Prop :=
  ∀ inputLength stateIndex tapeIndex symbolIndex position,
    stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
    symbolIndex < 4 →
    position ≤ values inputLength Work.horizon + 1 →
      values inputLength Work.available +
          writtenCellScheduleSize (transitionCases tm).length k
            (values inputLength Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm) +
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

private theorem WrittenCellFormulaWidthCap.frontier
    {tm : NTM k} {tape : WritableSlot k} {symbol : Γ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hcap : WrittenCellFormulaWidthCap tm tape symbol values width) :
    ∀ inputLength,
      values inputLength Work.available +
          writtenCellScheduleSize (transitionCases tm).length k
            (values inputLength Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm) ≤ width inputLength := by
  intro inputLength
  have hstate : stateIndex tm tm.qstart < Fintype.card tm.Q :=
    (Fintype.equivFin tm.Q tm.qstart).isLt
  have hbound := hcap inputLength (stateIndex tm tm.qstart) 0 0 0
    hstate (by omega) (by omega) (Nat.zero_le _)
  omega

private theorem emitHeadAtCurrentCell_spaceBoundByWidthAt
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      HeadAtCurrentCellClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitHeadAtCurrentCell stateCount)
      initialSpace values width := by
  let copy := BinaryRoutine.binaryCopy Work.horizon Work.temporary₃
    Work.copyCounter
  let afterCopy : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (values inputLength)
  let succ := BinaryRoutine.addConst Work.temporary₃ 1
  let afterSucc : ℕ → BinaryValues WorkCount := fun inputLength =>
    succ.effect (afterCopy inputLength)
  let gap := decrementReferenceBy Work.temporary₃ Work.position Work.loop₃
  let afterGap : ℕ → BinaryValues WorkCount := fun inputLength =>
    gap.effect (afterSucc inputLength)
  let gate := emitHeadAtCurrentCellGate stateCount
  let afterGate : ℕ → BinaryValues WorkCount := fun inputLength =>
    gate.effect (afterGap inputLength)
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.horizon
      Work.temporary₃ Work.copyCounter
    · exact fun inputLength => hvalues inputLength Work.horizon
    · exact fun inputLength => hvalues inputLength Work.temporary₃
  have hafterCopyValues : ∀ inputLength index,
      afterCopy inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.temporary₃
      (hvalues inputLength)
    exact hvalues inputLength Work.horizon
  have hsucc : BinaryRoutine.SpaceBoundByWidthAt succ initialSpace afterCopy
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst Work.temporary₃ 1
    intro inputLength
    simpa [succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      Work.temporary₃, Work.horizon] using hhorizon inputLength
  have hafterSuccValues : ∀ inputLength index,
      afterSucc inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.temporary₃
      (hafterCopyValues inputLength)
    simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.temporary₃, Work.horizon] using
      hhorizon inputLength
  have hdistinct : DecrementReferenceDistinct Work.temporary₃ Work.position
      Work.loop₃ :=
    { reference_ne_offset := by decide
      reference_ne_counter := by decide
      offset_ne_counter := by decide }
  have hloopSucc : ∀ inputLength,
      afterSucc inputLength Work.loop₃ = 0 := by
    intro inputLength
    simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.temporary₃, Work.loop₃,
      Work.horizon] using (hclean inputLength).loop₃
  have hgap : BinaryRoutine.SpaceBoundByWidthAt gap initialSpace afterSucc
      width := by
    apply decrementReferenceBy_spaceBoundByWidth Work.temporary₃
      Work.position Work.loop₃ hdistinct
    · intro inputLength
      rw [hloopSucc inputLength]
      exact Nat.zero_le _
    · intro inputLength
      rw [hloopSucc inputLength, Nat.sub_zero]
      simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
        BinaryRoutine.addConst, Work.temporary₃, Work.position,
        Work.horizon] using hposition inputLength
    · exact fun inputLength =>
        hafterSuccValues inputLength Work.temporary₃
    · exact fun inputLength => hafterSuccValues inputLength Work.position
  have hgapEffect : ∀ inputLength,
      afterGap inputLength =
        Function.update
          (Function.update (afterSucc inputLength) Work.temporary₃
            (afterSucc inputLength Work.temporary₃ -
              afterSucc inputLength Work.position)) Work.loop₃ 0 := by
    intro inputLength
    exact decrementReferenceBy_effect Work.temporary₃ Work.position
      Work.loop₃ (afterSucc inputLength) hdistinct
        (hloopSucc inputLength)
  have hafterGapValues : ∀ inputLength index,
      afterGap inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hgapEffect inputLength]
    apply BinaryRoutine.values_update_le Work.loop₃
    · apply BinaryRoutine.values_update_le Work.temporary₃
        (hafterSuccValues inputLength)
      exact le_trans (Nat.sub_le _ _) (hafterSuccValues inputLength _)
    · exact Nat.zero_le _
  have hconstant : BinaryRoutine.SpaceBoundByWidthAt (emitConstantGate false)
      initialSpace afterGap width :=
    emitConstantGate_spaceBoundByWidth false
      (fun inputLength => hafterGapValues inputLength Work.available)
      (fun inputLength => hafterGapValues inputLength Work.reference₀)
  have hhead : BinaryRoutine.SpaceBoundByWidthAt
      (emitHeadReference stateCount) initialSpace afterGap width := by
    apply emitHeadReference_spaceBoundByWidth stateCount false hafterGapValues
    intro inputLength
    rw [hgapEffect inputLength]
    simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.temporary₃, Work.position, Work.loop₃,
      Work.horizon, Work.configBase, Work.tapeIndex] using
      hheadCap inputLength
  have hgate : BinaryRoutine.SpaceBoundByWidthAt gate initialSpace afterGap
      width := by
    simpa [gate, emitHeadAtCurrentCellGate] using
      (BinaryRoutine.SpaceBoundByWidthAt.branchZero Work.temporary₃
        hconstant hhead)
  have htemporaryGap : ∀ inputLength,
      afterGap inputLength Work.temporary₀ = 0 := by
    intro inputLength
    rw [hgapEffect inputLength]
    simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.temporary₃, Work.position, Work.loop₃,
      Work.temporary₀, Work.horizon] using
      (hclean inputLength).temporary₀
  have hreferenceGap : ∀ inputLength,
      afterGap inputLength Work.reference₀ = 0 := by
    intro inputLength
    rw [hgapEffect inputLength]
    simpa [afterSucc, succ, afterCopy, copy, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, Work.temporary₃, Work.position, Work.loop₃,
      Work.reference₀, Work.horizon] using (hclean inputLength).reference₀
  have hgateEffect : ∀ inputLength,
      afterGate inputLength =
        Function.update (afterGap inputLength) Work.available
          (afterGap inputLength Work.available + 1) := by
    intro inputLength
    exact emitHeadAtCurrentCellGate_effect_internal stateCount
      (afterGap inputLength) (htemporaryGap inputLength)
        (hreferenceGap inputLength)
  have hafterGateValues : ∀ inputLength index,
      afterGate inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hgateEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hafterGapValues inputLength)
    simpa [hgapEffect inputLength, afterSucc, succ, afterCopy, copy,
      BinaryRoutine.binaryCopy, BinaryRoutine.addConst, Work.temporary₃,
      Work.position, Work.loop₃, Work.available, Work.horizon] using
      hfrontier inputLength
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace afterGate width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      (fun inputLength => hafterGateValues inputLength Work.temporary₃)
  rw [emitHeadAtCurrentCell]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hcopy, hsucc, hgap, hgate, hclear, trivial⟩

private theorem writtenCellPrefixRoutines_spaceBoundByWidthAt
    (stateCount tapeIndex symbolIndex : ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      WrittenCellFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (htapeIndex : ∀ inputLength, tapeIndex ≤ width inputLength)
    (hsymbolIndex : ∀ inputLength, symbolIndex ≤ width inputLength)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase) tapeIndex
          (values inputLength Work.position) + tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellPrefixRoutines stateCount tapeIndex symbolIndex)
      initialSpace values width := by
  let setTape := BinaryRoutine.set Work.tapeIndex tapeIndex
  let afterTape : ℕ → BinaryValues WorkCount := fun inputLength =>
    setTape.effect (values inputLength)
  let setSymbol := BinaryRoutine.set Work.symbolIndex symbolIndex
  let selected : ℕ → BinaryValues WorkCount := fun inputLength =>
    setSymbol.effect (afterTape inputLength)
  let head := emitHeadAtCurrentCell stateCount
  let afterHead : ℕ → BinaryValues WorkCount := fun inputLength =>
    head.effect (selected inputLength)
  let prepare := prepareRecentReference Work.savedOutput 1
  let afterPrepare : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (afterHead inputLength)
  let copy := BinaryRoutine.binaryCopy Work.position Work.limit₂
    Work.copyCounter
  let afterCopy : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (afterPrepare inputLength)
  let clearPosition := BinaryRoutine.clear Work.position
  let afterPosition : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearPosition.effect (afterCopy inputLength)
  let clearTape := BinaryRoutine.clear Work.tapeIndex
  let afterTapeClear : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearTape.effect (afterPosition inputLength)
  have hsetTape : BinaryRoutine.SpaceBoundByWidthAt setTape initialSpace
      values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.tapeIndex tapeIndex
    · exact fun inputLength => hvalues inputLength Work.tapeIndex
    · exact htapeIndex
  have hafterTapeValues : ∀ inputLength index,
      afterTape inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [afterTape, setTape, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst] using
      (BinaryRoutine.values_update_le Work.tapeIndex
        (hvalues inputLength) (htapeIndex inputLength))
  have hsetSymbol : BinaryRoutine.SpaceBoundByWidthAt setSymbol initialSpace
      afterTape width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.symbolIndex symbolIndex
    · exact fun inputLength => hafterTapeValues inputLength Work.symbolIndex
    · exact hsymbolIndex
  have hselectedValues : ∀ inputLength index,
      selected inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [selected, setSymbol, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst] using
      (BinaryRoutine.values_update_le Work.symbolIndex
        (hafterTapeValues inputLength) (hsymbolIndex inputLength))
  have hselected : ∀ inputLength,
      selected inputLength =
        writtenCellSelectedValues (values inputLength) tapeIndex
          symbolIndex := by
    intro inputLength
    symm
    exact writtenCellSelectedValues_eq_effect (values inputLength) tapeIndex
      symbolIndex
  have hheadClean : ∀ inputLength,
      HeadAtCurrentCellClean (selected inputLength) := by
    intro inputLength
    rw [hselected inputLength]
    exact HeadAtCurrentCellClean.writtenCellSelectedValues
      (values inputLength) tapeIndex symbolIndex
      (hclean inputLength).headAtCurrentCellClean_internal
  have hheadSpace : BinaryRoutine.SpaceBoundByWidthAt head initialSpace
      selected width := by
    apply emitHeadAtCurrentCell_spaceBoundByWidthAt stateCount hheadClean
      hselectedValues
    · intro inputLength
      rw [hselected inputLength]
      simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex,
        Work.position, Work.horizon] using hposition inputLength
    · intro inputLength
      rw [hselected inputLength]
      simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex,
        Work.horizon] using hhorizon inputLength
    · intro inputLength
      rw [hselected inputLength]
      simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex,
        Work.available] using hfrontier inputLength
    · intro inputLength
      rw [hselected inputLength]
      simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex,
        Work.horizon, Work.configBase, Work.position] using
        hheadCap inputLength
  have hheadEffect : ∀ inputLength,
      afterHead inputLength =
        Function.update (selected inputLength) Work.available
          (selected inputLength Work.available + 1) := by
    intro inputLength
    exact emitHeadAtCurrentCell_effect_internal stateCount
      (selected inputLength) (hheadClean inputLength)
  have hafterHeadValues : ∀ inputLength index,
      afterHead inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hheadEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hselectedValues inputLength)
    rw [hselected inputLength]
    simpa [writtenCellSelectedValues, Work.tapeIndex, Work.symbolIndex,
      Work.available] using hfrontier inputLength
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      afterHead width := by
    apply prepareRecentReference_spaceBoundByWidth Work.savedOutput 1
    · exact fun inputLength => hafterHeadValues inputLength Work.available
    · exact fun inputLength => hafterHeadValues inputLength Work.savedOutput
    · intro inputLength
      rw [hheadEffect inputLength]
      simp [Work.available]
  have hafterPrepareValues : ∀ inputLength index,
      afterPrepare inputLength index ≤ width inputLength := by
    intro inputLength
    rw [show afterPrepare inputLength =
        Function.update (afterHead inputLength) Work.savedOutput
          (afterHead inputLength Work.available - 1) by
      exact prepareRecentReference_effect Work.savedOutput 1
        (afterHead inputLength)]
    apply BinaryRoutine.values_update_le Work.savedOutput
      (hafterHeadValues inputLength)
    exact le_trans (Nat.sub_le _ _) (hafterHeadValues inputLength _)
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace
      afterPrepare width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.position Work.limit₂
      Work.copyCounter
    · exact fun inputLength => hafterPrepareValues inputLength Work.position
    · exact fun inputLength => hafterPrepareValues inputLength Work.limit₂
  have hafterCopyValues : ∀ inputLength index,
      afterCopy inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.limit₂
      (hafterPrepareValues inputLength)
    exact hafterPrepareValues inputLength Work.position
  have hclearPosition : BinaryRoutine.SpaceBoundByWidthAt clearPosition
      initialSpace afterCopy width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.position
      (fun inputLength => hafterCopyValues inputLength Work.position)
  have hafterPositionValues : ∀ inputLength index,
      afterPosition inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.position
      (hafterCopyValues inputLength)
    exact Nat.zero_le _
  have hclearTape : BinaryRoutine.SpaceBoundByWidthAt clearTape initialSpace
      afterPosition width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.tapeIndex
      (fun inputLength => hafterPositionValues inputLength Work.tapeIndex)
  have hafterTapeClearValues : ∀ inputLength index,
      afterTapeClear inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.tapeIndex
      (hafterPositionValues inputLength)
    exact Nat.zero_le _
  have hclearSymbol : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.symbolIndex) initialSpace afterTapeClear
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.symbolIndex
      (fun inputLength => hafterTapeClearValues inputLength Work.symbolIndex)
  simp only [writtenCellPrefixRoutines,
    BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hsetTape, hsetSymbol, hheadSpace, hprepare, hcopy,
    hclearPosition, hclearTape, hclearSymbol, trivial⟩

private def writtenCellFinishLeftRoutines
    (tapeIndex symbolIndex : ℕ) : List (BinaryRoutine WorkCount) :=
  [BinaryRoutine.binaryCopy Work.limit₂ Work.position Work.copyCounter,
    BinaryRoutine.set Work.tapeIndex tapeIndex,
    BinaryRoutine.set Work.symbolIndex symbolIndex,
    prepareRecentReference Work.reference₁ 1,
    BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
      Work.available Work.savedOutput Work.reference₁,
    BinaryRoutine.clear Work.reference₁]

private def writtenCellFinishSuffixRoutines
    (stateCount tapeCount : ℕ) : List (BinaryRoutine WorkCount) :=
  [emitHeadAtCurrentCell stateCount,
    emitRecentGate .and true true 1 1,
    emitCellReference stateCount tapeCount,
    emitRecentGate .and false false 2 1,
    emitRecentGate .or false false 5 1,
    BinaryRoutine.clear Work.savedOutput,
    BinaryRoutine.clear Work.limit₂,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private def writtenCellFinishReferenceRoutines
    (stateCount tapeCount : ℕ) : List (BinaryRoutine WorkCount) :=
  [emitHeadAtCurrentCell stateCount,
    emitRecentGate .and true true 1 1,
    emitCellReference stateCount tapeCount]

private def writtenCellFinishConnectorRoutines :
    List (BinaryRoutine WorkCount) :=
  [emitRecentGate .and false false 2 1,
    emitRecentGate .or false false 5 1,
    BinaryRoutine.clear Work.savedOutput,
    BinaryRoutine.clear Work.limit₂,
    BinaryRoutine.clear Work.tapeIndex,
    BinaryRoutine.clear Work.symbolIndex]

private theorem writtenCellFinishSuffixRoutines_eq_append
    (stateCount tapeCount : ℕ) :
    writtenCellFinishSuffixRoutines stateCount tapeCount =
      writtenCellFinishReferenceRoutines stateCount tapeCount ++
        writtenCellFinishConnectorRoutines := rfl

private theorem writtenCellFinishRoutines_eq_append
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    writtenCellFinishRoutines stateCount tapeCount tapeIndex symbolIndex =
      writtenCellFinishLeftRoutines tapeIndex symbolIndex ++
        writtenCellFinishSuffixRoutines stateCount tapeCount := rfl

private theorem writtenCellFinishLeftRoutines_spaceBoundByWidthAt
    (tapeIndex symbolIndex : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (htapeIndex : ∀ inputLength, tapeIndex ≤ width inputLength)
    (hsymbolIndex : ∀ inputLength, symbolIndex ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellFinishLeftRoutines tapeIndex symbolIndex)
      initialSpace values width := by
  let restore := BinaryRoutine.binaryCopy Work.limit₂ Work.position
    Work.copyCounter
  let restored : ℕ → BinaryValues WorkCount := fun inputLength =>
    restore.effect (values inputLength)
  let setTape := BinaryRoutine.set Work.tapeIndex tapeIndex
  let afterTape : ℕ → BinaryValues WorkCount := fun inputLength =>
    setTape.effect (restored inputLength)
  let setSymbol := BinaryRoutine.set Work.symbolIndex symbolIndex
  let selected : ℕ → BinaryValues WorkCount := fun inputLength =>
    setSymbol.effect (afterTape inputLength)
  let prepare := prepareRecentReference Work.reference₁ 1
  let prepared : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (selected inputLength)
  let raw := BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
    Work.available Work.savedOutput Work.reference₁
  let afterRaw : ℕ → BinaryValues WorkCount := fun inputLength =>
    raw.effect (prepared inputLength)
  have hrestore : BinaryRoutine.SpaceBoundByWidthAt restore initialSpace
      values width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.limit₂ Work.position
      Work.copyCounter (fun inputLength => hvalues inputLength Work.limit₂)
      (fun inputLength => hvalues inputLength Work.position)
  have hrestoredValues : ∀ inputLength index,
      restored inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [restored, restore, BinaryRoutine.binaryCopy] using
      (BinaryRoutine.values_update_le Work.position (hvalues inputLength)
        (hvalues inputLength Work.limit₂))
  have hsetTape : BinaryRoutine.SpaceBoundByWidthAt setTape initialSpace
      restored width :=
    BinaryRoutine.SpaceBoundByWidthAt.set Work.tapeIndex tapeIndex
      (fun inputLength => hrestoredValues inputLength Work.tapeIndex)
      htapeIndex
  have hafterTapeValues : ∀ inputLength index,
      afterTape inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [afterTape, setTape, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst] using
      (BinaryRoutine.values_update_le Work.tapeIndex
        (hrestoredValues inputLength) (htapeIndex inputLength))
  have hsetSymbol : BinaryRoutine.SpaceBoundByWidthAt setSymbol initialSpace
      afterTape width :=
    BinaryRoutine.SpaceBoundByWidthAt.set Work.symbolIndex symbolIndex
      (fun inputLength => hafterTapeValues inputLength Work.symbolIndex)
      hsymbolIndex
  have hselectedValues : ∀ inputLength index,
      selected inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [selected, setSymbol, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst] using
      (BinaryRoutine.values_update_le Work.symbolIndex
        (hafterTapeValues inputLength) (hsymbolIndex inputLength))
  have hreference₁ : ∀ inputLength,
      selected inputLength Work.reference₁ = 0 := by
    intro inputLength
    simpa [selected, setSymbol, afterTape, setTape, restored, restore,
      BinaryRoutine.binaryCopy, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.position,
      Work.tapeIndex, Work.symbolIndex, Work.reference₁] using
      (hclean inputLength).reference₁
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      selected width :=
    prepareRecentReference_spaceBoundByWidth Work.reference₁ 1
      (fun inputLength => hselectedValues inputLength Work.available)
      (fun inputLength => hselectedValues inputLength Work.reference₁)
      (by
        intro inputLength
        simpa [selected, setSymbol, afterTape, setTape, restored, restore,
          BinaryRoutine.binaryCopy, BinaryRoutine.set, BinaryRoutine.seq,
          BinaryRoutine.clear, BinaryRoutine.addConst, Work.available,
          Work.position, Work.tapeIndex, Work.symbolIndex] using
          havailable inputLength)
  have hpreparedValues : ∀ inputLength index,
      prepared inputLength index ≤ width inputLength := by
    intro inputLength
    rw [show prepared inputLength =
        Function.update (selected inputLength) Work.reference₁
          (selected inputLength Work.available - 1) by
      exact prepareRecentReference_effect Work.reference₁ 1
        (selected inputLength)]
    exact BinaryRoutine.values_update_le Work.reference₁
      (hselectedValues inputLength)
      (le_trans (Nat.sub_le (selected inputLength Work.available) 1)
        (hselectedValues inputLength Work.available))
  have hraw : BinaryRoutine.SpaceBoundByWidthAt raw initialSpace prepared
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .and false false
      Work.emitCounter Work.available Work.savedOutput Work.reference₁
      (fun inputLength => hpreparedValues inputLength Work.available)
      (fun inputLength => hpreparedValues inputLength Work.savedOutput)
      (fun inputLength => hpreparedValues inputLength Work.reference₁)
  have hafterRawValues : ∀ inputLength index,
      afterRaw inputLength index ≤ width inputLength := by
    intro inputLength
    apply BinaryRoutine.values_update_le Work.available
      (hpreparedValues inputLength)
    have hbound := hfrontier inputLength
    simp [prepared, prepare, selected, setSymbol, afterTape, setTape,
      restored, restore, prepareRecentReference_effect,
      BinaryRoutine.binaryCopy, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.available,
      Work.reference₁, Work.position, Work.tapeIndex, Work.symbolIndex]
      at *
    omega
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₁) initialSpace afterRaw width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₁
      (fun inputLength => hafterRawValues inputLength Work.reference₁)
  simp only [writtenCellFinishLeftRoutines,
    BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hrestore, hsetTape, hsetSymbol, hprepare, hraw, hclear, trivial⟩

private theorem writtenCellFinishReferenceRoutines_spaceBoundByWidthAt
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      HeadAtCurrentCellClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 3 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength)
    (hcellCap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position)
          (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
              (values inputLength Work.horizon + 2) +
            values inputLength Work.position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellFinishReferenceRoutines stateCount tapeCount)
      initialSpace values width := by
  let head := emitHeadAtCurrentCell stateCount
  let afterHead : ℕ → BinaryValues WorkCount := fun inputLength =>
    head.effect (values inputLength)
  let negated := emitRecentGate .and true true 1 1
  let afterNegated : ℕ → BinaryValues WorkCount := fun inputLength =>
    negated.effect (afterHead inputLength)
  let cell := emitCellReference stateCount tapeCount
  have hhead : BinaryRoutine.SpaceBoundByWidthAt head initialSpace values
      width := emitHeadAtCurrentCell_spaceBoundByWidthAt stateCount hclean
        hvalues hposition hhorizon
        (fun inputLength => by
          have := hfrontier inputLength
          omega)
        hheadCap
  have hheadEffect : ∀ inputLength,
      afterHead inputLength =
        Function.update (values inputLength) Work.available
          (values inputLength Work.available + 1) := fun inputLength =>
    emitHeadAtCurrentCell_effect_internal stateCount (values inputLength)
      (hclean inputLength)
  have hafterHeadValues : ∀ inputLength index,
      afterHead inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hheadEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hvalues inputLength)
    have := hfrontier inputLength
    omega
  have hnegated : BinaryRoutine.SpaceBoundByWidthAt negated initialSpace
      afterHead width := by
    apply emitRecentGate_spaceBoundByWidth .and true true 1 1
    · exact fun inputLength => hafterHeadValues inputLength Work.available
    · exact fun inputLength => hafterHeadValues inputLength Work.reference₀
    · exact fun inputLength => hafterHeadValues inputLength Work.reference₁
    all_goals
      intro inputLength
      rw [hheadEffect inputLength]
      simp only [Function.update_self]
      omega
  have hafterNegatedValues : ∀ inputLength index,
      afterNegated inputLength index ≤ width inputLength := by
    intro inputLength
    rw [show afterNegated inputLength =
        Function.update
          (Function.update
            (Function.update (afterHead inputLength) Work.available
              (afterHead inputLength Work.available + 1))
            Work.reference₀ 0) Work.reference₁ 0 by
      exact emitRecentGate_effect .and true true 1 1
        (afterHead inputLength)]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.reference₀
      · apply BinaryRoutine.values_update_le Work.available
          (hafterHeadValues inputLength)
        rw [hheadEffect inputLength]
        have := hfrontier inputLength
        simp only [Function.update_self]
        omega
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hcell : BinaryRoutine.SpaceBoundByWidthAt cell initialSpace
      afterNegated width := by
    apply emitCellReference_spaceBoundByWidth stateCount tapeCount false
      hafterNegatedValues
    intro inputLength
    simpa [afterNegated, negated, emitRecentGate_effect,
      hheadEffect inputLength, Work.available, Work.reference₀,
      Work.reference₁, Work.horizon, Work.configBase, Work.tapeIndex,
      Work.position, Work.symbolIndex] using hcellCap inputLength
  simp only [writtenCellFinishReferenceRoutines,
    BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hhead, hnegated, hcell, trivial⟩

private theorem writtenCellFinishReferenceRoutines_effect
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount) :
    (BinaryRoutine.seqList
      (writtenCellFinishReferenceRoutines stateCount tapeCount)).effect values =
      (emitCellReference stateCount tapeCount).effect
        ((emitRecentGate .and true true 1 1).effect
          ((emitHeadAtCurrentCell stateCount).effect values)) := by
  rw [show writtenCellFinishReferenceRoutines stateCount tapeCount =
      [emitHeadAtCurrentCell stateCount] ++
        ([emitRecentGate .and true true 1 1] ++
          [emitCellReference stateCount tapeCount]) by rfl]
  rw [seqList_append_effect_for_writtenCell]
  rw [seqList_append_effect_for_writtenCell]
  simp only [seqList_singleton_effect_for_writtenCell]

private theorem emitHeadAtCurrentCell_effect_values_le_for_writtenCell
    (stateCount : ℕ) {values : BinaryValues WorkCount} {width : ℕ}
    (hclean : HeadAtCurrentCellClean values)
    (hvalues : ∀ index, values index ≤ width)
    (havailable : values Work.available + 1 ≤ width) :
    ∀ index,
      (emitHeadAtCurrentCell stateCount).effect values index ≤ width := by
  rw [emitHeadAtCurrentCell_effect_internal stateCount values hclean]
  exact BinaryRoutine.values_update_le Work.available hvalues havailable

private theorem emitRecentGate_effect_values_le_for_writtenCell
    (op : AndOrOp) (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    {values : BinaryValues WorkCount} {width : ℕ}
    (hvalues : ∀ index, values index ≤ width)
    (havailable : values Work.available + 1 ≤ width) :
    ∀ index,
      (emitRecentGate op negated₀ negated₁ offset₀ offset₁).effect
          values index ≤ width := by
  rw [emitRecentGate_effect]
  apply BinaryRoutine.values_update_le Work.reference₁
  · apply BinaryRoutine.values_update_le Work.reference₀
    · exact BinaryRoutine.values_update_le Work.available hvalues havailable
    · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem emitCellReference_effect_values_le_for_writtenCell
    (stateCount tapeCount : ℕ) {values : BinaryValues WorkCount} {width : ℕ}
    (hvalues : ∀ index, values index ≤ width)
    (havailable : values Work.available + 1 ≤ width) :
    ∀ index,
      (emitCellReference stateCount tapeCount).effect values index ≤ width := by
  rw [emitCellReference_effect]
  apply BinaryRoutine.values_update_le Work.reference₀
  · apply BinaryRoutine.values_update_le Work.available
    · apply BinaryRoutine.values_update_le Work.temporary₂
      · apply BinaryRoutine.values_update_le Work.temporary₁
        · exact BinaryRoutine.values_update_le Work.temporary₀ hvalues
            (Nat.zero_le _)
        · exact Nat.zero_le _
      · exact Nat.zero_le _
    · exact havailable
  · exact Nat.zero_le _

private theorem writtenCellFinishReferenceRoutines_values_le
    (stateCount tapeCount : ℕ)
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      HeadAtCurrentCellClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 3 ≤ width inputLength) :
    ∀ inputLength index,
      (BinaryRoutine.seqList
        (writtenCellFinishReferenceRoutines stateCount tapeCount)).effect
          (values inputLength) index ≤ width inputLength := by
  intro inputLength index
  have hheadAvailable :
      (emitHeadAtCurrentCell stateCount).effect
          (values inputLength) Work.available =
        values inputLength Work.available + 1 := by
    rw [emitHeadAtCurrentCell_effect_internal stateCount
      (values inputLength) (hclean inputLength)]
    simp only [Function.update_self]
  have hrecentAvailable :
      (emitRecentGate .and true true 1 1).effect
          ((emitHeadAtCurrentCell stateCount).effect (values inputLength))
          Work.available = values inputLength Work.available + 2 := by
    rw [emitRecentGate_effect]
    simp [Work.available, Work.reference₀, Work.reference₁]
    simpa [Work.available] using hheadAvailable
  rw [writtenCellFinishReferenceRoutines_effect]
  apply emitCellReference_effect_values_le_for_writtenCell
  · apply emitRecentGate_effect_values_le_for_writtenCell
    · apply emitHeadAtCurrentCell_effect_values_le_for_writtenCell
        stateCount (hclean inputLength) (hvalues inputLength)
      have := hfrontier inputLength
      omega
    · rw [hheadAvailable]
      have := hfrontier inputLength
      omega
  · rw [hrecentAvailable]
    exact hfrontier inputLength

private theorem writtenCellFinishReferenceRoutines_available
    (stateCount tapeCount : ℕ)
    {values : ℕ → BinaryValues WorkCount}
    (hclean : ∀ inputLength,
      HeadAtCurrentCellClean (values inputLength)) :
    ∀ inputLength,
      (BinaryRoutine.seqList
        (writtenCellFinishReferenceRoutines stateCount tapeCount)).effect
          (values inputLength) Work.available =
        values inputLength Work.available + 3 := by
  intro inputLength
  rw [writtenCellFinishReferenceRoutines_effect]
  rw [emitHeadAtCurrentCell_effect_internal stateCount (values inputLength)
    (hclean inputLength)]
  simp [emitRecentGate_effect, emitCellReference_effect, Work.available,
    Work.reference₀, Work.reference₁, Work.temporary₀,
    Work.temporary₁, Work.temporary₂]

private theorem writtenCellFinishConnectorRoutines_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength,
      4 ≤ values inputLength Work.available)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 2 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      writtenCellFinishConnectorRoutines initialSpace values width := by
  let right := emitRecentGate .and false false 2 1
  let afterRight : ℕ → BinaryValues WorkCount := fun inputLength =>
    right.effect (values inputLength)
  let final := emitRecentGate .or false false 5 1
  let afterFinal : ℕ → BinaryValues WorkCount := fun inputLength =>
    final.effect (afterRight inputLength)
  let clearSaved := BinaryRoutine.clear Work.savedOutput
  let afterSaved : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearSaved.effect (afterFinal inputLength)
  let clearLimit := BinaryRoutine.clear Work.limit₂
  let afterLimit : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearLimit.effect (afterSaved inputLength)
  let clearTape := BinaryRoutine.clear Work.tapeIndex
  let afterTapeClear : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearTape.effect (afterLimit inputLength)
  have hright : BinaryRoutine.SpaceBoundByWidthAt right initialSpace values
      width := by
    apply emitRecentGate_spaceBoundByWidth .and false false 2 1
    · exact fun inputLength => hvalues inputLength Work.available
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · exact fun inputLength => hvalues inputLength Work.reference₁
    · intro inputLength
      exact le_trans (by omega) (havailable inputLength)
    · intro inputLength
      exact le_trans (by omega) (havailable inputLength)
  have hrightEffect : ∀ inputLength,
      afterRight inputLength =
        Function.update
          (Function.update
            (Function.update (values inputLength) Work.available
              (values inputLength Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0 := fun inputLength =>
    emitRecentGate_effect .and false false 2 1 (values inputLength)
  have hafterRightValues : ∀ inputLength index,
      afterRight inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hrightEffect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.reference₀
      · apply BinaryRoutine.values_update_le Work.available
          (hvalues inputLength)
        have := hfrontier inputLength
        omega
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hrightAvailable : ∀ inputLength,
      afterRight inputLength Work.available =
        values inputLength Work.available + 1 := by
    intro inputLength
    rw [hrightEffect inputLength]
    simp [Work.available, Work.reference₀, Work.reference₁]
  have hfinal : BinaryRoutine.SpaceBoundByWidthAt final initialSpace
      afterRight width := by
    apply emitRecentGate_spaceBoundByWidth .or false false 5 1
    · exact fun inputLength => hafterRightValues inputLength Work.available
    · exact fun inputLength => hafterRightValues inputLength Work.reference₀
    · exact fun inputLength => hafterRightValues inputLength Work.reference₁
    · intro inputLength
      rw [hrightAvailable inputLength]
      have := havailable inputLength
      omega
    · intro inputLength
      rw [hrightAvailable inputLength]
      omega
  have hfinalEffect : ∀ inputLength,
      afterFinal inputLength =
        Function.update
          (Function.update
            (Function.update (afterRight inputLength) Work.available
              (afterRight inputLength Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0 := fun inputLength =>
    emitRecentGate_effect .or false false 5 1 (afterRight inputLength)
  have hafterFinalValues : ∀ inputLength index,
      afterFinal inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hfinalEffect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.reference₀
      · apply BinaryRoutine.values_update_le Work.available
          (hafterRightValues inputLength)
        rw [hrightAvailable inputLength]
        exact hfrontier inputLength
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hclearSaved : BinaryRoutine.SpaceBoundByWidthAt clearSaved initialSpace
      afterFinal width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.savedOutput
      (fun inputLength => hafterFinalValues inputLength Work.savedOutput)
  have hafterSavedValues : ∀ inputLength index,
      afterSaved inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [afterSaved, clearSaved, BinaryRoutine.clear] using
      (BinaryRoutine.values_update_le Work.savedOutput
        (hafterFinalValues inputLength) (Nat.zero_le _))
  have hclearLimit : BinaryRoutine.SpaceBoundByWidthAt clearLimit initialSpace
      afterSaved width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₂
      (fun inputLength => hafterSavedValues inputLength Work.limit₂)
  have hafterLimitValues : ∀ inputLength index,
      afterLimit inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [afterLimit, clearLimit, BinaryRoutine.clear] using
      (BinaryRoutine.values_update_le Work.limit₂
        (hafterSavedValues inputLength) (Nat.zero_le _))
  have hclearTape : BinaryRoutine.SpaceBoundByWidthAt clearTape initialSpace
      afterLimit width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.tapeIndex
      (fun inputLength => hafterLimitValues inputLength Work.tapeIndex)
  have hafterTapeClearValues : ∀ inputLength index,
      afterTapeClear inputLength index ≤ width inputLength := by
    intro inputLength
    simpa [afterTapeClear, clearTape, BinaryRoutine.clear] using
      (BinaryRoutine.values_update_le Work.tapeIndex
        (hafterLimitValues inputLength) (Nat.zero_le _))
  have hclearSymbol : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.symbolIndex) initialSpace afterTapeClear
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.symbolIndex
      (fun inputLength => hafterTapeClearValues inputLength Work.symbolIndex)
  simp only [writtenCellFinishConnectorRoutines,
    BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨hright, hfinal, hclearSaved, hclearLimit, hclearTape,
    hclearSymbol, trivial⟩

private theorem writtenCellFinishSuffixRoutines_spaceBoundByWidthAt
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      HeadAtCurrentCellClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (havailable : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 5 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength)
    (hcellCap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position)
          (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
              (values inputLength Work.horizon + 2) +
            values inputLength Work.position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤ width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellFinishSuffixRoutines stateCount tapeCount)
      initialSpace values width := by
  let references := writtenCellFinishReferenceRoutines stateCount tapeCount
  let afterReferences : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList references).effect (values inputLength)
  have href : BinaryRoutine.SeqListSpaceBoundByWidthAt references
      initialSpace values width :=
    writtenCellFinishReferenceRoutines_spaceBoundByWidthAt
      stateCount tapeCount (initialSpace := initialSpace) hclean hvalues
      hposition hhorizon
        (fun inputLength => by
          have := hfrontier inputLength
          omega)
        hheadCap hcellCap
  have hrefValues : ∀ inputLength index,
      afterReferences inputLength index ≤ width inputLength :=
    writtenCellFinishReferenceRoutines_values_le stateCount tapeCount hclean
      hvalues (fun inputLength => by
        have := hfrontier inputLength
        omega)
  have hrefAvailable : ∀ inputLength,
      afterReferences inputLength Work.available =
        values inputLength Work.available + 3 :=
    writtenCellFinishReferenceRoutines_available stateCount tapeCount hclean
  have hconnectors : BinaryRoutine.SeqListSpaceBoundByWidthAt
      writtenCellFinishConnectorRoutines initialSpace afterReferences
      width := by
    apply writtenCellFinishConnectorRoutines_spaceBoundByWidthAt
    · intro inputLength index
      exact hrefValues inputLength index
    · intro inputLength
      have hpositive := havailable inputLength
      rw [show afterReferences inputLength Work.available =
          values inputLength Work.available + 3 by
        exact hrefAvailable inputLength]
      omega
    · intro inputLength
      rw [show afterReferences inputLength Work.available =
          values inputLength Work.available + 3 by
        exact hrefAvailable inputLength]
      exact hfrontier inputLength
  rw [writtenCellFinishSuffixRoutines_eq_append]
  exact BinaryRoutine.SeqListSpaceBoundByWidthAt.append _ _ href
    hconnectors

private theorem writtenCellFinishRoutines_spaceBoundByWidthAt
    (stateCount tapeCount tapeIndex symbolIndex : ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.limit₂ ≤
        values inputLength Work.horizon + 1)
    (havailable : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (htapeIndex : ∀ inputLength, tapeIndex ≤ width inputLength)
    (hsymbolIndex : ∀ inputLength, symbolIndex ≤ width inputLength)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available + 6 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase) tapeIndex
          (values inputLength Work.limit₂) + tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength)
    (hcellCap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (values inputLength Work.horizon)
          (values inputLength Work.configBase) tapeIndex
          (values inputLength Work.limit₂) symbolIndex +
          (tapeIndex * (values inputLength Work.horizon + 2) +
            values inputLength Work.limit₂) +
          (values inputLength Work.horizon + 2) + tapeCount + tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellFinishRoutines stateCount tapeCount tapeIndex symbolIndex)
      initialSpace values width := by
  let left := writtenCellFinishLeftRoutines tapeIndex symbolIndex
  let afterLeft : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList left).effect (values inputLength)
  have hleft : BinaryRoutine.SeqListSpaceBoundByWidthAt left initialSpace
      values width :=
    writtenCellFinishLeftRoutines_spaceBoundByWidthAt tapeIndex
    symbolIndex (initialSpace := initialSpace) hclean hvalues havailable
      htapeIndex hsymbolIndex
      (fun inputLength => by
        have := hfrontier inputLength
        omega)
  have hleftEffect : ∀ inputLength,
      afterLeft inputLength =
        Function.update
          (Function.update
            (Function.update
              (Function.update (values inputLength) Work.position
                (values inputLength Work.limit₂)) Work.tapeIndex tapeIndex)
            Work.symbolIndex symbolIndex) Work.available
          (values inputLength Work.available + 1) := by
    intro inputLength
    let selected :=
      Function.update
        (Function.update
          (Function.update (values inputLength) Work.position
            (values inputLength Work.limit₂)) Work.tapeIndex tapeIndex)
        Work.symbolIndex symbolIndex
    have hreference₁ : selected Work.reference₁ = 0 := by
      simpa [selected, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.reference₁] using (hclean inputLength).reference₁
    have hselected :
        (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
            ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect
              ((BinaryRoutine.binaryCopy Work.limit₂ Work.position
                Work.copyCounter).effect (values inputLength))) =
          selected := by
      simp [selected, BinaryRoutine.binaryCopy, BinaryRoutine.set,
        BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.addConst]
    simp only [afterLeft, left, writtenCellFinishLeftRoutines,
      BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
    simp only [id_eq]
    rw [hselected]
    rw [writtenCellLeftAnd_effect selected hreference₁]
    simp [selected, Work.available, Work.position, Work.tapeIndex,
      Work.symbolIndex]
  have hafterLeftValues : ∀ inputLength index,
      afterLeft inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hleftEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
    · apply BinaryRoutine.values_update_le Work.symbolIndex
      · apply BinaryRoutine.values_update_le Work.tapeIndex
        · apply BinaryRoutine.values_update_le Work.position
            (hvalues inputLength)
          exact hvalues inputLength Work.limit₂
        · exact htapeIndex inputLength
      · exact hsymbolIndex inputLength
    · have := hfrontier inputLength
      omega
  have hafterLeftClean : ∀ inputLength,
      HeadAtCurrentCellClean (afterLeft inputLength) := by
    intro inputLength
    rw [hleftEffect inputLength]
    refine
      { loop₃ := ?_
        temporary₃ := ?_
        reference₀ := ?_
        emitCounter := ?_
        copyCounter := ?_
        multiplyCounter := ?_
        addCounter := ?_
        temporary₀ := ?_ }
    all_goals
      simp [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex]
      first | exact (hclean inputLength).loop₃ |
        exact (hclean inputLength).temporary₃ |
        exact (hclean inputLength).reference₀ |
        exact (hclean inputLength).emitCounter |
        exact (hclean inputLength).copyCounter |
        exact (hclean inputLength).multiplyCounter |
        exact (hclean inputLength).addCounter |
        exact (hclean inputLength).temporary₀
  have hsuffix : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (writtenCellFinishSuffixRoutines stateCount tapeCount)
      initialSpace afterLeft width :=
    writtenCellFinishSuffixRoutines_spaceBoundByWidthAt
    stateCount tapeCount (initialSpace := initialSpace) hafterLeftClean
      hafterLeftValues
    (fun inputLength => by
      rw [hleftEffect inputLength]
      simpa [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex]
        using! hposition inputLength)
    (fun inputLength => by
      rw [hleftEffect inputLength]
      simp [Work.available])
    (fun inputLength => by
      rw [hleftEffect inputLength]
      simpa [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.horizon] using hhorizon inputLength)
    (fun inputLength => by
      rw [hleftEffect inputLength]
      have := hfrontier inputLength
      simp only [Function.update_self]
      omega)
    (fun inputLength => by
      rw [hleftEffect inputLength]
      simpa [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.horizon, Work.configBase] using hheadCap inputLength)
    (fun inputLength => by
      rw [hleftEffect inputLength]
      simpa [Work.available, Work.position, Work.tapeIndex, Work.symbolIndex,
        Work.horizon, Work.configBase] using hcellCap inputLength)
  rw [writtenCellFinishRoutines_eq_append]
  exact BinaryRoutine.SeqListSpaceBoundByWidthAt.append _ _ hleft hsuffix

private theorem writtenCellEffectStartValues_values_le
    {values : BinaryValues WorkCount} {width : ℕ}
    (hvalues : ∀ index, values index ≤ width)
    (havailable : values Work.available + 1 ≤ width) :
    ∀ index, writtenCellEffectStartValues values index ≤ width := by
  unfold writtenCellEffectStartValues
  apply BinaryRoutine.values_update_le Work.symbolIndex
  · apply BinaryRoutine.values_update_le Work.tapeIndex
    · apply BinaryRoutine.values_update_le Work.position
      · apply BinaryRoutine.values_update_le Work.limit₂
        · apply BinaryRoutine.values_update_le Work.savedOutput
          · exact BinaryRoutine.values_update_le Work.available hvalues
              havailable
          · exact hvalues Work.available
        · exact hvalues Work.position
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem emitWrittenCellFormula_spaceBoundByWidth_internal
    (tm : NTM k) (tape : WritableSlot k) (symbol : Γ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength,
      WrittenCellFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position ≤
        values inputLength Work.horizon + 1)
    (hcap : ∀ inputLength stateIndex tapeIndex symbolIndex position,
      stateIndex < Fintype.card tm.Q → tapeIndex ≤ k + 1 →
      symbolIndex < 4 →
      position ≤ values inputLength Work.horizon + 1 →
        values inputLength Work.available +
            writtenCellScheduleSize (transitionCases tm).length k
              (values inputLength Work.horizon)
              (writtenCellEffectSelectedAt tm tape symbol)
              (effectCaseChoiceAt tm) +
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
    BinaryRoutine.SpaceBoundByWidthAt
      (emitWrittenCellFormula tm tape symbol) initialSpace values width := by
  have hwidthCap : WrittenCellFormulaWidthCap tm tape symbol values width :=
    hcap
  let tapeIndex := tape.toTapeSlot.index.val
  let symbolIndex := (CircuitUnrolling.symbolIndex symbol).val
  let prefixRoutines := writtenCellPrefixRoutines (Fintype.card tm.Q) tapeIndex
    symbolIndex
  let afterPrefix : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList prefixRoutines).effect (values inputLength)
  have hstateRange : stateIndex tm tm.qstart < Fintype.card tm.Q :=
    (Fintype.equivFin tm.Q tm.qstart).isLt
  have htapeRange : tapeIndex ≤ k + 1 := by
    have hindex := tape.toTapeSlot.index.isLt
    dsimp only [tapeIndex]
    omega
  have hsymbolRange : symbolIndex < 4 := by
    exact (CircuitUnrolling.symbolIndex symbol).isLt
  let fixedCap := fun inputLength =>
    hwidthCap inputLength (stateIndex tm tm.qstart) tapeIndex symbolIndex
      (values inputLength Work.position) hstateRange htapeRange hsymbolRange
      (hposition inputLength)
  have htapeWidth : ∀ inputLength,
      tapeIndex ≤ width inputLength := by
    intro inputLength
    have hbound := fixedCap inputLength
    omega
  have hsymbolWidth : ∀ inputLength,
      symbolIndex ≤ width inputLength := by
    intro inputLength
    have hbound := fixedCap inputLength
    omega
  have hhorizonWidth : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength := by
    intro inputLength
    have hbound := fixedCap inputLength
    omega
  have hprefixFrontier : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength := by
    intro inputLength
    have hbound := fixedCap inputLength
    omega
  have hprefixHeadCap : ∀ inputLength,
      transitionHeadRef (Fintype.card tm.Q)
          (values inputLength Work.horizon)
          (values inputLength Work.configBase) tapeIndex
          (values inputLength Work.position) + tapeIndex +
          values inputLength Work.horizon + 1 ≤ width inputLength := by
    intro inputLength
    have hbound := fixedCap inputLength
    omega
  have hprefix : BinaryRoutine.SeqListSpaceBoundByWidthAt prefixRoutines
      initialSpace values width :=
    writtenCellPrefixRoutines_spaceBoundByWidthAt
      (Fintype.card tm.Q) tapeIndex symbolIndex
      (initialSpace := initialSpace) hclean hvalues hposition htapeWidth
      hsymbolWidth hhorizonWidth hprefixFrontier hprefixHeadCap
  have hafterPrefixEffect : ∀ inputLength,
      afterPrefix inputLength =
        writtenCellEffectStartValues (values inputLength) := by
    intro inputLength
    dsimp only [afterPrefix, prefixRoutines]
    rw [← emitWrittenCellPrefix_eq_seqList]
    exact emitWrittenCellPrefix_effect (Fintype.card tm.Q) tapeIndex
      symbolIndex (values inputLength) (hclean inputLength)
  have hafterPrefixValues : ∀ inputLength index,
      afterPrefix inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    exact writtenCellEffectStartValues_values_le (hvalues inputLength)
      (hprefixFrontier inputLength)
  have hafterPrefixClean : ∀ inputLength,
      CaseFormulaClean (afterPrefix inputLength) := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    exact writtenCellEffectStartValues_caseClean (values inputLength)
      (hclean inputLength)
  have hafterPrefixAvailable : ∀ inputLength,
      afterPrefix inputLength Work.available =
        values inputLength Work.available + 1 := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    simp [writtenCellEffectStartValues, Work.available, Work.savedOutput,
      Work.limit₂, Work.position, Work.tapeIndex, Work.symbolIndex]
  have hafterPrefixHorizon : ∀ inputLength,
      afterPrefix inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    simp [writtenCellEffectStartValues, Work.available, Work.savedOutput,
      Work.limit₂, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.horizon]
  have hafterPrefixConfigBase : ∀ inputLength,
      afterPrefix inputLength Work.configBase =
        values inputLength Work.configBase := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    simp [writtenCellEffectStartValues, Work.available, Work.savedOutput,
      Work.limit₂, Work.position, Work.tapeIndex, Work.symbolIndex,
      Work.configBase]
  have hafterPrefixLimit₂ : ∀ inputLength,
      afterPrefix inputLength Work.limit₂ =
        values inputLength Work.position := by
    intro inputLength
    rw [hafterPrefixEffect inputLength]
    simp [writtenCellEffectStartValues, Work.available, Work.savedOutput,
      Work.limit₂, Work.position, Work.tapeIndex, Work.symbolIndex]
  let effectRoutine := emitWrittenCellEffect tm tape symbol
  have heffect : BinaryRoutine.SpaceBoundByWidthAt effectRoutine initialSpace
      afterPrefix width := by
    dsimp only [effectRoutine, emitWrittenCellEffect]
    apply emitEffectFormula_spaceBoundByWidth tm
      (fun effect => decide ((effect.write tape).toΓ = symbol))
      hafterPrefixClean hafterPrefixValues
    intro inputLength stateIndex' tapeIndex' symbolIndex' position'
      hstateIndex' htapeIndex' hsymbolIndex' hposition'
    have hpositionOriginal :
        position' ≤ values inputLength Work.horizon + 1 := by
      rw [hafterPrefixHorizon inputLength] at hposition'
      omega
    have hbound := hwidthCap inputLength stateIndex' tapeIndex'
      symbolIndex' position' hstateIndex' htapeIndex' hsymbolIndex'
      hpositionOriginal
    rw [hafterPrefixAvailable inputLength,
      hafterPrefixHorizon inputLength,
      hafterPrefixConfigBase inputLength]
    simp only [writtenCellScheduleSize, writtenCellEffectSize,
      writtenCellEffectSelectedAt] at hbound
    omega
  have heffectList : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [effectRoutine] initialSpace afterPrefix width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    exact ⟨heffect, trivial⟩
  let coreRoutines := prefixRoutines ++ [effectRoutine]
  have hcore : BinaryRoutine.SeqListSpaceBoundByWidthAt coreRoutines
      initialSpace values width := by
    dsimp only [coreRoutines]
    exact BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      prefixRoutines [effectRoutine] hprefix heffectList
  let afterEffect : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList coreRoutines).effect (values inputLength)
  have hafterEffectDecompose : ∀ inputLength,
      afterEffect inputLength =
        effectRoutine.effect (afterPrefix inputLength) := by
    intro inputLength
    dsimp only [afterEffect, coreRoutines]
    rw [seqList_append_effect_for_writtenCell]
    rw [seqList_singleton_effect_for_writtenCell]
  have hafterPrefixPositive : ∀ inputLength,
      1 ≤ afterPrefix inputLength Work.available := by
    intro inputLength
    rw [hafterPrefixAvailable inputLength]
    omega
  have hafterEffectEffect : ∀ inputLength,
      afterEffect inputLength =
        Function.update (afterPrefix inputLength) Work.available
          (afterPrefix inputLength Work.available +
            writtenCellEffectSize (transitionCases tm).length k
              (afterPrefix inputLength Work.horizon)
              (writtenCellEffectSelectedAt tm tape symbol)
              (effectCaseChoiceAt tm)) := by
    intro inputLength
    rw [hafterEffectDecompose inputLength]
    dsimp only [effectRoutine]
    exact emitWrittenCellEffect_effect_internal tm tape symbol
      (afterPrefix inputLength) (hafterPrefixClean inputLength)
      (hafterPrefixPositive inputLength)
  have hafterEffectValues : ∀ inputLength index,
      afterEffect inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
      (hafterPrefixValues inputLength)
    have hfrontier := hwidthCap.frontier inputLength
    rw [hafterPrefixAvailable inputLength,
      hafterPrefixHorizon inputLength]
    simp only [writtenCellScheduleSize] at hfrontier
    omega
  have hafterEffectClean : ∀ inputLength,
      CaseFormulaClean (afterEffect inputLength) := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    exact CaseFormulaClean.updateAvailable_for_writtenCell
      (afterPrefix inputLength) (hafterPrefixClean inputLength) _
  have hafterEffectAvailable : ∀ inputLength,
      afterEffect inputLength Work.available =
        afterPrefix inputLength Work.available +
          writtenCellEffectSize (transitionCases tm).length k
            (afterPrefix inputLength Work.horizon)
            (writtenCellEffectSelectedAt tm tape symbol)
            (effectCaseChoiceAt tm) := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    simp only [Function.update_self]
  have hafterEffectHorizon : ∀ inputLength,
      afterEffect inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    simpa [Work.available, Work.horizon] using
      hafterPrefixHorizon inputLength
  have hafterEffectConfigBase : ∀ inputLength,
      afterEffect inputLength Work.configBase =
        values inputLength Work.configBase := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    simpa [Work.available, Work.configBase] using
      hafterPrefixConfigBase inputLength
  have hafterEffectLimit₂ : ∀ inputLength,
      afterEffect inputLength Work.limit₂ =
        values inputLength Work.position := by
    intro inputLength
    rw [hafterEffectEffect inputLength]
    simpa [Work.available, Work.limit₂] using
      hafterPrefixLimit₂ inputLength
  have hfinishPosition : ∀ inputLength,
      afterEffect inputLength Work.limit₂ ≤
        afterEffect inputLength Work.horizon + 1 := by
    intro inputLength
    rw [hafterEffectLimit₂ inputLength,
      hafterEffectHorizon inputLength]
    exact hposition inputLength
  have hfinishAvailable : ∀ inputLength,
      1 ≤ afterEffect inputLength Work.available := by
    intro inputLength
    rw [hafterEffectAvailable inputLength,
      hafterPrefixAvailable inputLength]
    omega
  have hfinishHorizon : ∀ inputLength,
      afterEffect inputLength Work.horizon + 1 ≤ width inputLength := by
    intro inputLength
    rw [hafterEffectHorizon inputLength]
    exact hhorizonWidth inputLength
  have hfinishFrontier : ∀ inputLength,
      afterEffect inputLength Work.available + 6 ≤ width inputLength := by
    intro inputLength
    rw [hafterEffectAvailable inputLength,
      hafterPrefixAvailable inputLength,
      hafterPrefixHorizon inputLength]
    have hfrontier := hwidthCap.frontier inputLength
    simp only [writtenCellScheduleSize] at hfrontier
    omega
  have hfinishHeadCap : ∀ inputLength,
      transitionHeadRef (Fintype.card tm.Q)
          (afterEffect inputLength Work.horizon)
          (afterEffect inputLength Work.configBase) tapeIndex
          (afterEffect inputLength Work.limit₂) + tapeIndex +
          afterEffect inputLength Work.horizon + 1 ≤ width inputLength := by
    intro inputLength
    rw [hafterEffectHorizon inputLength,
      hafterEffectConfigBase inputLength,
      hafterEffectLimit₂ inputLength]
    have hbound := fixedCap inputLength
    omega
  have hfinishCellCap : ∀ inputLength,
      transitionCellRef (Fintype.card tm.Q) (k + 2)
          (afterEffect inputLength Work.horizon)
          (afterEffect inputLength Work.configBase) tapeIndex
          (afterEffect inputLength Work.limit₂) symbolIndex +
          (tapeIndex * (afterEffect inputLength Work.horizon + 2) +
            afterEffect inputLength Work.limit₂) +
          (afterEffect inputLength Work.horizon + 2) + (k + 2) +
          tapeIndex + 4 ≤ width inputLength := by
    intro inputLength
    rw [hafterEffectHorizon inputLength,
      hafterEffectConfigBase inputLength,
      hafterEffectLimit₂ inputLength]
    have hbound := fixedCap inputLength
    omega
  let finishRoutines := writtenCellFinishRoutines (Fintype.card tm.Q)
    (k + 2) tapeIndex symbolIndex
  have hfinish : BinaryRoutine.SeqListSpaceBoundByWidthAt finishRoutines
      initialSpace afterEffect width :=
    writtenCellFinishRoutines_spaceBoundByWidthAt
      (Fintype.card tm.Q) (k + 2) tapeIndex symbolIndex
      (initialSpace := initialSpace) hafterEffectClean hafterEffectValues
      hfinishPosition hfinishAvailable htapeWidth hsymbolWidth
      hfinishHorizon hfinishFrontier hfinishHeadCap hfinishCellCap
  have htotal : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (coreRoutines ++ finishRoutines) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append coreRoutines
      finishRoutines hcore hfinish
  rw [emitWrittenCellFormula_eq_seqList]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simpa [coreRoutines, finishRoutines, prefixRoutines, effectRoutine,
    tapeIndex, symbolIndex, List.append_assoc] using htotal

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
