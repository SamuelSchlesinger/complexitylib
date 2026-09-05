/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Case.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization

/-!
# Direct-unrolling transition-case generator -- proof internals
-/


@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem emitCaseChoice_sound_internal (choiceValue : Bool) :
    (emitCaseChoice choiceValue).Sound := by
  cases choiceValue with
  | false =>
      exact (emitCopyGate_sound Work.reference₀ false).seq
        (emitRecentGate_sound .and true true 1 1)
  | true => exact emitCopyGate_sound Work.reference₀ false

theorem emitCaseRead_sound_internal
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

private theorem emitCaseReads_sound
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ) :
    (emitCaseReads stateCount workCount count start symbolAt).Sound := by
  induction count generalizing start symbolAt with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact (emitCaseRead_sound_internal stateCount workCount start
        (symbolAt 0)).seq
          (ih (start := start + 1)
            (symbolAt := fun index => symbolAt (index + 1)))

theorem emitCaseMembers_sound_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact emitCaseChoice_sound_internal choiceValue
  · subst routine
    exact emitStateReference_sound stateIndex false
  · subst routine
    exact emitCaseRead_sound_internal stateCount workCount 0 inputSymbolIndex
  · subst routine
    exact emitCaseReads_sound stateCount workCount workCount 1
      workSymbolIndexAt
  · subst routine
    exact emitCaseRead_sound_internal stateCount workCount (workCount + 1)
      outputSymbolIndex

theorem prepareCaseReadSize_sound_internal : prepareCaseReadSize.Sound := by
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

theorem emitCaseConnector_sound_internal : emitCaseConnector.Sound := by
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

theorem emitPreviousCaseReadConnector_sound_internal :
    emitPreviousCaseReadConnector.Sound :=
  (decrementReferenceBy_sound Work.reference₀ Work.temporary₃
    Work.loop₃).seq emitCaseConnector_sound_internal

theorem emitPreviousCaseChoiceConnector_sound_internal :
    emitPreviousCaseChoiceConnector.Sound :=
  (BinaryRoutine.binaryPred_sound Work.reference₀).seq
    emitCaseConnector_sound_internal

private theorem emitPreviousCaseReadConnectors_sound (count : ℕ) :
    (emitPreviousCaseReadConnectors count).Sound := by
  induction count with
  | zero => exact BinaryRoutine.identity_sound
  | succ count ih =>
      exact emitPreviousCaseReadConnector_sound_internal.seq ih

theorem emitCaseFormula_sound_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact emitCaseMembers_sound_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
  · subst routine
    exact emitConstantGate_sound true
  · subst routine
    exact prepareCaseReadSize_sound_internal
  · subst routine
    exact prepareRecentReference_sound Work.reference₀ 2
  · subst routine
    exact emitCaseConnector_sound_internal
  · subst routine
    exact emitPreviousCaseReadConnectors_sound (workCount + 2)
  · subst routine
    exact emitPreviousCaseChoiceConnector_sound_internal
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

private theorem emitCopyGate_reference₀_requires
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    (emitCopyGate Work.reference₀).requires values := by
  change CircuitCode.Machine.RawGateStepDistinct 9 5 7 7 ∧ values 9 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  simpa [Work.emitCounter] using hemit

/-- Register state used to begin reading one transition case. -/
def caseReadStartValues (values : BinaryValues WorkCount)
    (tapeIndex symbolIndex : ℕ) : BinaryValues WorkCount :=
  Function.update
    (Function.update values Work.tapeIndex tapeIndex)
    Work.symbolIndex symbolIndex

private theorem caseReadStartValues_eq_effect
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ) :
    ((BinaryRoutine.set Work.symbolIndex symbolIndex).effect
      ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values)) =
        caseReadStartValues values tapeIndex symbolIndex := by
  simp [caseReadStartValues, BinaryRoutine.set, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
    Work.symbolIndex]

private theorem ReadFormulaClean.caseReadStartValues
    (values : BinaryValues WorkCount) (tapeIndex symbolIndex : ℕ)
    (hclean : ReadFormulaClean values) :
    ReadFormulaClean (caseReadStartValues values tapeIndex symbolIndex) := by
  refine
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

private theorem ReadFormulaClean.updateAvailable
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hclean : ReadFormulaClean values) :
    ReadFormulaClean (Function.update values Work.available amount) := by
  rcases hclean with
    ⟨hposition, hloop, hlimit, hreference₀, hreference₁, hemit,
      hcopy, hmultiply, hadd, htemporary₀, htemporary₁, htemporary₂⟩
  constructor <;>
    simp_all [Work.available, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₀, Work.reference₁, Work.emitCounter,
      Work.copyCounter, Work.multiplyCounter, Work.addCounter,
      Work.temporary₀, Work.temporary₁, Work.temporary₂]

private theorem ReadFormulaClean.updateReference₀Zero
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadFormulaClean (Function.update values Work.reference₀ 0) := by
  rcases hclean with
    ⟨hposition, hloop, hlimit, _hreference₀, hreference₁, hemit,
      hcopy, hmultiply, hadd, htemporary₀, htemporary₁, htemporary₂⟩
  constructor <;>
    simp_all [Work.reference₀, Work.position, Work.loop₀, Work.limit₀,
      Work.reference₁, Work.emitCounter, Work.copyCounter,
      Work.multiplyCounter, Work.addCounter, Work.temporary₀,
      Work.temporary₁, Work.temporary₂]

theorem emitCaseChoice_effect_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount)
    (hreference₀ : values Work.reference₀ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitCaseChoice choiceValue).effect values =
      Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue) := by
  cases choiceValue with
  | true =>
      simpa [emitCaseChoice, caseChoiceLiteralSize] using
        emitCopyGate_effect_internal Work.reference₀ false values
  | false =>
      simp only [emitCaseChoice, Bool.false_eq_true, ↓reduceIte,
        BinaryRoutine.seq]
      rw [emitCopyGate_effect_internal, emitRecentGate_effect]
      funext i
      simp only [Function.update_apply]
      split_ifs <;>
        simp_all [caseChoiceLiteralSize, Work.available, Work.reference₀,
          Work.reference₁]

theorem emitCaseChoice_emitted_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount) :
    (emitCaseChoice choiceValue).emitted values =
      (caseChoiceLiteralSchedule (values Work.available)
        (values Work.reference₀) choiceValue).flatMap
          CircuitCode.RawGate.encode := by
  cases choiceValue with
  | true =>
      simp [emitCaseChoice, caseChoiceLiteralSchedule,
        emitCopyGate_emitted_internal]
  | false =>
      simp only [emitCaseChoice, Bool.false_eq_true, ↓reduceIte,
        BinaryRoutine.seq]
      rw [emitCopyGate_emitted_internal, emitCopyGate_effect_internal,
        emitRecentGate_emitted]
      simp [caseChoiceLiteralSchedule, CircuitCode.RawGate.copy,
        Work.available, Work.reference₀]

theorem emitCaseChoice_requires_internal (choiceValue : Bool)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitCaseChoice choiceValue).requires values := by
  cases choiceValue with
  | true => exact emitCopyGate_reference₀_requires values hemit
  | false =>
      rw [emitCaseChoice, BinaryRoutine.seq]
      refine ⟨emitCopyGate_reference₀_requires values hemit, ?_⟩
      rw [emitCopyGate_effect_internal]
      apply (emitRecentGate_requires .and true true 1 1 _).2
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Work.available, Work.copyCounter] using hcopy
      · simp [Work.available]
      · simp [Work.available]
      · have hemit' : values 9 = 0 := by
          simpa [Work.emitCounter] using hemit
        simp [Work.available, Work.emitCounter, hemit']

theorem emitCaseRead_effect_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).effect values =
      Function.update (caseReadStartValues values tapeIndex symbolIndex)
        Work.available
        (values Work.available + caseReadSize (values Work.horizon)) := by
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseReadStartValues_eq_effect]
  rw [emitReadFormula_effect stateCount (workCount + 2) _
    (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)]
  simp [caseReadStartValues, caseReadSize, Work.available, Work.horizon,
    Work.tapeIndex, Work.symbolIndex]

theorem emitCaseRead_emitted_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).emitted values =
      (readFormulaSchedule stateCount (workCount + 2)
        (values Work.horizon) (values Work.configBase)
        (values Work.available) tapeIndex symbolIndex).flatMap
          CircuitCode.RawGate.encode := by
  have htape :
      (BinaryRoutine.set Work.tapeIndex tapeIndex).emitted values = [] := by
    rfl
  have hsymbol :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).emitted
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) = [] := by
    rfl
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [htape, hsymbol]
  simp only [List.nil_append, List.append_nil]
  rw [caseReadStartValues_eq_effect]
  rw [emitReadFormula_emitted stateCount (workCount + 2) _
    (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)]
  simp [caseReadStartValues, Work.horizon, Work.configBase, Work.available,
    Work.tapeIndex, Work.symbolIndex]

theorem emitCaseRead_requires_internal
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitCaseRead stateCount workCount tapeIndex symbolIndex).requires
      values := by
  have htape :
      (BinaryRoutine.set Work.tapeIndex tapeIndex).requires values :=
    ⟨trivial, trivial⟩
  have hsymbol :
      (BinaryRoutine.set Work.symbolIndex symbolIndex).requires
        ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect values) :=
    ⟨trivial, trivial⟩
  have hread :
      (emitReadFormula stateCount (workCount + 2)).requires
        (caseReadStartValues values tapeIndex symbolIndex) :=
    emitReadFormula_requires stateCount (workCount + 2) _
      (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)
  simp only [emitCaseRead, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseReadStartValues_eq_effect]
  exact ⟨htape, hsymbol, hread, trivial⟩

theorem prepareCaseReadSize_effect_internal
    (values : BinaryValues WorkCount) :
    prepareCaseReadSize.effect values =
      Function.update
        (Function.update values Work.temporary₃
          (caseReadSize (values Work.horizon))) Work.temporary₂ 0 := by
  simp [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits,
    caseReadSize, Work.horizon, Work.temporary₂, Work.temporary₃,
    Work.multiplyCounter, Work.addCounter]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> omega

theorem prepareCaseReadSize_emitted_internal
    (values : BinaryValues WorkCount) :
    prepareCaseReadSize.emitted values = [] := by
  simp [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.mulAdd, BinaryRoutine.identity, BinaryRoutine.emitBits]

theorem prepareCaseReadSize_requires_internal
    (values : BinaryValues WorkCount)
    (hmultiply : values Work.multiplyCounter = 0)
    (hadd : values Work.addCounter = 0) :
    prepareCaseReadSize.requires values := by
  simp only [prepareCaseReadSize, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ?_, trivial,
    trivial⟩
  change TM.BinaryMulAddDistinct 1 24 25 12 13 ∧
    (Function.update
        (Function.update
          ((BinaryRoutine.set Work.temporary₃ 5).effect values)
          Work.temporary₂ 0) Work.temporary₂ 4) 12 = 0 ∧
    (Function.update
        (Function.update
          ((BinaryRoutine.set Work.temporary₃ 5).effect values)
          Work.temporary₂ 0) Work.temporary₂ 4) 13 = 0
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩, ?_, ?_⟩
  · simp [Work.temporary₂]
    exact hmultiply
  · simp [Work.temporary₂]
    exact hadd

theorem emitCaseConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitCaseConnector.effect values =
      Function.update
        (Function.update values Work.available (values Work.available + 1))
        Work.reference₁ 0 := by
  simp [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₁]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem emitCaseConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitCaseConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  simp [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, prepareRecentReference_emitted,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.available,
    Work.reference₀, Work.reference₁]

theorem emitCaseConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitCaseConnector.requires values := by
  have hprepare := (prepareRecentReference_requires Work.reference₁ 1 values
    (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
      Work.available Work.reference₀ Work.reference₁ := by
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  simp only [emitCaseConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨hprepare, ⟨hdistinct, ?_⟩, trivial, trivial⟩
  rw [prepareRecentReference_effect]
  simpa [Work.reference₁, Work.emitCounter] using hemit

theorem emitPreviousCaseReadConnector_effect_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    emitPreviousCaseReadConnector.effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0 := by
  change emitCaseConnector.effect
      ((decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).effect values) = _
  rw [decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
      values ⟨by decide, by decide, by decide⟩ hloop,
    emitCaseConnector_effect_internal]
  funext i
  simp only [Function.update_apply]
  split_ifs <;>
    simp_all [Work.reference₀, Work.reference₁, Work.available,
      Work.temporary₃, Work.loop₃]

theorem emitPreviousCaseReadConnector_emitted_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0) :
    emitPreviousCaseReadConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀ - values Work.temporary₃
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  change
    (decrementReferenceBy Work.reference₀ Work.temporary₃
        Work.loop₃).emitted values ++
      emitCaseConnector.emitted
        ((decrementReferenceBy Work.reference₀ Work.temporary₃
          Work.loop₃).effect values) = _
  rw [decrementReferenceBy_emitted,
    decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
      values ⟨by decide, by decide, by decide⟩ hloop,
    emitCaseConnector_emitted_internal]
  simp [Work.reference₀, Work.available, Work.temporary₃, Work.loop₃]

theorem emitPreviousCaseReadConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hoffset : values Work.temporary₃ ≤ values Work.reference₀)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPreviousCaseReadConnector.requires values := by
  rw [emitPreviousCaseReadConnector, BinaryRoutine.seq]
  have hdecrement := (decrementReferenceBy_requires Work.reference₀
    Work.temporary₃ Work.loop₃ values).2
      ⟨⟨by decide, by decide, by decide⟩, hloop, hoffset⟩
  refine ⟨hdecrement, ?_⟩
  rw [decrementReferenceBy_effect Work.reference₀ Work.temporary₃ Work.loop₃
    values ⟨by decide, by decide, by decide⟩ hloop]
  apply emitCaseConnector_requires_internal
  · simpa [Work.reference₀, Work.loop₃, Work.copyCounter] using hcopy
  · simpa [Work.reference₀, Work.loop₃, Work.available] using
      havailable
  · simpa [Work.reference₀, Work.loop₃, Work.emitCounter] using hemit

theorem emitPreviousCaseChoiceConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitPreviousCaseChoiceConnector.effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - 1)) Work.available
          (values Work.available + 1)) Work.reference₁ 0 := by
  rw [emitPreviousCaseChoiceConnector, BinaryRoutine.seq,
    emitCaseConnector_effect_internal]
  simp [BinaryRoutine.binaryPred, Work.reference₀, Work.available,
    Work.reference₁]

theorem emitPreviousCaseChoiceConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitPreviousCaseChoiceConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .and
          input₀ := values Work.reference₀ - 1
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  change (BinaryRoutine.binaryPred Work.reference₀).emitted values ++
      emitCaseConnector.emitted
        ((BinaryRoutine.binaryPred Work.reference₀).effect values) = _
  rw [emitCaseConnector_emitted_internal]
  simp [BinaryRoutine.binaryPred, Work.reference₀, Work.available]

theorem emitPreviousCaseChoiceConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hreference : 1 ≤ values Work.reference₀)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitPreviousCaseChoiceConnector.requires values := by
  rw [emitPreviousCaseChoiceConnector, BinaryRoutine.seq]
  refine ⟨?_, ?_⟩
  · exact hreference
  rw [show (BinaryRoutine.binaryPred Work.reference₀).effect values =
      Function.update values Work.reference₀
        (values Work.reference₀ - 1) by rfl]
  apply emitCaseConnector_requires_internal
  · simpa [Work.reference₀, Work.copyCounter] using hcopy
  · simpa [Work.reference₀, Work.available] using havailable
  · simpa [Work.reference₀, Work.emitCounter] using hemit

private theorem emitPreviousCaseReadConnectors_effect
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitPreviousCaseReadConnectors count).effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃ * count))
          Work.available (values Work.available + count))
        Work.reference₁ 0 := by
  induction count generalizing values with
  | zero =>
      funext i
      simp only [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits, Nat.mul_zero, Nat.sub_zero, Nat.add_zero,
        Function.update_apply]
      split_ifs <;> simp_all [Work.reference₁]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors]
      change (emitPreviousCaseReadConnectors count).effect
        (emitPreviousCaseReadConnector.effect values) = _
      rw [emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      have hloopCurrent : current Work.loop₃ = 0 := by
        have hloop' : values 20 = 0 := by
          simpa [Work.loop₃] using hloop
        simpa [current, Work.reference₀, Work.available,
          Work.reference₁, Work.loop₃] using hloop'
      have hreferenceCurrent : current Work.reference₁ = 0 := by
        simp [current]
      rw [ih current hloopCurrent hreferenceCurrent]
      funext i
      simp only [current, Function.update_apply]
      split_ifs <;>
        simp_all [Work.reference₀, Work.available, Work.reference₁,
          Work.temporary₃, Nat.mul_succ, Nat.sub_sub, Nat.add_assoc]
      all_goals omega

private theorem emitPreviousCaseReadConnectors_emitted
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0) :
    (emitPreviousCaseReadConnectors count).emitted values =
      (indexedGateBlocks count fun rank =>
        [{ op := .and
           input₀ := values Work.reference₀ -
             values Work.temporary₃ * (rank + 1)
           input₁ := values Work.available + rank - 1
           negated₀ := false
           negated₁ := false }]).flatMap CircuitCode.RawGate.encode := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors]
      change emitPreviousCaseReadConnector.emitted values ++
        (emitPreviousCaseReadConnectors count).emitted
          (emitPreviousCaseReadConnector.effect values) = _
      rw [emitPreviousCaseReadConnector_emitted_internal values hloop,
        emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      have hloopCurrent : current Work.loop₃ = 0 := by
        have hloop' : values 20 = 0 := by
          simpa [Work.loop₃] using hloop
        simpa [current, Work.reference₀, Work.available,
          Work.reference₁, Work.loop₃] using hloop'
      have hreferenceCurrent : current Work.reference₁ = 0 := by
        simp [current]
      rw [ih current hloopCurrent hreferenceCurrent]
      simp only [indexedGateBlocks, List.flatMap_append]
      simp
      apply congrArg (List.flatMap CircuitCode.RawGate.encode)
      apply congrArg (indexedGateBlocks count)
      funext rank
      simp [current, Work.reference₀, Work.available, Work.reference₁,
        Work.temporary₃, Nat.mul_succ, Nat.sub_sub,
        Nat.add_left_comm, Nat.add_comm]
      omega

private theorem emitPreviousCaseReadConnectors_requires
    (count : ℕ) (values : BinaryValues WorkCount)
    (hloop : values Work.loop₃ = 0)
    (hreference₁ : values Work.reference₁ = 0)
    (hcopy : values Work.copyCounter = 0)
    (hemit : values Work.emitCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hoffset : ∀ rank, rank < count →
      values Work.temporary₃ * (rank + 1) ≤
        values Work.reference₀) :
    (emitPreviousCaseReadConnectors count).requires values := by
  induction count generalizing values with
  | zero =>
      simp [emitPreviousCaseReadConnectors, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitPreviousCaseReadConnectors, BinaryRoutine.seq]
      have hfirstOffset :
          values Work.temporary₃ ≤ values Work.reference₀ := by
        simpa using hoffset 0 (by omega)
      refine ⟨emitPreviousCaseReadConnector_requires_internal values hloop
        hfirstOffset hcopy havailable hemit, ?_⟩
      rw [emitPreviousCaseReadConnector_effect_internal values hloop]
      let current := Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - values Work.temporary₃))
          Work.available (values Work.available + 1)) Work.reference₁ 0
      apply ih current
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.loop₃] using hloop
      · simp [current]
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.copyCounter] using hcopy
      · simpa [current, Work.reference₀, Work.available, Work.reference₁,
          Work.emitCounter] using hemit
      · simp [current, Work.reference₀, Work.available, Work.reference₁]
      · intro rank hrank
        simp only [current, Function.update_apply]
        simp [Work.reference₀, Work.available, Work.reference₁,
          Work.temporary₃]
        have hnext := hoffset (rank + 1) (by omega)
        apply Nat.le_sub_of_add_le
        calc
          values Work.temporary₃ * (rank + 1) +
                values Work.temporary₃ =
              values Work.temporary₃ * (rank + 1 + 1) := by ring
          _ ≤ values Work.reference₀ := hnext

private theorem emitIndexedCaseReads_effect_succ
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount (count + 1) start
        symbolAt).effect values =
      Function.update
        (caseReadStartValues values (start + count) (symbolAt count))
        Work.available
        (values Work.available +
          caseReadSize (values Work.horizon) * (count + 1)) := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp only [emitCaseReads, BinaryRoutine.seq,
        BinaryRoutine.identity, BinaryRoutine.emitBits, Nat.add_zero]
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      funext i
      simp [caseReadStartValues, Work.available, Work.horizon,
        Work.tapeIndex, Work.symbolIndex]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      let current := Function.update
        (caseReadStartValues values start (symbolAt 0)) Work.available
          (values Work.available + caseReadSize (values Work.horizon))
      have hcurrent : ReadFormulaClean current :=
        ReadFormulaClean.updateAvailable
          (caseReadStartValues values start (symbolAt 0))
          (values Work.available + caseReadSize (values Work.horizon))
          (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
            hclean)
      rw [ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
        (values := current) hcurrent]
      funext i
      simp only [current, caseReadStartValues, Function.update_apply]
      split_ifs <;>
        simp_all [Work.available, Work.horizon, Work.tapeIndex,
          Work.symbolIndex, Nat.mul_succ] <;> omega

private theorem emitIndexedCaseReads_effect_zero
    (stateCount workCount start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) :
    (emitCaseReads stateCount workCount 0 start symbolAt).effect
      values = values := by
  simp [emitCaseReads, BinaryRoutine.identity, BinaryRoutine.emitBits]

set_option maxHeartbeats 800000 in
private theorem emitIndexedCaseReads_requires
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount count start symbolAt).requires
      values := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp [emitCaseReads, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      have hhead := emitCaseRead_requires_internal stateCount workCount start
        (symbolAt 0) values hclean
      refine ⟨hhead, ?_⟩
      rw [emitCaseRead_effect_internal stateCount workCount start
        (symbolAt 0) values hclean]
      apply ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
      exact ReadFormulaClean.updateAvailable
        (caseReadStartValues values start (symbolAt 0))
        (values Work.available + caseReadSize (values Work.horizon))
        (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
          hclean)

private theorem emitIndexedCaseReads_emitted
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    (emitCaseReads stateCount workCount count start symbolAt).emitted
        values =
      (indexedGateBlocks count fun index =>
        readFormulaSchedule stateCount (workCount + 2)
          (values Work.horizon) (values Work.configBase)
          (values Work.available +
            caseReadSize (values Work.horizon) * index)
          (start + index) (symbolAt index)).flatMap
            CircuitCode.RawGate.encode := by
  induction count generalizing start symbolAt values with
  | zero =>
      simp [emitCaseReads, BinaryRoutine.identity,
        BinaryRoutine.emitBits, indexedGateBlocks]
  | succ count ih =>
      rw [emitCaseReads]
      simp only [BinaryRoutine.seq]
      rw [emitCaseRead_emitted_internal stateCount workCount start
          (symbolAt 0) values hclean,
        emitCaseRead_effect_internal stateCount workCount start
          (symbolAt 0) values hclean]
      let current := Function.update
        (caseReadStartValues values start (symbolAt 0)) Work.available
          (values Work.available + caseReadSize (values Work.horizon))
      have hcurrent : ReadFormulaClean current :=
        ReadFormulaClean.updateAvailable
          (caseReadStartValues values start (symbolAt 0))
          (values Work.available + caseReadSize (values Work.horizon))
          (ReadFormulaClean.caseReadStartValues values start (symbolAt 0)
            hclean)
      rw [ih (start := start + 1)
        (symbolAt := fun index => symbolAt (index + 1))
        (values := current) hcurrent]
      simp only [indexedGateBlocks, List.flatMap_append]
      simp [current, caseReadStartValues, Work.horizon, Work.configBase,
        Work.available, Work.tapeIndex, Work.symbolIndex, Nat.mul_add,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem emitCaseMembers_effect_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update
        (caseReadStartValues values (workCount + 1) outputSymbolIndex)
        Work.available
        (values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon)
            choiceValue) := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseChoice_effect_internal choiceValue values hclean.reference₀
      hclean.reference₁,
    emitStateReference_effect]
  let afterState := Function.update
    (Function.update
      (Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue))
      Work.available
      ((Function.update values Work.available
        (values Work.available + caseChoiceLiteralSize choiceValue))
          Work.available + 1)) Work.reference₀ 0
  have hafterState : ReadFormulaClean afterState :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable _ _
        (ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean))
  rw [emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
    afterState hafterState]
  let afterInput := Function.update
    (caseReadStartValues afterState 0 inputSymbolIndex) Work.available
      (afterState Work.available + caseReadSize (afterState Work.horizon))
  have hafterInput : ReadFormulaClean afterInput :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  have hreference₀ : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  simp only [id_eq]
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      rw [emitCaseRead_effect_internal stateCount 0 1 outputSymbolIndex
        afterInput hafterInput]
      funext i
      simp only [afterInput, afterState, caseReadStartValues,
        caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
        Work.available, Work.horizon, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex, Function.update_apply]
      split_ifs <;> simp_all
      all_goals omega
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt afterInput hafterInput]
      let afterWork := Function.update
        (caseReadStartValues afterInput (1 + workCount)
          (workSymbolIndexAt workCount)) Work.available
        (afterInput Work.available +
          caseReadSize (afterInput Work.horizon) * (workCount + 1))
      have hafterWork : ReadFormulaClean afterWork :=
        ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues afterInput (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      rw [emitCaseRead_effect_internal stateCount (workCount + 1)
        (workCount + 2) outputSymbolIndex afterWork hafterWork]
      funext i
      simp only [afterWork, afterInput, afterState, caseReadStartValues,
        caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
        Work.available, Work.horizon, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex, Nat.mul_succ, Function.update_apply]
      split_ifs <;> simp_all
      all_goals first
        | omega
        | cases choiceValue <;> norm_num at * <;> ring

theorem emitCaseMembers_requires_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨emitCaseChoice_requires_internal choiceValue values
    hclean.copyCounter hclean.emitCounter, ?_⟩
  rw [emitCaseChoice_effect_internal choiceValue values hclean.reference₀
    hclean.reference₁]
  let afterChoice := Function.update values Work.available
    (values Work.available + caseChoiceLiteralSize choiceValue)
  have hafterChoice : ReadFormulaClean afterChoice :=
    ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean
  refine ⟨emitStateReference_requires stateIndex false afterChoice
    hafterChoice.addCounter hafterChoice.emitCounter, ?_⟩
  rw [emitStateReference_effect]
  have hafterState : ReadFormulaClean
      (Function.update
        (Function.update afterChoice Work.available
          (afterChoice Work.available + 1)) Work.reference₀ 0) :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable afterChoice _ hafterChoice)
  refine ⟨emitCaseRead_requires_internal stateCount workCount 0
    inputSymbolIndex _ hafterState, ?_⟩
  rw [emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
    _ hafterState]
  let afterState := Function.update
    (Function.update afterChoice Work.available
      (afterChoice Work.available + 1)) Work.reference₀ 0
  have hafterInput : ReadFormulaClean
      (Function.update (caseReadStartValues afterState 0 inputSymbolIndex)
        Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))) :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  refine ⟨emitIndexedCaseReads_requires stateCount workCount workCount 1
    workSymbolIndexAt _ hafterInput, ?_⟩
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      constructor
      · apply emitCaseRead_requires_internal
        simpa only [afterState] using hafterInput
      · trivial
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt _ hafterInput]
      constructor
      · apply emitCaseRead_requires_internal
        exact ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues _ (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      · trivial

theorem emitCaseMembers_emitted_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaMemberGates stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt).flatMap
          CircuitCode.RawGate.encode := by
  rw [emitCaseMembers]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseChoice_emitted_internal choiceValue values,
    emitCaseChoice_effect_internal choiceValue values hclean.reference₀
      hclean.reference₁]
  let afterChoice := Function.update values Work.available
    (values Work.available + caseChoiceLiteralSize choiceValue)
  have hafterChoice : ReadFormulaClean afterChoice :=
    ReadFormulaClean.updateAvailable values _ hclean.toReadFormulaClean
  rw [emitStateReference_emitted, emitStateReference_effect]
  have hafterState : ReadFormulaClean
      (Function.update
        (Function.update afterChoice Work.available
          (afterChoice Work.available + 1)) Work.reference₀ 0) :=
    ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable afterChoice _ hafterChoice)
  rw [emitCaseRead_emitted_internal stateCount workCount 0 inputSymbolIndex
      _ hafterState,
    emitCaseRead_effect_internal stateCount workCount 0 inputSymbolIndex
      _ hafterState]
  let afterState := Function.update
    (Function.update afterChoice Work.available
      (afterChoice Work.available + 1)) Work.reference₀ 0
  have hafterInput : ReadFormulaClean
      (Function.update (caseReadStartValues afterState 0 inputSymbolIndex)
        Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))) :=
    ReadFormulaClean.updateAvailable _ _
      (ReadFormulaClean.caseReadStartValues afterState 0 inputSymbolIndex
        hafterState)
  rw [emitIndexedCaseReads_emitted stateCount workCount workCount 1
    workSymbolIndexAt _ hafterInput]
  cases workCount with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      rw [emitCaseRead_emitted_internal stateCount 0 1 outputSymbolIndex _
        (by simpa only [afterState] using hafterInput)]
      simp only [List.append_nil]
      simp [caseFormulaMemberGates, caseWorkReadGates,
        caseInputReadAvailable, caseOutputReadAvailable,
        caseChoiceLiteralSize, indexedGateBlocks, List.flatMap_append,
        afterChoice, caseReadStartValues, Work.available,
        Work.horizon, Work.configBase, Work.reference₀, Work.tapeIndex,
        Work.symbolIndex]
  | succ workCount =>
      rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
        workCount 1 workSymbolIndexAt _ hafterInput]
      let afterInput := Function.update
        (caseReadStartValues afterState 0 inputSymbolIndex) Work.available
        (afterState Work.available + caseReadSize (afterState Work.horizon))
      have hafterWork : ReadFormulaClean
          (Function.update
            (caseReadStartValues afterInput (1 + workCount)
              (workSymbolIndexAt workCount)) Work.available
            (afterInput Work.available +
              caseReadSize (afterInput Work.horizon) * (workCount + 1))) :=
        ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues afterInput (1 + workCount)
            (workSymbolIndexAt workCount) hafterInput)
      rw [emitCaseRead_emitted_internal stateCount (workCount + 1)
        (workCount + 2) outputSymbolIndex _
          (by simpa only [afterInput, afterState] using hafterWork)]
      simp only [List.append_nil]
      simp [caseFormulaMemberGates, caseWorkReadGates,
        caseInputReadAvailable, caseWorkReadAvailable,
        caseOutputReadAvailable, caseChoiceLiteralSize,
        List.flatMap_append, afterState, afterChoice, caseReadStartValues,
        Work.available, Work.horizon, Work.configBase, Work.reference₀,
        Work.tapeIndex, Work.symbolIndex, Nat.mul_succ,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private def caseFormulaConnectorStartValues
    (values : BinaryValues WorkCount) (workCount outputSymbolIndex : ℕ)
    (choiceValue : Bool) : BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (caseReadStartValues values (workCount + 1) outputSymbolIndex)
            Work.temporary₃ (caseReadSize (values Work.horizon)))
          Work.temporary₂ 0) Work.reference₀
        (values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon) choiceValue -
          1)) Work.available
      (values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue + 2))
    Work.reference₁ 0

private theorem caseFormulaConnectorStart_effect
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    emitCaseConnector.effect
        ((prepareRecentReference Work.reference₀ 2).effect
          (prepareCaseReadSize.effect
            ((emitConstantGate true).effect
              ((emitCaseMembers stateCount workCount stateIndex
                inputSymbolIndex outputSymbolIndex choiceValue
                workSymbolIndexAt).effect values)))) =
      caseFormulaConnectorStartValues values workCount outputSymbolIndex
        choiceValue := by
  rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean,
    emitConstantGate_effect_internal, prepareCaseReadSize_effect_internal,
    prepareRecentReference_effect, emitCaseConnector_effect_internal]
  funext i
  simp only [caseFormulaConnectorStartValues, caseReadStartValues,
    Work.horizon, Work.available, Work.reference₀, Work.reference₁, Work.temporary₂,
    Work.temporary₃, Work.tapeIndex, Work.symbolIndex,
    Function.update_apply]
  split_ifs <;> simp_all

theorem emitCaseFormula_effect_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).effect values =
      Function.update values Work.available
        (values Work.available +
          caseFormulaScheduleSize workCount (values Work.horizon)
            choiceValue) := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    have hloop' : values 20 = 0 := by
      simpa [Work.loop₃] using hclean.loop₃
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀, Work.reference₁,
      Work.loop₃, Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex] using hloop'
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  rw [emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads
    hloop hreference₁]
  rw [emitPreviousCaseChoiceConnector_effect_internal]
  have hreference₀' : values 7 = 0 := by
    simpa [Work.reference₀] using hclean.reference₀
  have hreference₁' : values 8 = 0 := by
    simpa [Work.reference₁] using hclean.reference₁
  have htemporary₃' : values 25 = 0 := by
    simpa [Work.temporary₃] using hclean.temporary₃
  have htemporary₂' : values 24 = 0 := by
    simpa [Work.temporary₂] using hclean.temporary₂
  have htapeIndex' : values 29 = 0 := by
    simpa [Work.tapeIndex] using hclean.tapeIndex
  have hsymbolIndex' : values 31 = 0 := by
    simpa [Work.symbolIndex] using hclean.symbolIndex
  funext i
  simp only [beforeReads, caseFormulaConnectorStartValues,
    BinaryRoutine.clear, caseReadStartValues, caseFormulaScheduleSize,
    caseFormulaMembersSize, caseFormulaMemberCount, caseReadSize,
    Work.horizon, Work.available, Work.reference₀, Work.reference₁,
    Work.temporary₂, Work.temporary₃, Work.tapeIndex,
    Work.symbolIndex, WorkCount]
  simp_rw [Function.update_apply]
  split_ifs <;> simp_all [Nat.mul_succ] <;> try omega
  all_goals simp_rw [Function.update_apply]
  all_goals split_ifs <;> simp_all

theorem emitCaseFormula_requires_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).requires values := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨emitCaseMembers_requires_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean, ?_⟩
  refine ⟨?_, ?_⟩
  · apply emitConstantGate_requires_internal
    rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean]
    simp [Work.available, Work.emitCounter]
    exact hclean.emitCounter
  refine ⟨?_, ?_⟩
  · apply prepareCaseReadSize_requires_internal
    · rw [emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simp [Work.available, Work.multiplyCounter]
      exact hclean.multiplyCounter
    · rw [emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simp [Work.available, Work.addCounter]
      exact hclean.addCounter
  refine ⟨?_, ?_⟩
  · apply (prepareRecentReference_requires Work.reference₀ 2 _
      (by decide) (by decide) (by decide)).2
    constructor
    · rw [prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simp [Work.temporary₂, Work.temporary₃, Work.available, Work.copyCounter]
      exact hclean.copyCounter
    · rw [prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      cases choiceValue <;>
        simp [caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
          Work.temporary₂, Work.temporary₃, Work.available] <;> omega
  refine ⟨?_, ?_⟩
  · apply emitCaseConnector_requires_internal
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simp [Work.reference₀, Work.temporary₂, Work.temporary₃, Work.available, Work.copyCounter]
      exact hclean.copyCounter
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      cases choiceValue <;>
        simp [caseFormulaMembersSize, caseChoiceLiteralSize, caseReadSize,
          Work.reference₀, Work.temporary₂, Work.temporary₃,
          Work.available]
    · rw [prepareRecentReference_effect,
        prepareCaseReadSize_effect_internal,
        emitConstantGate_effect_internal,
        emitCaseMembers_effect_internal stateCount workCount stateIndex
          inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
          values hclean]
      simp [Work.reference₀, Work.temporary₂, Work.temporary₃, Work.available, Work.emitCounter]
      exact hclean.emitCounter
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex] using hclean.loop₃
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  have hbeforeAvailable : beforeReads Work.available =
      values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue +
          2 := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeReference₀ : beforeReads Work.reference₀ =
      values Work.available +
        caseFormulaMembersSize workCount (values Work.horizon) choiceValue -
          1 := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeTemporary₃ : beforeReads Work.temporary₃ =
      caseReadSize (values Work.horizon) := by
    simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hbeforeCopy : beforeReads Work.copyCounter = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex, Work.copyCounter] using
      hclean.copyCounter
  have hbeforeEmit : beforeReads Work.emitCounter = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex, Work.emitCounter] using
      hclean.emitCounter
  refine ⟨emitPreviousCaseReadConnectors_requires (workCount + 2)
    beforeReads hloop hreference₁ ?_ ?_ ?_ ?_, ?_⟩
  · exact hbeforeCopy
  · exact hbeforeEmit
  · rw [hbeforeAvailable]
    omega
  · intro rank hrank
    rw [hbeforeReference₀, hbeforeTemporary₃]
    have hrankle : rank + 1 ≤ workCount + 2 := by omega
    calc
      caseReadSize (values Work.horizon) * (rank + 1) ≤
          caseReadSize (values Work.horizon) * (workCount + 2) :=
        Nat.mul_le_mul_left _ hrankle
      _ ≤ values Work.available +
          caseFormulaMembersSize workCount (values Work.horizon)
            choiceValue - 1 := by
        rw [caseFormulaMembersSize, Nat.mul_comm
          (caseReadSize (values Work.horizon)) (workCount + 2)]
        cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
  rw [emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads
    hloop hreference₁]
  refine ⟨emitPreviousCaseChoiceConnector_requires_internal _ ?_ ?_ ?_ ?_,
    ⟨trivial, trivial, trivial, trivial, trivial⟩⟩
  · have hremaining : beforeReads Work.reference₀ -
        beforeReads Work.temporary₃ * (workCount + 2) =
          values Work.available + caseChoiceLiteralSize choiceValue := by
      rw [hbeforeReference₀, hbeforeTemporary₃,
        caseFormulaMembersSize, Nat.mul_comm
          (caseReadSize (values Work.horizon)) (workCount + 2)]
      cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
    simpa [Work.reference₀, Work.reference₁, Work.available,
      hremaining] using show
        1 ≤ beforeReads Work.reference₀ -
          beforeReads Work.temporary₃ * (workCount + 2) by
        rw [hremaining]
        cases choiceValue <;> simp [caseChoiceLiteralSize]
  · simpa [Work.reference₀, Work.reference₁, Work.available,
      Work.copyCounter] using hbeforeCopy
  · simpa [Work.reference₀, Work.reference₁, Work.available] using
      show 1 ≤ beforeReads Work.available + (workCount + 2) by
        rw [hbeforeAvailable]
        omega
  · simpa [Work.reference₀, Work.reference₁, Work.available,
      Work.emitCounter] using hbeforeEmit

private theorem prefixSize_caseFormulaSizeAt_two_add
    (workCount T : ℕ) (choiceValue : Bool) (offset : ℕ)
    (hoffset : 2 + offset ≤ caseFormulaMemberCount workCount) :
    prefixSize (caseFormulaSizeAt workCount T choiceValue) (2 + offset) =
      caseChoiceLiteralSize choiceValue + 1 + offset * caseReadSize T := by
  induction offset with
  | zero => simp [prefixSize, caseFormulaSizeAt]
  | succ offset ih =>
      rw [show 2 + (offset + 1) = (2 + offset) + 1 by omega,
        prefixSize_succ_internal, ih (by omega)]
      have hindex : 2 + offset < caseFormulaMemberCount workCount := by
        omega
      have hneOne : 2 + offset ≠ 1 := by omega
      simp [caseFormulaSizeAt, hindex, hneOne, Nat.add_mul,
        Nat.add_assoc]

private theorem getElem_indexedCaseConnectorBlocks
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate)
    (index : ℕ) (hindex : index < count) :
    (indexedGateBlocks count fun rank => [gateAt rank])[index]'(by
      rw [length_indexedGateBlocks count 1 _ (by simp)]
      omega) = gateAt index := by
  have hget := getElem_indexedGateBlocks count 1
    (fun rank => [gateAt rank]) (by simp) index 0 hindex (by omega)
  simpa using hget

private theorem initialCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    ({ op := .and
       input₀ := available + caseFormulaMembersSize workCount T choiceValue - 1
       input₁ := available + caseFormulaMembersSize workCount T choiceValue
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) 0 := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hcount : caseFormulaMemberCount workCount - 0 - 1 + 1 =
      caseFormulaMemberCount workCount := by
    simp [caseFormulaMemberCount]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcount, hcountForm,
    prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
      (workCount + 2) (by
        simp only [caseFormulaMemberCount]
        omega)]
  simp [caseFormulaMembersSize]

private theorem middleCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool)
    (rank : ℕ) (hrank : rank < workCount + 2) :
    ({ op := .and
       input₀ := available +
         caseFormulaMembersSize workCount T choiceValue - 1 -
           caseReadSize T * (rank + 1)
       input₁ := available +
         caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) (rank + 1) := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : caseFormulaMemberCount workCount - (rank + 1) - 1 + 1 =
      2 + (workCount + 1 - rank) := by
    simp [caseFormulaMemberCount]
    omega
  rw [hmember,
    prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
      (workCount + 1 - rank) (by
        simp only [caseFormulaMemberCount]
        omega)]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcountForm, prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
    (workCount + 2) (by
      simp only [caseFormulaMemberCount]
      omega)]
  have hsplit : workCount + 2 =
      (workCount + 1 - rank) + (rank + 1) := by omega
  rw [caseFormulaMembersSize, hsplit, Nat.add_mul]
  rw [Nat.mul_comm (caseReadSize T) (rank + 1)]
  simp only [CircuitCode.RawGate.mk.injEq]
  constructor
  all_goals cases choiceValue <;>
    simp [caseChoiceLiteralSize, caseFormulaMemberCount] at * <;> omega

private theorem lastCaseConnector_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    ({ op := .and
       input₀ := available +
         caseFormulaMembersSize workCount T choiceValue - 1 -
           caseReadSize T * (workCount + 2) - 1
       input₁ := available +
         caseFormulaMembersSize workCount T choiceValue + 2 +
           (workCount + 2) - 1
       negated₀ := false
       negated₁ := false } : CircuitCode.RawGate) =
      indexedRightFoldConnector .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) (workCount + 3) := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmember : caseFormulaMemberCount workCount - (workCount + 3) - 1 + 1 =
      1 := by
    simp [caseFormulaMemberCount]
  rw [hmember]
  have hcountForm : caseFormulaMemberCount workCount =
      2 + (workCount + 2) := by
    simp only [caseFormulaMemberCount]
    omega
  rw [hcountForm, prefixSize_caseFormulaSizeAt_two_add workCount T choiceValue
    (workCount + 2) (by
      simp only [caseFormulaMemberCount]
      omega)]
  simp [prefixSize, caseFormulaSizeAt, caseFormulaMembersSize]
  rw [Nat.mul_comm (caseReadSize T) (workCount + 2)]
  constructor
  · cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
  · omega

private theorem caseConnectorGates_eq
    (workCount T available : ℕ) (choiceValue : Bool) :
    (([({ op := .and
          input₀ := available +
            caseFormulaMembersSize workCount T choiceValue - 1
          input₁ := available +
            caseFormulaMembersSize workCount T choiceValue
          negated₀ := false
          negated₁ := false } : CircuitCode.RawGate)] ++
      indexedGateBlocks (workCount + 2) fun rank =>
        [({ op := .and
            input₀ := available +
              caseFormulaMembersSize workCount T choiceValue - 1 -
                caseReadSize T * (rank + 1)
            input₁ := available +
              caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
            negated₀ := false
            negated₁ := false } : CircuitCode.RawGate)]) ++
      [({ op := .and
          input₀ := available +
            caseFormulaMembersSize workCount T choiceValue - 1 -
              caseReadSize T * (workCount + 2) - 1
          input₁ := available +
            caseFormulaMembersSize workCount T choiceValue + 2 +
              (workCount + 2) - 1
          negated₀ := false
          negated₁ := false } : CircuitCode.RawGate)]) =
      indexedRightFoldConnectors .and available
        (caseFormulaMemberCount workCount)
        (caseFormulaSizeAt workCount T choiceValue) := by
  apply List.ext_getElem
  · simp [length_indexedGateBlocks, length_indexedRightFoldConnectors,
      caseFormulaMemberCount]
  · intro index hleft hright
    have hindex : index < workCount + 4 := by
      simpa [length_indexedRightFoldConnectors,
        caseFormulaMemberCount] using hright
    by_cases hzero : index = 0
    · subst index
      rw [List.getElem_append_left (by
        simp [length_indexedGateBlocks])]
      rw [List.getElem_append_left (by simp)]
      simp only [List.getElem_cons_zero]
      exact (initialCaseConnector_eq workCount T available choiceValue).trans
        (getElem_indexedRightFoldConnectors .and available
          (caseFormulaMemberCount workCount)
          (caseFormulaSizeAt workCount T choiceValue)
          ⟨0, by simp [caseFormulaMemberCount]⟩).symm
    · by_cases hmiddle : index < workCount + 3
      · rw [List.getElem_append_left (by
          simp [length_indexedGateBlocks]
          omega)]
        rw [List.getElem_append_right (by simp; omega)]
        have hrank : index - 1 < workCount + 2 := by omega
        simp only [List.length_singleton]
        rw [getElem_indexedCaseConnectorBlocks (workCount + 2) (fun rank =>
          ({ op := .and
             input₀ := available +
               caseFormulaMembersSize workCount T choiceValue - 1 -
                 caseReadSize T * (rank + 1)
             input₁ := available +
               caseFormulaMembersSize workCount T choiceValue + 2 + rank - 1
             negated₀ := false
             negated₁ := false } : CircuitCode.RawGate)) (index - 1)
          hrank]
        have hindexEq : index - 1 + 1 = index := by omega
        rw [middleCaseConnector_eq workCount T available choiceValue
          (index - 1) hrank, hindexEq]
        exact (getElem_indexedRightFoldConnectors .and available
          (caseFormulaMemberCount workCount)
          (caseFormulaSizeAt workCount T choiceValue)
          ⟨index, by simpa [caseFormulaMemberCount] using hindex⟩).symm
      · have hlast : index = workCount + 3 := by omega
        subst index
        rw [List.getElem_append_right (by
          simp [length_indexedGateBlocks])]
        simpa [length_indexedGateBlocks] using
          (lastCaseConnector_eq workCount T available choiceValue).trans
          (getElem_indexedRightFoldConnectors .and available
            (caseFormulaMemberCount workCount)
            (caseFormulaSizeAt workCount T choiceValue)
            ⟨workCount + 3, by simp [caseFormulaMemberCount]⟩).symm

private theorem encode_cons_append_singleton
    (first last : CircuitCode.RawGate) (middle : CircuitCode.RawCircuit) :
    first.encode ++ (middle.flatMap CircuitCode.RawGate.encode ++
      last.encode) =
      (([first] ++ middle) ++ [last]).flatMap
        CircuitCode.RawGate.encode := by
  simp [List.flatMap_append]

theorem emitCaseFormula_emitted_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : CaseFormulaClean values) :
    (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
      outputSymbolIndex choiceValue workSymbolIndexAt).emitted values =
      (caseFormulaSchedule stateCount workCount (values Work.horizon)
        (values Work.configBase) (values Work.reference₀)
        (values Work.available) stateIndex inputSymbolIndex outputSymbolIndex
        choiceValue workSymbolIndexAt).flatMap CircuitCode.RawGate.encode := by
  simp only [emitCaseFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [emitCaseMembers_emitted_internal stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  have hreference :
      (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt).effect values
          Work.reference₀ = 0 := by
    rw [emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean]
    simpa [caseReadStartValues, Work.tapeIndex, Work.symbolIndex,
      Work.available, Work.reference₀] using hclean.reference₀
  rw [emitConstantGate_emitted_internal true _ hreference,
    prepareCaseReadSize_emitted_internal, prepareRecentReference_emitted,
    emitCaseConnector_emitted_internal]
  rw [caseFormulaConnectorStart_effect stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
    hclean]
  let beforeReads := caseFormulaConnectorStartValues values workCount
    outputSymbolIndex choiceValue
  have hloop : beforeReads Work.loop₃ = 0 := by
    simpa [beforeReads, caseFormulaConnectorStartValues,
      caseReadStartValues, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁, Work.temporary₂, Work.temporary₃,
      Work.tapeIndex, Work.symbolIndex] using hclean.loop₃
  have hreference₁ : beforeReads Work.reference₁ = 0 := by
    simp [beforeReads, caseFormulaConnectorStartValues]
  rw [emitPreviousCaseReadConnectors_emitted (workCount + 2) beforeReads
    hloop hreference₁,
    emitPreviousCaseReadConnectors_effect (workCount + 2) beforeReads hloop
      hreference₁,
    emitPreviousCaseChoiceConnector_emitted_internal]
  simp only [BinaryRoutine.clear, List.append_nil]
  rw [caseFormulaSchedule, List.flatMap_append,
    List.flatMap_append, List.flatMap_singleton]
  simp only [List.nil_append, List.append_assoc]
  apply congrArg₂ List.append rfl
  simp only [directInitConstant]
  apply congrArg₂ List.append rfl
  rw [encode_cons_append_singleton]
  apply congrArg (List.flatMap CircuitCode.RawGate.encode)
  convert caseConnectorGates_eq workCount (values Work.horizon)
    (values Work.available) choiceValue using 1
  all_goals simp [beforeReads, caseFormulaConnectorStartValues, caseReadStartValues,
    caseFormulaMembersSize, caseReadSize, Work.horizon, Work.available,
    Work.reference₀, Work.reference₁, Work.temporary₂,
    Work.temporary₃, Work.tapeIndex, Work.symbolIndex,
    emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt values
      hclean,
    emitConstantGate_effect_internal, prepareCaseReadSize_effect_internal,
    prepareRecentReference_effect,
    Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  all_goals omega

private theorem emitCaseChoice_spaceBoundByWidthAt
    (choiceValue : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          caseChoiceLiteralSize choiceValue ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (emitCaseChoice choiceValue)
      initialSpace values width := by
  cases choiceValue with
  | true =>
      apply emitCopyGate_spaceBoundByWidth Work.reference₀ false
      · intro inputLength
        have := havailable inputLength
        simp [caseChoiceLiteralSize] at this
        omega
      · exact hreference₀
  | false =>
      let copy := emitCopyGate Work.reference₀ false
      let recent := emitRecentGate .and true true 1 1
      let copied : ℕ → BinaryValues WorkCount := fun inputLength =>
        copy.effect (values inputLength)
      have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
          width := by
        apply emitCopyGate_spaceBoundByWidth Work.reference₀ false
        · intro inputLength
          have := havailable inputLength
          simp [caseChoiceLiteralSize] at this
          omega
        · exact hreference₀
      have hrecent : BinaryRoutine.SpaceBoundByWidthAt recent initialSpace
          copied width := by
        apply emitRecentGate_spaceBoundByWidth .and true true 1 1
        · intro inputLength
          simp [copied, copy, emitCopyGate_effect_internal, Work.available]
          have := havailable inputLength
          simp [caseChoiceLiteralSize, Work.available] at this
          omega
        · intro inputLength
          rw [show copied inputLength =
              Function.update (values inputLength) Work.available
                (values inputLength Work.available + 1) by
            exact emitCopyGate_effect_internal Work.reference₀ false
              (values inputLength)]
          simpa [Work.available, Work.reference₀] using
            hreference₀ inputLength
        · intro inputLength
          rw [show copied inputLength =
              Function.update (values inputLength) Work.available
                (values inputLength Work.available + 1) by
            exact emitCopyGate_effect_internal Work.reference₀ false
              (values inputLength)]
          simpa [Work.available, Work.reference₁] using
            hreference₁ inputLength
        · intro inputLength
          simp [copied, copy, emitCopyGate_effect_internal, Work.available]
        · intro inputLength
          simp [copied, copy, emitCopyGate_effect_internal, Work.available]
      simpa [emitCaseChoice, copy, recent, copied] using
        (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy hrecent)

private theorem emitCaseRead_spaceBoundByWidthAt
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, ReadFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (htapeIndex : ∀ inputLength, tapeIndex ≤ width inputLength)
    (hsymbolIndex : ∀ inputLength, symbolIndex ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          caseReadSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hheadCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
        transitionHeadRef stateCount
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position +
            tapeIndex + values inputLength Work.horizon + 1 ≤
          width inputLength)
    (hcellCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
        transitionCellRef stateCount (workCount + 2)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position
              symbolIndex +
            (tapeIndex * (values inputLength Work.horizon + 2) +
              position) +
            (values inputLength Work.horizon + 2) + (workCount + 2) +
            tapeIndex + 4 ≤
          width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitCaseRead stateCount workCount tapeIndex symbolIndex)
      initialSpace values width := by
  let setTape := BinaryRoutine.set Work.tapeIndex tapeIndex
  let setSymbol := BinaryRoutine.set Work.symbolIndex symbolIndex
  let selected : ℕ → BinaryValues WorkCount := fun inputLength =>
    caseReadStartValues (values inputLength) tapeIndex symbolIndex
  have hsetTape : BinaryRoutine.SpaceBoundByWidthAt setTape initialSpace
      values width :=
    BinaryRoutine.SpaceBoundByWidthAt.set Work.tapeIndex tapeIndex
      (fun inputLength => hvalues inputLength Work.tapeIndex) htapeIndex
  have hsetSymbol : BinaryRoutine.SpaceBoundByWidthAt setSymbol initialSpace
      (fun inputLength => setTape.effect (values inputLength)) width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.symbolIndex symbolIndex
    · intro inputLength
      simpa [setTape, BinaryRoutine.set, BinaryRoutine.seq,
        BinaryRoutine.clear, BinaryRoutine.addConst, Work.tapeIndex,
        Work.symbolIndex] using hvalues inputLength Work.symbolIndex
    · exact hsymbolIndex
  have hselectedEffect : ∀ inputLength,
      setSymbol.effect (setTape.effect (values inputLength)) =
        selected inputLength := by
    intro inputLength
    exact caseReadStartValues_eq_effect (values inputLength) tapeIndex
      symbolIndex
  have hselectedClean : ∀ inputLength,
      ReadFormulaClean (selected inputLength) := by
    intro inputLength
    exact ReadFormulaClean.caseReadStartValues (values inputLength) tapeIndex
      symbolIndex (hclean inputLength)
  have hselectedValues : ∀ inputLength index,
      selected inputLength index ≤ width inputLength := by
    intro inputLength index
    by_cases htape : index = Work.tapeIndex
    · subst index
      simpa [selected, caseReadStartValues, Work.tapeIndex,
        Work.symbolIndex] using htapeIndex inputLength
    by_cases hsymbol : index = Work.symbolIndex
    · subst index
      simp [selected, caseReadStartValues, Work.tapeIndex, Work.symbolIndex]
      exact hsymbolIndex inputLength
    · simpa [selected, caseReadStartValues, Function.update_apply,
        htape, hsymbol] using hvalues inputLength index
  have hread : BinaryRoutine.SpaceBoundByWidthAt
      (emitReadFormula stateCount (workCount + 2)) initialSpace selected
      width := by
    apply emitReadFormula_spaceBoundByWidth stateCount (workCount + 2)
    · exact hselectedClean
    · exact hselectedValues
    · intro inputLength
      simpa [selected, caseReadStartValues, caseReadSize, Work.available,
        Work.horizon, Work.tapeIndex, Work.symbolIndex] using
          hfrontier inputLength
    · intro inputLength position hposition
      simpa [selected, caseReadStartValues, Work.horizon, Work.configBase,
        Work.tapeIndex, Work.position, Work.symbolIndex] using
          hheadCap inputLength position (by
            simpa [selected, caseReadStartValues, Work.horizon,
              Work.tapeIndex, Work.symbolIndex] using hposition)
    · intro inputLength position hposition
      simpa [selected, caseReadStartValues, Work.horizon, Work.configBase,
        Work.tapeIndex, Work.position, Work.symbolIndex] using
          hcellCap inputLength position (by
            simpa [selected, caseReadStartValues, Work.horizon,
              Work.tapeIndex, Work.symbolIndex] using hposition)
  unfold emitCaseRead
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · simpa [setTape] using hsetTape
  constructor
  · simpa [setTape, setSymbol] using hsetSymbol
  constructor
  · rw [show (fun inputLength =>
        (BinaryRoutine.set Work.symbolIndex symbolIndex).effect
          ((BinaryRoutine.set Work.tapeIndex tapeIndex).effect
            (values inputLength))) = selected by
      funext inputLength
      exact hselectedEffect inputLength]
    exact hread
  · trivial

private theorem emitCaseRead_preservesClean
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadFormulaClean
      ((emitCaseRead stateCount workCount tapeIndex symbolIndex).effect
        values) := by
  rw [emitCaseRead_effect_internal stateCount workCount tapeIndex symbolIndex
    values hclean]
  exact ReadFormulaClean.updateAvailable _ _
    (ReadFormulaClean.caseReadStartValues values tapeIndex symbolIndex hclean)

private theorem emitCaseRead_effect_values_le
    (stateCount workCount tapeIndex symbolIndex : ℕ)
    {values : BinaryValues WorkCount} {width : ℕ}
    (hclean : ReadFormulaClean values)
    (hvalues : ∀ index, values index ≤ width)
    (htapeIndex : tapeIndex ≤ width)
    (hsymbolIndex : symbolIndex ≤ width)
    (hfrontier : values Work.available + caseReadSize (values Work.horizon) ≤
      width) :
    ∀ index,
      (emitCaseRead stateCount workCount tapeIndex symbolIndex).effect
          values index ≤ width := by
  rw [emitCaseRead_effect_internal stateCount workCount tapeIndex symbolIndex
    values hclean]
  apply BinaryRoutine.values_update_le Work.available
  · unfold caseReadStartValues
    exact BinaryRoutine.values_update_le Work.symbolIndex
      (BinaryRoutine.values_update_le Work.tapeIndex hvalues htapeIndex)
      hsymbolIndex
  · exact hfrontier

private theorem emitCaseReads_spaceBoundByWidthAt
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, ReadFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (htapeIndices : ∀ inputLength index, index < count →
      start + index ≤ width inputLength)
    (hsymbolIndices : ∀ inputLength index, index < count →
      symbolAt index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          count * caseReadSize (values inputLength Work.horizon) ≤
        width inputLength)
    (hheadCap : ∀ inputLength index, index < count →
      ∀ position, position ≤ values inputLength Work.horizon →
        transitionHeadRef stateCount
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) (start + index) position +
            (start + index) + values inputLength Work.horizon + 1 ≤
          width inputLength)
    (hcellCap : ∀ inputLength index, index < count →
      ∀ position, position ≤ values inputLength Work.horizon →
        transitionCellRef stateCount (workCount + 2)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) (start + index) position
              (symbolAt index) +
            ((start + index) *
                (values inputLength Work.horizon + 2) + position) +
            (values inputLength Work.horizon + 2) + (workCount + 2) +
            (start + index) + 4 ≤
          width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitCaseReads stateCount workCount count start symbolAt)
      initialSpace values width := by
  induction count generalizing start symbolAt values with
  | zero => exact BinaryRoutine.SpaceBoundByWidthAt.identity
  | succ count ih =>
      let head := emitCaseRead stateCount workCount start (symbolAt 0)
      let current : ℕ → BinaryValues WorkCount := fun inputLength =>
        Function.update
          (caseReadStartValues (values inputLength) start (symbolAt 0))
          Work.available
          (values inputLength Work.available +
            caseReadSize (values inputLength Work.horizon))
      have hhead : BinaryRoutine.SpaceBoundByWidthAt head initialSpace values
          width := by
        apply emitCaseRead_spaceBoundByWidthAt
        · exact hclean
        · exact hvalues
        · intro inputLength
          exact htapeIndices inputLength 0 (by omega)
        · intro inputLength
          exact hsymbolIndices inputLength 0 (by omega)
        · intro inputLength
          have hbound := hfrontier inputLength
          simp only [Nat.succ_mul] at hbound
          omega
        · intro inputLength position hposition
          simpa using hheadCap inputLength 0 (by omega) position hposition
        · intro inputLength position hposition
          simpa using hcellCap inputLength 0 (by omega) position hposition
      have hheadEffect : ∀ inputLength,
          head.effect (values inputLength) = current inputLength := by
        intro inputLength
        exact emitCaseRead_effect_internal stateCount workCount start
          (symbolAt 0) (values inputLength) (hclean inputLength)
      have hcurrentClean : ∀ inputLength,
          ReadFormulaClean (current inputLength) := by
        intro inputLength
        exact ReadFormulaClean.updateAvailable _ _
          (ReadFormulaClean.caseReadStartValues (values inputLength) start
            (symbolAt 0) (hclean inputLength))
      have hcurrentValues : ∀ inputLength index,
          current inputLength index ≤ width inputLength := by
        intro inputLength index
        by_cases havailable : index = Work.available
        · subst index
          simp [current, caseReadStartValues, Work.available,
            Work.tapeIndex, Work.symbolIndex]
          have hbound := hfrontier inputLength
          simp only [Work.available] at hbound
          simp only [Nat.succ_mul] at hbound
          omega
        by_cases htape : index = Work.tapeIndex
        · subst index
          simpa [current, caseReadStartValues, Work.available,
            Work.tapeIndex, Work.symbolIndex] using
              htapeIndices inputLength 0 (by omega)
        by_cases hsymbol : index = Work.symbolIndex
        · subst index
          simpa [current, caseReadStartValues, Work.available,
            Work.tapeIndex, Work.symbolIndex] using
              hsymbolIndices inputLength 0 (by omega)
        · simpa [current, caseReadStartValues, Function.update_apply,
            havailable, htape, hsymbol] using hvalues inputLength index
      have htail : BinaryRoutine.SpaceBoundByWidthAt
          (emitCaseReads stateCount workCount count (start + 1)
            (fun index => symbolAt (index + 1))) initialSpace current width := by
        apply ih
        · exact hcurrentClean
        · exact hcurrentValues
        · intro inputLength index hindex
          have := htapeIndices inputLength (index + 1) (by omega)
          omega
        · intro inputLength index hindex
          exact hsymbolIndices inputLength (index + 1) (by omega)
        · intro inputLength
          have hcurrentAvailable : current inputLength Work.available =
              values inputLength Work.available +
                caseReadSize (values inputLength Work.horizon) := by
            simp [current, caseReadStartValues, Work.available,
              Work.tapeIndex, Work.symbolIndex]
          have hcurrentHorizon : current inputLength Work.horizon =
              values inputLength Work.horizon := by
            simp [current, caseReadStartValues, Work.available, Work.horizon,
              Work.tapeIndex, Work.symbolIndex]
          rw [hcurrentAvailable, hcurrentHorizon]
          have hbound := hfrontier inputLength
          simp only [Nat.succ_mul] at hbound
          omega
        · intro inputLength index hindex position hposition
          have hcurrentHorizon : current inputLength Work.horizon =
              values inputLength Work.horizon := by
            simp [current, caseReadStartValues, Work.horizon,
              Work.available, Work.tapeIndex, Work.symbolIndex]
          have hcurrentConfig : current inputLength Work.configBase =
              values inputLength Work.configBase := by
            simp [current, caseReadStartValues, Work.configBase,
              Work.available, Work.tapeIndex, Work.symbolIndex]
          rw [hcurrentHorizon] at hposition
          rw [hcurrentHorizon, hcurrentConfig]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hheadCap inputLength (index + 1) (by omega) position hposition
        · intro inputLength index hindex position hposition
          have hcurrentHorizon : current inputLength Work.horizon =
              values inputLength Work.horizon := by
            simp [current, caseReadStartValues, Work.horizon,
              Work.available, Work.tapeIndex, Work.symbolIndex]
          have hcurrentConfig : current inputLength Work.configBase =
              values inputLength Work.configBase := by
            simp [current, caseReadStartValues, Work.configBase,
              Work.available, Work.tapeIndex, Work.symbolIndex]
          rw [hcurrentHorizon] at hposition
          rw [hcurrentHorizon, hcurrentConfig]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            hcellCap inputLength (index + 1) (by omega) position hposition
      have htail' : BinaryRoutine.SpaceBoundByWidthAt
          (emitCaseReads stateCount workCount count (start + 1)
            (fun index => symbolAt (index + 1))) initialSpace
          (fun inputLength => head.effect (values inputLength)) width := by
        simpa only [hheadEffect] using htail
      simpa [emitCaseReads, head, current] using
        (BinaryRoutine.SpaceBoundByWidthAt.seq hhead htail')

private theorem emitCaseReads_preservesClean
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadFormulaClean
      ((emitCaseReads stateCount workCount count start symbolAt).effect
        values) := by
  cases count with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      exact hclean
  | succ count =>
      rw [emitIndexedCaseReads_effect_succ stateCount workCount count start
        symbolAt values hclean]
      exact ReadFormulaClean.updateAvailable _ _
        (ReadFormulaClean.caseReadStartValues values (start + count)
          (symbolAt count) hclean)

private theorem emitCaseReads_effect_values_le
    (stateCount workCount count start : ℕ) (symbolAt : ℕ → ℕ)
    {values : BinaryValues WorkCount} {width : ℕ}
    (hclean : ReadFormulaClean values)
    (hvalues : ∀ index, values index ≤ width)
    (htapeIndices : ∀ index, index < count → start + index ≤ width)
    (hsymbolIndices : ∀ index, index < count → symbolAt index ≤ width)
    (hfrontier : values Work.available +
        count * caseReadSize (values Work.horizon) ≤ width) :
    ∀ index,
      (emitCaseReads stateCount workCount count start symbolAt).effect
          values index ≤ width := by
  intro index
  cases count with
  | zero =>
      rw [emitIndexedCaseReads_effect_zero]
      exact hvalues index
  | succ count =>
      rw [emitIndexedCaseReads_effect_succ stateCount workCount count start
        symbolAt values hclean]
      by_cases havailable : index = Work.available
      · subst index
        simp only [Function.update_self]
        rw [Nat.mul_comm]
        exact hfrontier
      by_cases htape : index = Work.tapeIndex
      · subst index
        simpa [caseReadStartValues, Work.available, Work.tapeIndex,
          Work.symbolIndex] using htapeIndices count (by omega)
      by_cases hsymbol : index = Work.symbolIndex
      · subst index
        simpa [caseReadStartValues, Work.available, Work.tapeIndex,
          Work.symbolIndex] using hsymbolIndices count (by omega)
      · simpa [caseReadStartValues, Function.update_apply, havailable,
          htape, hsymbol] using hvalues index

private theorem emitCaseMembers_spaceBoundByWidthAt
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hinputSymbol : inputSymbolIndex < 4)
    (houtputSymbol : outputSymbolIndex < 4)
    (hworkSymbols : ∀ index, index < workCount →
      workSymbolIndexAt index < 4)
    (htapeBound : ∀ inputLength,
      workCount + 1 ≤ width inputLength)
    (hsymbolBound : ∀ inputLength, 4 ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue ≤
        width inputLength)
    (hstateCap : ∀ inputLength,
      transitionStateRef (values inputLength Work.configBase) stateIndex ≤
        width inputLength)
    (hheadCap : ∀ inputLength tapeIndex position,
      tapeIndex ≤ workCount + 1 →
      position ≤ values inputLength Work.horizon →
        transitionHeadRef stateCount
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position +
            tapeIndex + values inputLength Work.horizon + 1 ≤
          width inputLength)
    (hcellCap : ∀ inputLength tapeIndex symbolIndex position,
      tapeIndex ≤ workCount + 1 → symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        transitionCellRef stateCount (workCount + 2)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position
              symbolIndex +
            (tapeIndex * (values inputLength Work.horizon + 2) +
              position) +
            (values inputLength Work.horizon + 2) + (workCount + 2) +
            tapeIndex + 4 ≤
          width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitCaseMembers stateCount workCount stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt)
      initialSpace values width := by
  let choice := emitCaseChoice choiceValue
  let afterChoice : ℕ → BinaryValues WorkCount := fun inputLength =>
    choice.effect (values inputLength)
  let state := emitStateReference stateIndex false
  let afterState : ℕ → BinaryValues WorkCount := fun inputLength =>
    state.effect (afterChoice inputLength)
  let inputRead := emitCaseRead stateCount workCount 0 inputSymbolIndex
  let afterInput : ℕ → BinaryValues WorkCount := fun inputLength =>
    inputRead.effect (afterState inputLength)
  let workReads := emitCaseReads stateCount workCount workCount 1
    workSymbolIndexAt
  let afterWork : ℕ → BinaryValues WorkCount := fun inputLength =>
    workReads.effect (afterInput inputLength)
  let outputRead := emitCaseRead stateCount workCount (workCount + 1)
    outputSymbolIndex
  have hchoice : BinaryRoutine.SpaceBoundByWidthAt choice initialSpace values
      width := by
    apply emitCaseChoice_spaceBoundByWidthAt
    · intro inputLength
      have := hfrontier inputLength
      simp only [caseFormulaMembersSize] at this
      omega
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · exact fun inputLength => hvalues inputLength Work.reference₁
  have hafterChoiceEffect : ∀ inputLength,
      afterChoice inputLength =
        Function.update (values inputLength) Work.available
          (values inputLength Work.available +
            caseChoiceLiteralSize choiceValue) := by
    intro inputLength
    exact emitCaseChoice_effect_internal choiceValue (values inputLength)
      (hclean inputLength).reference₀ (hclean inputLength).reference₁
  have hafterChoiceValues : ∀ inputLength index,
      afterChoice inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hafterChoiceEffect inputLength]
    apply BinaryRoutine.values_update_le Work.available
    · exact hvalues inputLength
    · have := hfrontier inputLength
      simp only [caseFormulaMembersSize] at this
      omega
  have hafterChoiceClean : ∀ inputLength,
      ReadFormulaClean (afterChoice inputLength) := by
    intro inputLength
    rw [hafterChoiceEffect inputLength]
    exact ReadFormulaClean.updateAvailable _ _
      (hclean inputLength).toReadFormulaClean
  have hstate : BinaryRoutine.SpaceBoundByWidthAt state initialSpace
      afterChoice width := by
    apply emitStateReference_spaceBoundByWidth stateIndex false
    · exact hafterChoiceValues
    · intro inputLength
      rw [hafterChoiceEffect inputLength]
      simpa [Work.available, Work.configBase] using hstateCap inputLength
  have hafterStateEffect : ∀ inputLength,
      afterState inputLength =
        Function.update
          (Function.update (afterChoice inputLength) Work.available
            (afterChoice inputLength Work.available + 1)) Work.reference₀
          0 := by
    intro inputLength
    exact emitStateReference_effect stateIndex false (afterChoice inputLength)
  have hafterStateValues : ∀ inputLength index,
      afterState inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hafterStateEffect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₀
    · apply BinaryRoutine.values_update_le Work.available
      · exact hafterChoiceValues inputLength
      · rw [hafterChoiceEffect inputLength]
        simp only [Function.update_self]
        have := hfrontier inputLength
        simp only [caseFormulaMembersSize] at this
        omega
    · exact Nat.zero_le _
  have hafterStateClean : ∀ inputLength,
      ReadFormulaClean (afterState inputLength) := by
    intro inputLength
    rw [hafterStateEffect inputLength]
    exact ReadFormulaClean.updateReference₀Zero _
      (ReadFormulaClean.updateAvailable _ _
        (hafterChoiceClean inputLength))
  have hafterStateAvailable : ∀ inputLength,
      afterState inputLength Work.available =
        values inputLength Work.available +
          caseChoiceLiteralSize choiceValue + 1 := by
    intro inputLength
    rw [hafterStateEffect inputLength, hafterChoiceEffect inputLength]
    simp [Work.available, Work.reference₀]
  have hafterStateHorizon : ∀ inputLength,
      afterState inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    rw [hafterStateEffect inputLength, hafterChoiceEffect inputLength]
    simp [Work.available, Work.reference₀, Work.horizon]
  have hafterStateConfig : ∀ inputLength,
      afterState inputLength Work.configBase =
        values inputLength Work.configBase := by
    intro inputLength
    rw [hafterStateEffect inputLength, hafterChoiceEffect inputLength]
    simp [Work.available, Work.reference₀, Work.configBase]
  have hinputRead : BinaryRoutine.SpaceBoundByWidthAt inputRead initialSpace
      afterState width := by
    apply emitCaseRead_spaceBoundByWidthAt
    · exact hafterStateClean
    · exact hafterStateValues
    · intro inputLength
      exact Nat.zero_le _
    · intro inputLength
      exact (Nat.le_of_lt hinputSymbol).trans (hsymbolBound inputLength)
    · intro inputLength
      rw [hafterStateAvailable inputLength, hafterStateHorizon inputLength]
      have hbound := hfrontier inputLength
      simp only [caseFormulaMembersSize] at hbound
      have hread : caseReadSize (values inputLength Work.horizon) ≤
          (workCount + 2) *
            caseReadSize (values inputLength Work.horizon) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · intro inputLength position hposition
      rw [hafterStateHorizon inputLength] at hposition
      rw [hafterStateHorizon inputLength, hafterStateConfig inputLength]
      exact hheadCap inputLength 0 position (by omega) hposition
    · intro inputLength position hposition
      rw [hafterStateHorizon inputLength] at hposition
      rw [hafterStateHorizon inputLength, hafterStateConfig inputLength]
      exact hcellCap inputLength 0 inputSymbolIndex position (by omega)
        hinputSymbol hposition
  have hafterInputClean : ∀ inputLength,
      ReadFormulaClean (afterInput inputLength) := by
    intro inputLength
    exact emitCaseRead_preservesClean stateCount workCount 0 inputSymbolIndex
      (afterState inputLength) (hafterStateClean inputLength)
  have hafterInputValues : ∀ inputLength index,
      afterInput inputLength index ≤ width inputLength := by
    intro inputLength
    apply emitCaseRead_effect_values_le stateCount workCount 0
      inputSymbolIndex (hafterStateClean inputLength)
      (hafterStateValues inputLength) (Nat.zero_le _)
      ((Nat.le_of_lt hinputSymbol).trans (hsymbolBound inputLength))
    rw [hafterStateAvailable inputLength, hafterStateHorizon inputLength]
    have hbound := hfrontier inputLength
    simp only [caseFormulaMembersSize] at hbound
    have hread : caseReadSize (values inputLength Work.horizon) ≤
        (workCount + 2) * caseReadSize (values inputLength Work.horizon) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hafterInputEffect : ∀ inputLength,
      afterInput inputLength =
        Function.update
          (caseReadStartValues (afterState inputLength) 0 inputSymbolIndex)
          Work.available
          (afterState inputLength Work.available +
            caseReadSize (afterState inputLength Work.horizon)) := by
    intro inputLength
    exact emitCaseRead_effect_internal stateCount workCount 0
      inputSymbolIndex (afterState inputLength) (hafterStateClean inputLength)
  have hafterInputAvailable : ∀ inputLength,
      afterInput inputLength Work.available =
        values inputLength Work.available +
          caseChoiceLiteralSize choiceValue + 1 +
          caseReadSize (values inputLength Work.horizon) := by
    intro inputLength
    rw [hafterInputEffect inputLength]
    simp only [Function.update_self]
    rw [hafterStateAvailable inputLength, hafterStateHorizon inputLength]
  have hafterInputHorizon : ∀ inputLength,
      afterInput inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    rw [hafterInputEffect inputLength]
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.horizon ≠ Work.available)]
    unfold caseReadStartValues
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.horizon ≠ Work.symbolIndex),
      ite_eq_right (by decide : Work.horizon ≠ Work.tapeIndex)]
    exact hafterStateHorizon inputLength
  have hafterInputConfig : ∀ inputLength,
      afterInput inputLength Work.configBase =
        values inputLength Work.configBase := by
    intro inputLength
    rw [hafterInputEffect inputLength]
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.configBase ≠ Work.available)]
    unfold caseReadStartValues
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.configBase ≠ Work.symbolIndex),
      ite_eq_right (by decide : Work.configBase ≠ Work.tapeIndex)]
    exact hafterStateConfig inputLength
  have hworkFrontier : ∀ inputLength,
      afterInput inputLength Work.available +
          workCount * caseReadSize (afterInput inputLength Work.horizon) ≤
        width inputLength := by
    intro inputLength
    rw [hafterInputAvailable inputLength, hafterInputHorizon inputLength]
    have hbound := hfrontier inputLength
    have hsplit : (workCount + 2) *
          caseReadSize (values inputLength Work.horizon) =
        caseReadSize (values inputLength Work.horizon) +
          workCount * caseReadSize (values inputLength Work.horizon) +
          caseReadSize (values inputLength Work.horizon) := by ring
    rw [caseFormulaMembersSize, hsplit] at hbound
    omega
  have hworkReads : BinaryRoutine.SpaceBoundByWidthAt workReads initialSpace
      afterInput width := by
    apply emitCaseReads_spaceBoundByWidthAt
    · exact hafterInputClean
    · exact hafterInputValues
    · intro inputLength index hindex
      exact (show 1 + index ≤ workCount + 1 by omega).trans
        (htapeBound inputLength)
    · intro inputLength index hindex
      exact (Nat.le_of_lt (hworkSymbols index hindex)).trans
        (hsymbolBound inputLength)
    · intro inputLength
      exact hworkFrontier inputLength
    · intro inputLength index hindex position hposition
      rw [hafterInputHorizon inputLength] at hposition
      rw [hafterInputHorizon inputLength, hafterInputConfig inputLength]
      exact hheadCap inputLength (1 + index) position (by omega) hposition
    · intro inputLength index hindex position hposition
      rw [hafterInputHorizon inputLength] at hposition
      rw [hafterInputHorizon inputLength, hafterInputConfig inputLength]
      exact hcellCap inputLength (1 + index) (workSymbolIndexAt index)
        position (by omega) (hworkSymbols index hindex) hposition
  have hafterWorkClean : ∀ inputLength,
      ReadFormulaClean (afterWork inputLength) := by
    intro inputLength
    exact emitCaseReads_preservesClean stateCount workCount workCount 1
      workSymbolIndexAt (afterInput inputLength) (hafterInputClean inputLength)
  have hafterWorkValues : ∀ inputLength index,
      afterWork inputLength index ≤ width inputLength := by
    intro inputLength
    apply emitCaseReads_effect_values_le stateCount workCount workCount 1
      workSymbolIndexAt (hafterInputClean inputLength)
      (hafterInputValues inputLength)
    · intro index hindex
      exact (show 1 + index ≤ workCount + 1 by omega).trans
        (htapeBound inputLength)
    · intro index hindex
      exact (Nat.le_of_lt (hworkSymbols index hindex)).trans
        (hsymbolBound inputLength)
    · exact hworkFrontier inputLength
  have hafterWorkAvailable : ∀ inputLength,
      afterWork inputLength Work.available =
        afterInput inputLength Work.available +
          workCount * caseReadSize (afterInput inputLength Work.horizon) := by
    intro inputLength
    change (emitCaseReads stateCount workCount workCount 1
      workSymbolIndexAt).effect (afterInput inputLength) Work.available = _
    cases workCount with
    | zero =>
        rw [emitIndexedCaseReads_effect_zero]
        simp
    | succ workCount =>
        rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
          workCount 1 workSymbolIndexAt (afterInput inputLength)
          (hafterInputClean inputLength)]
        simp [caseReadStartValues, Work.available, Work.tapeIndex,
          Work.symbolIndex, Nat.succ_mul, Nat.mul_comm]
  have hafterWorkHorizon : ∀ inputLength,
      afterWork inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    change (emitCaseReads stateCount workCount workCount 1
      workSymbolIndexAt).effect (afterInput inputLength) Work.horizon = _
    cases workCount with
    | zero =>
        rw [emitIndexedCaseReads_effect_zero]
        exact hafterInputHorizon inputLength
    | succ workCount =>
        rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
          workCount 1 workSymbolIndexAt (afterInput inputLength)
          (hafterInputClean inputLength)]
        simpa [caseReadStartValues, Work.available, Work.horizon,
          Work.tapeIndex, Work.symbolIndex] using
            hafterInputHorizon inputLength
  have hafterWorkConfig : ∀ inputLength,
      afterWork inputLength Work.configBase =
        values inputLength Work.configBase := by
    intro inputLength
    change (emitCaseReads stateCount workCount workCount 1
      workSymbolIndexAt).effect (afterInput inputLength) Work.configBase = _
    cases workCount with
    | zero =>
        rw [emitIndexedCaseReads_effect_zero]
        exact hafterInputConfig inputLength
    | succ workCount =>
        rw [emitIndexedCaseReads_effect_succ stateCount (workCount + 1)
          workCount 1 workSymbolIndexAt (afterInput inputLength)
          (hafterInputClean inputLength)]
        simpa [caseReadStartValues, Work.available, Work.configBase,
          Work.tapeIndex, Work.symbolIndex] using
            hafterInputConfig inputLength
  have houtputRead : BinaryRoutine.SpaceBoundByWidthAt outputRead initialSpace
      afterWork width := by
    apply emitCaseRead_spaceBoundByWidthAt
    · exact hafterWorkClean
    · exact hafterWorkValues
    · exact htapeBound
    · intro inputLength
      exact (Nat.le_of_lt houtputSymbol).trans (hsymbolBound inputLength)
    · intro inputLength
      rw [hafterWorkAvailable inputLength, hafterWorkHorizon inputLength,
        hafterInputAvailable inputLength, hafterInputHorizon inputLength]
      have hbound := hfrontier inputLength
      have hsplit : (workCount + 2) *
            caseReadSize (values inputLength Work.horizon) =
          caseReadSize (values inputLength Work.horizon) +
            workCount * caseReadSize (values inputLength Work.horizon) +
            caseReadSize (values inputLength Work.horizon) := by ring
      rw [caseFormulaMembersSize, hsplit] at hbound
      omega
    · intro inputLength position hposition
      rw [hafterWorkHorizon inputLength] at hposition
      rw [hafterWorkHorizon inputLength, hafterWorkConfig inputLength]
      exact hheadCap inputLength (workCount + 1) position (by omega) hposition
    · intro inputLength position hposition
      rw [hafterWorkHorizon inputLength] at hposition
      rw [hafterWorkHorizon inputLength, hafterWorkConfig inputLength]
      exact hcellCap inputLength (workCount + 1) outputSymbolIndex position
        (by omega) houtputSymbol hposition
  unfold emitCaseMembers
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · exact hchoice
  constructor
  · exact hstate
  constructor
  · exact hinputRead
  constructor
  · exact hworkReads
  constructor
  · exact houtputRead
  · trivial

private theorem prepareCaseReadSize_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt prepareCaseReadSize initialSpace values
      width := by
  let setFive := BinaryRoutine.set Work.temporary₃ 5
  let setFour := BinaryRoutine.set Work.temporary₂ 4
  let multiply := BinaryRoutine.mulAdd Work.horizon Work.temporary₂
    Work.temporary₃ Work.multiplyCounter Work.addCounter
  let clear := BinaryRoutine.clear Work.temporary₂
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    setFive.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    setFour.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    multiply.effect (values₂ inputLength)
  have hvalues₂Horizon : ∀ inputLength,
      values₂ inputLength Work.horizon =
        values inputLength Work.horizon := by
    intro inputLength
    simp [values₂, values₁, setFour, setFive,
      BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, Work.horizon, Work.temporary₂,
      Work.temporary₃]
  have hsetFive : BinaryRoutine.SpaceBoundByWidthAt setFive initialSpace
      values width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.temporary₃ 5
    · exact fun inputLength => hvalues inputLength Work.temporary₃
    · intro inputLength
      have := hcap inputLength
      simp [caseReadSize] at this
      omega
  have hsetFour : BinaryRoutine.SpaceBoundByWidthAt setFour initialSpace
      values₁ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.temporary₂ 4
    · intro inputLength
      simpa [values₁, setFive, BinaryRoutine.set, BinaryRoutine.seq,
        BinaryRoutine.clear, BinaryRoutine.addConst, Work.temporary₂,
        Work.temporary₃] using hvalues inputLength Work.temporary₂
    · intro inputLength
      have := hcap inputLength
      simp [caseReadSize] at this
      omega
  have hmultiply : BinaryRoutine.SpaceBoundByWidthAt multiply initialSpace
      values₂ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd Work.horizon
      Work.temporary₂ Work.temporary₃ Work.multiplyCounter
      Work.addCounter
    · intro inputLength
      simpa [values₂, values₁, setFour, setFive,
        BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.horizon, Work.temporary₂,
        Work.temporary₃] using hvalues inputLength Work.horizon
    · intro inputLength
      simp [values₂, values₁, setFour, setFive,
        BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.temporary₂, Work.temporary₃]
      have := hcap inputLength
      simp [caseReadSize] at this
      omega
    · intro inputLength
      rw [hvalues₂Horizon inputLength]
      simp [values₂, values₁, setFour, setFive,
        BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.temporary₂,
        Work.temporary₃]
      have := hcap inputLength
      simp [caseReadSize] at this ⊢
      omega
  have hclear : BinaryRoutine.SpaceBoundByWidthAt clear initialSpace values₃
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₂
    intro inputLength
    simp [values₃, values₂, values₁, multiply, setFour, setFive,
      BinaryRoutine.mulAdd, BinaryRoutine.set, BinaryRoutine.seq,
      BinaryRoutine.clear, BinaryRoutine.addConst, Work.horizon,
      Work.temporary₂, Work.temporary₃]
    have := hcap inputLength
    simp [caseReadSize] at this
    omega
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength => clear.effect (values₃ inputLength)) width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hsetFive
    (BinaryRoutine.SpaceBoundByWidthAt.seq hsetFour
      (BinaryRoutine.SpaceBoundByWidthAt.seq hmultiply
        (BinaryRoutine.SpaceBoundByWidthAt.seq hclear hid)))
  simpa [prepareCaseReadSize, BinaryRoutine.seqList, setFive, setFour,
    multiply, clear, values₁, values₂, values₃] using hroutine

private theorem emitCaseConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitCaseConnector initialSpace values
      width := by
  let prepare := prepareRecentReference Work.reference₁ 1
  let emit := BinaryRoutine.emitRawGateStep .and false false
    Work.emitCounter Work.available Work.reference₀ Work.reference₁
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (values₁ inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width := by
    apply prepareRecentReference_spaceBoundByWidth Work.reference₁ 1
    · intro inputLength
      have := havailable inputLength
      omega
    · exact hreference₁
    · exact havailablePositive
  have hvalues₁Available : ∀ inputLength,
      values₁ inputLength Work.available ≤ width inputLength := by
    intro inputLength
    have hbase : values inputLength Work.available ≤ width inputLength := by
      have := havailable inputLength
      omega
    simpa [values₁, prepare, prepareRecentReference_effect,
      show Work.available ≠ Work.reference₁ by decide] using hbase
  have hvalues₁Reference₀ : ∀ inputLength,
      values₁ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare, prepareRecentReference_effect,
      Work.reference₀, Work.reference₁] using
        hreference₀ inputLength
  have hvalues₁Reference₁ : ∀ inputLength,
      values₁ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simp [values₁, prepare, prepareRecentReference_effect,
      Work.reference₁]
    have := havailable inputLength
    omega
  have hemit : BinaryRoutine.SpaceBoundByWidthAt emit initialSpace values₁
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .and false false
      Work.emitCounter Work.available Work.reference₀ Work.reference₁
      hvalues₁Available hvalues₁Reference₀ hvalues₁Reference₁
  have hvalues₂Reference₁ : ∀ inputLength,
      values₂ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simpa [values₂, emit, BinaryRoutine.emitRawGateStep,
      Work.available, Work.reference₁] using
        hvalues₁Reference₁ inputLength
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₁) initialSpace values₂ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₁
      hvalues₂Reference₁
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength =>
        (BinaryRoutine.clear Work.reference₁).effect
          (values₂ inputLength)) width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hprepare
    (BinaryRoutine.SpaceBoundByWidthAt.seq hemit
      (BinaryRoutine.SpaceBoundByWidthAt.seq hclear hid))
  simpa [emitCaseConnector, BinaryRoutine.seqList, prepare, emit, values₁,
    values₂] using hroutine

private theorem emitPreviousCaseReadConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hloop : ∀ inputLength, values inputLength Work.loop₃ = 0)
    (hfit : ∀ inputLength,
      values inputLength Work.temporary₃ ≤
        values inputLength Work.reference₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hoffset : ∀ inputLength,
      values inputLength Work.temporary₃ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitPreviousCaseReadConnector
      initialSpace values width := by
  let decrement := decrementReferenceBy Work.reference₀ Work.temporary₃
    Work.loop₃
  let decremented : ℕ → BinaryValues WorkCount := fun inputLength =>
    decrement.effect (values inputLength)
  have hdecrement : BinaryRoutine.SpaceBoundByWidthAt decrement initialSpace
      values width := by
    apply decrementReferenceBy_spaceBoundByWidth Work.reference₀
      Work.temporary₃ Work.loop₃ ⟨by decide, by decide, by decide⟩
    · intro inputLength
      rw [hloop inputLength]
      omega
    · intro inputLength
      rw [hloop inputLength]
      simpa using hfit inputLength
    · exact hreference₀
    · exact hoffset
  have hconnector : BinaryRoutine.SpaceBoundByWidthAt emitCaseConnector
      initialSpace decremented width := by
    apply emitCaseConnector_spaceBoundByWidthAt
    · intro inputLength
      rw [show decremented inputLength =
          Function.update
            (Function.update (values inputLength) Work.reference₀
              (values inputLength Work.reference₀ -
                values inputLength Work.temporary₃)) Work.loop₃ 0 by
        exact decrementReferenceBy_effect Work.reference₀ Work.temporary₃
          Work.loop₃ (values inputLength)
            ⟨by decide, by decide, by decide⟩ (hloop inputLength)]
      simpa [Work.reference₀, Work.loop₃, Work.available] using
        havailable inputLength
    · intro inputLength
      rw [show decremented inputLength =
          Function.update
            (Function.update (values inputLength) Work.reference₀
              (values inputLength Work.reference₀ -
                values inputLength Work.temporary₃)) Work.loop₃ 0 by
        exact decrementReferenceBy_effect Work.reference₀ Work.temporary₃
          Work.loop₃ (values inputLength)
            ⟨by decide, by decide, by decide⟩ (hloop inputLength)]
      simpa [Work.reference₀, Work.loop₃, Work.available] using
        havailablePositive inputLength
    · intro inputLength
      rw [show decremented inputLength =
          Function.update
            (Function.update (values inputLength) Work.reference₀
              (values inputLength Work.reference₀ -
                values inputLength Work.temporary₃)) Work.loop₃ 0 by
        exact decrementReferenceBy_effect Work.reference₀ Work.temporary₃
          Work.loop₃ (values inputLength)
            ⟨by decide, by decide, by decide⟩ (hloop inputLength)]
      simp only [Function.update_apply]
      rw [ite_eq_right (by decide : Work.reference₀ ≠ Work.loop₃), ite_true]
      exact (Nat.sub_le _ _).trans (hreference₀ inputLength)
    · intro inputLength
      rw [show decremented inputLength =
          Function.update
            (Function.update (values inputLength) Work.reference₀
              (values inputLength Work.reference₀ -
                values inputLength Work.temporary₃)) Work.loop₃ 0 by
        exact decrementReferenceBy_effect Work.reference₀ Work.temporary₃
          Work.loop₃ (values inputLength)
            ⟨by decide, by decide, by decide⟩ (hloop inputLength)]
      simpa [Work.reference₀, Work.reference₁, Work.loop₃] using
        hreference₁ inputLength
  simpa [emitPreviousCaseReadConnector, decrement, decremented] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hdecrement hconnector)

private theorem emitPreviousCaseReadConnectors_spaceBoundByWidthAt
    (count : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hloop : ∀ inputLength, values inputLength Work.loop₃ = 0)
    (hreference₁Zero : ∀ inputLength,
      values inputLength Work.reference₁ = 0)
    (hfit : ∀ inputLength,
      values inputLength Work.temporary₃ * count ≤
        values inputLength Work.reference₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available + count ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hoffset : ∀ inputLength,
      values inputLength Work.temporary₃ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPreviousCaseReadConnectors count) initialSpace values width := by
  induction count generalizing values with
  | zero => exact BinaryRoutine.SpaceBoundByWidthAt.identity
  | succ count ih =>
      let head := emitPreviousCaseReadConnector
      let current : ℕ → BinaryValues WorkCount := fun inputLength =>
        head.effect (values inputLength)
      have hhead : BinaryRoutine.SpaceBoundByWidthAt head initialSpace values
          width := by
        apply emitPreviousCaseReadConnector_spaceBoundByWidthAt
        · exact hloop
        · intro inputLength
          have hfit' := hfit inputLength
          simp only [Nat.mul_succ] at hfit'
          omega
        · intro inputLength
          have := havailable inputLength
          omega
        · exact havailablePositive
        · exact hreference₀
        · intro inputLength
          rw [hreference₁Zero inputLength]
          exact Nat.zero_le _
        · exact hoffset
      have hcurrentEffect : ∀ inputLength,
          current inputLength =
            Function.update
              (Function.update
                (Function.update (values inputLength) Work.reference₀
                  (values inputLength Work.reference₀ -
                    values inputLength Work.temporary₃)) Work.available
                (values inputLength Work.available + 1)) Work.reference₁
              0 := by
        intro inputLength
        exact emitPreviousCaseReadConnector_effect_internal
          (values inputLength) (hloop inputLength)
      have hcurrentLoop : ∀ inputLength,
          current inputLength Work.loop₃ = 0 := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simpa [Work.reference₀, Work.available, Work.reference₁,
          Work.loop₃] using hloop inputLength
      have hcurrentReference₁ : ∀ inputLength,
          current inputLength Work.reference₁ = 0 := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₁]
      have hcurrentOffset : ∀ inputLength,
          current inputLength Work.temporary₃ =
            values inputLength Work.temporary₃ := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₀, Work.available, Work.reference₁,
          Work.temporary₃]
      have hcurrentReference₀ : ∀ inputLength,
          current inputLength Work.reference₀ =
            values inputLength Work.reference₀ -
              values inputLength Work.temporary₃ := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₀, Work.available, Work.reference₁]
      have hcurrentAvailable : ∀ inputLength,
          current inputLength Work.available =
            values inputLength Work.available + 1 := by
        intro inputLength
        rw [hcurrentEffect inputLength]
        simp [Work.reference₀, Work.available, Work.reference₁]
      have htail : BinaryRoutine.SpaceBoundByWidthAt
          (emitPreviousCaseReadConnectors count) initialSpace current width := by
        apply ih
        · exact hcurrentLoop
        · exact hcurrentReference₁
        · intro inputLength
          rw [hcurrentOffset inputLength, hcurrentReference₀ inputLength]
          have hfit' := hfit inputLength
          simp only [Nat.mul_succ] at hfit'
          omega
        · intro inputLength
          rw [hcurrentAvailable inputLength]
          have := havailable inputLength
          omega
        · intro inputLength
          rw [hcurrentAvailable inputLength]
          omega
        · intro inputLength
          rw [hcurrentReference₀ inputLength]
          exact (Nat.sub_le _ _).trans (hreference₀ inputLength)
        · intro inputLength
          rw [hcurrentOffset inputLength]
          exact hoffset inputLength
      simpa [emitPreviousCaseReadConnectors, head, current] using
        (BinaryRoutine.SpaceBoundByWidthAt.seq hhead htail)

private theorem emitPreviousCaseChoiceConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hreferencePositive : ∀ inputLength,
      1 ≤ values inputLength Work.reference₀)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 1 ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt emitPreviousCaseChoiceConnector
      initialSpace values width := by
  let pred := BinaryRoutine.binaryPred Work.reference₀
  let current : ℕ → BinaryValues WorkCount := fun inputLength =>
    pred.effect (values inputLength)
  have hpred : BinaryRoutine.SpaceBoundByWidthAt pred initialSpace values
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred Work.reference₀
    intro inputLength
    have hlower := hreferencePositive inputLength
    have hupper := hreference₀ inputLength
    omega
  have hconnector : BinaryRoutine.SpaceBoundByWidthAt emitCaseConnector
      initialSpace current width := by
    apply emitCaseConnector_spaceBoundByWidthAt
    · intro inputLength
      change values inputLength Work.available + 1 ≤ width inputLength
      exact havailable inputLength
    · intro inputLength
      change 1 ≤ values inputLength Work.available
      exact havailablePositive inputLength
    · intro inputLength
      change values inputLength Work.reference₀ - 1 ≤ width inputLength
      exact (Nat.sub_le _ _).trans (hreference₀ inputLength)
    · intro inputLength
      change values inputLength Work.reference₁ ≤ width inputLength
      exact hreference₁ inputLength
  simpa [emitPreviousCaseChoiceConnector, pred, current] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hpred hconnector)

theorem emitCaseFormula_spaceBoundByWidth_internal
    (stateCount workCount stateIndex inputSymbolIndex outputSymbolIndex : ℕ)
    (choiceValue : Bool) (workSymbolIndexAt : ℕ → ℕ)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, CaseFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hinputSymbol : inputSymbolIndex < 4)
    (houtputSymbol : outputSymbolIndex < 4)
    (hworkSymbols : ∀ index, index < workCount →
      workSymbolIndexAt index < 4)
    (hcap : ∀ inputLength tapeIndex symbolIndex position,
      tapeIndex ≤ workCount + 1 → symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        values inputLength Work.available +
            caseFormulaScheduleSize workCount
              (values inputLength Work.horizon) choiceValue +
          transitionStateRef (values inputLength Work.configBase)
            stateIndex +
          (transitionHeadRef stateCount
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position +
              tapeIndex + values inputLength Work.horizon + 1) +
          (transitionCellRef stateCount (workCount + 2)
                (values inputLength Work.horizon)
                (values inputLength Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (values inputLength Work.horizon + 2) +
                position) +
              (values inputLength Work.horizon + 2) + (workCount + 2) +
              tapeIndex + 4) +
          caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitCaseFormula stateCount workCount stateIndex inputSymbolIndex
        outputSymbolIndex choiceValue workSymbolIndexAt)
      initialSpace values width := by
  have hcapZero (inputLength : ℕ) :=
    hcap inputLength 0 0 0 (by omega) (by omega) (Nat.zero_le _)
  have htapeBound : ∀ inputLength,
      workCount + 1 ≤ width inputLength := by
    intro inputLength
    have hbound := hcap inputLength (workCount + 1) 0 0 (by omega)
      (by omega) (Nat.zero_le _)
    omega
  have hsymbolBound : ∀ inputLength, 4 ≤ width inputLength := by
    intro inputLength
    have hbound := hcapZero inputLength
    omega
  have hfrontier : ∀ inputLength,
      values inputLength Work.available +
          caseFormulaScheduleSize workCount
            (values inputLength Work.horizon) choiceValue ≤
        width inputLength := by
    intro inputLength
    have hbound := hcapZero inputLength
    omega
  have hmembersFrontier : ∀ inputLength,
      values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue ≤
        width inputLength := by
    intro inputLength
    have hbound := hfrontier inputLength
    simp only [caseFormulaScheduleSize] at hbound
    omega
  have hstateCap : ∀ inputLength,
      transitionStateRef (values inputLength Work.configBase) stateIndex ≤
        width inputLength := by
    intro inputLength
    have hbound := hcapZero inputLength
    omega
  have hheadCap : ∀ inputLength tapeIndex position,
      tapeIndex ≤ workCount + 1 →
      position ≤ values inputLength Work.horizon →
        transitionHeadRef stateCount
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position +
            tapeIndex + values inputLength Work.horizon + 1 ≤
          width inputLength := by
    intro inputLength tapeIndex position htape hposition
    have hbound := hcap inputLength tapeIndex 0 position htape (by omega)
      hposition
    omega
  have hcellCap : ∀ inputLength tapeIndex symbolIndex position,
      tapeIndex ≤ workCount + 1 → symbolIndex < 4 →
      position ≤ values inputLength Work.horizon →
        transitionCellRef stateCount (workCount + 2)
              (values inputLength Work.horizon)
              (values inputLength Work.configBase) tapeIndex position
              symbolIndex +
            (tapeIndex * (values inputLength Work.horizon + 2) +
              position) +
            (values inputLength Work.horizon + 2) + (workCount + 2) +
            tapeIndex + 4 ≤
          width inputLength := by
    intro inputLength tapeIndex symbolIndex position htape hsymbol hposition
    have hbound := hcap inputLength tapeIndex symbolIndex position htape
      hsymbol hposition
    omega
  have hreadSizeCap : ∀ inputLength,
      caseReadSize (values inputLength Work.horizon) +
          values inputLength Work.horizon ≤ width inputLength := by
    intro inputLength
    have hbound := hcapZero inputLength
    omega
  let members := emitCaseMembers stateCount workCount stateIndex
    inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    members.effect (values inputLength)
  let constant := emitConstantGate true
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    constant.effect (values₁ inputLength)
  let prepareSize := prepareCaseReadSize
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepareSize.effect (values₂ inputLength)
  let prepareReference := prepareRecentReference Work.reference₀ 2
  let values₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepareReference.effect (values₃ inputLength)
  let connector := emitCaseConnector
  let values₅ : ℕ → BinaryValues WorkCount := fun inputLength =>
    connector.effect (values₄ inputLength)
  let readConnectors := emitPreviousCaseReadConnectors (workCount + 2)
  let values₆ : ℕ → BinaryValues WorkCount := fun inputLength =>
    readConnectors.effect (values₅ inputLength)
  let choiceConnector := emitPreviousCaseChoiceConnector
  let values₇ : ℕ → BinaryValues WorkCount := fun inputLength =>
    choiceConnector.effect (values₆ inputLength)
  have hmembers : BinaryRoutine.SpaceBoundByWidthAt members initialSpace
      values width := by
    apply emitCaseMembers_spaceBoundByWidthAt
    · exact hclean
    · exact hvalues
    · exact hinputSymbol
    · exact houtputSymbol
    · exact hworkSymbols
    · exact htapeBound
    · exact hsymbolBound
    · exact hmembersFrontier
    · exact hstateCap
    · exact hheadCap
    · exact hcellCap
  have hvalues₁Effect : ∀ inputLength,
      values₁ inputLength =
        Function.update
          (caseReadStartValues (values inputLength) (workCount + 1)
            outputSymbolIndex) Work.available
          (values inputLength Work.available +
            caseFormulaMembersSize workCount
              (values inputLength Work.horizon) choiceValue) := by
    intro inputLength
    exact emitCaseMembers_effect_internal stateCount workCount stateIndex
      inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
      (values inputLength) (hclean inputLength)
  have hvalues₁Available : ∀ inputLength,
      values₁ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue := by
    intro inputLength
    rw [hvalues₁Effect inputLength]
    simp [caseReadStartValues, Work.available, Work.tapeIndex,
      Work.symbolIndex]
  have hvalues₁Horizon : ∀ inputLength,
      values₁ inputLength Work.horizon = values inputLength Work.horizon := by
    intro inputLength
    rw [hvalues₁Effect inputLength]
    simp [caseReadStartValues, Work.available, Work.horizon,
      Work.tapeIndex, Work.symbolIndex]
  have hvalues₁Reference₀ : ∀ inputLength,
      values₁ inputLength Work.reference₀ = 0 := by
    intro inputLength
    rw [hvalues₁Effect inputLength]
    simpa [caseReadStartValues, Work.available, Work.reference₀,
      Work.tapeIndex, Work.symbolIndex] using (hclean inputLength).reference₀
  have hvalues₁Values : ∀ inputLength index,
      values₁ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₁Effect inputLength]
    apply BinaryRoutine.values_update_le Work.available
    · unfold caseReadStartValues
      apply BinaryRoutine.values_update_le Work.symbolIndex
      · apply BinaryRoutine.values_update_le Work.tapeIndex
        · exact hvalues inputLength
        · exact htapeBound inputLength
      · exact (Nat.le_of_lt houtputSymbol).trans
          (hsymbolBound inputLength)
    · exact hmembersFrontier inputLength
  have hconstant : BinaryRoutine.SpaceBoundByWidthAt constant initialSpace
      values₁ width := by
    apply emitConstantGate_spaceBoundByWidth true
    · exact fun inputLength => hvalues₁Values inputLength Work.available
    · intro inputLength
      rw [hvalues₁Reference₀ inputLength]
      exact Nat.zero_le _
  have hvalues₂Effect : ∀ inputLength,
      values₂ inputLength =
        Function.update (values₁ inputLength) Work.available
          (values₁ inputLength Work.available + 1) := by
    intro inputLength
    exact emitConstantGate_effect_internal true (values₁ inputLength)
  have hvalues₂Available : ∀ inputLength,
      values₂ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue + 1 := by
    intro inputLength
    rw [hvalues₂Effect inputLength, hvalues₁Available inputLength]
    simp
  have hvalues₂Horizon : ∀ inputLength,
      values₂ inputLength Work.horizon = values inputLength Work.horizon := by
    intro inputLength
    rw [hvalues₂Effect inputLength]
    simpa [Work.available, Work.horizon] using hvalues₁Horizon inputLength
  have hvalues₂Values : ∀ inputLength index,
      values₂ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₂Effect inputLength]
    apply BinaryRoutine.values_update_le Work.available
    · exact hvalues₁Values inputLength
    · rw [hvalues₁Available inputLength]
      have hbound := hfrontier inputLength
      simp only [caseFormulaScheduleSize] at hbound
      omega
  have hprepareSize : BinaryRoutine.SpaceBoundByWidthAt prepareSize
      initialSpace values₂ width := by
    apply prepareCaseReadSize_spaceBoundByWidthAt
    · exact hvalues₂Values
    · intro inputLength
      rw [hvalues₂Horizon inputLength]
      exact hreadSizeCap inputLength
  have hvalues₃Effect : ∀ inputLength,
      values₃ inputLength =
        Function.update
          (Function.update (values₂ inputLength) Work.temporary₃
            (caseReadSize (values₂ inputLength Work.horizon)))
          Work.temporary₂ 0 := by
    intro inputLength
    exact prepareCaseReadSize_effect_internal (values₂ inputLength)
  have hvalues₃Available : ∀ inputLength,
      values₃ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue + 1 := by
    intro inputLength
    rw [hvalues₃Effect inputLength]
    simpa [Work.temporary₂, Work.temporary₃, Work.available] using
      hvalues₂Available inputLength
  have hvalues₃Horizon : ∀ inputLength,
      values₃ inputLength Work.horizon = values inputLength Work.horizon := by
    intro inputLength
    rw [hvalues₃Effect inputLength]
    simpa [Work.temporary₂, Work.temporary₃, Work.horizon] using
      hvalues₂Horizon inputLength
  have hvalues₃Values : ∀ inputLength index,
      values₃ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₃Effect inputLength]
    apply BinaryRoutine.values_update_le Work.temporary₂
    · apply BinaryRoutine.values_update_le Work.temporary₃
      · exact hvalues₂Values inputLength
      · rw [hvalues₂Horizon inputLength]
        have := hreadSizeCap inputLength
        omega
    · exact Nat.zero_le _
  have hprepareReference : BinaryRoutine.SpaceBoundByWidthAt prepareReference
      initialSpace values₃ width := by
    apply prepareRecentReference_spaceBoundByWidth Work.reference₀ 2
    · exact fun inputLength => hvalues₃Values inputLength Work.available
    · exact fun inputLength => hvalues₃Values inputLength Work.reference₀
    · intro inputLength
      rw [hvalues₃Available inputLength]
      unfold caseFormulaMembersSize caseChoiceLiteralSize caseReadSize
      cases choiceValue <;> omega
  have hvalues₄Effect : ∀ inputLength,
      values₄ inputLength =
        Function.update (values₃ inputLength) Work.reference₀
          (values₃ inputLength Work.available - 2) := by
    intro inputLength
    exact prepareRecentReference_effect Work.reference₀ 2
      (values₃ inputLength)
  have hvalues₄Available : ∀ inputLength,
      values₄ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue + 1 := by
    intro inputLength
    rw [hvalues₄Effect inputLength]
    simpa [Work.reference₀, Work.available] using
      hvalues₃Available inputLength
  have hvalues₄Values : ∀ inputLength index,
      values₄ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₄Effect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₀
    · exact hvalues₃Values inputLength
    · exact (Nat.sub_le _ _).trans
        (hvalues₃Values inputLength Work.available)
  have hconnector : BinaryRoutine.SpaceBoundByWidthAt connector initialSpace
      values₄ width := by
    apply emitCaseConnector_spaceBoundByWidthAt
    · intro inputLength
      rw [hvalues₄Available inputLength]
      have hbound := hfrontier inputLength
      simp only [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
      omega
    · intro inputLength
      rw [hvalues₄Available inputLength]
      unfold caseFormulaMembersSize caseChoiceLiteralSize caseReadSize
      cases choiceValue <;> omega
    · exact fun inputLength => hvalues₄Values inputLength Work.reference₀
    · exact fun inputLength => hvalues₄Values inputLength Work.reference₁
  have hvalues₅Effect : ∀ inputLength,
      values₅ inputLength =
        Function.update
          (Function.update (values₄ inputLength) Work.available
            (values₄ inputLength Work.available + 1)) Work.reference₁ 0 := by
    intro inputLength
    exact emitCaseConnector_effect_internal (values₄ inputLength)
  have hvalues₅Values : ∀ inputLength index,
      values₅ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₅Effect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.available
      · exact hvalues₄Values inputLength
      · rw [hvalues₄Available inputLength]
        have hbound := hfrontier inputLength
        simp only [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
        omega
    · exact Nat.zero_le _
  have hvalues₅Start : ∀ inputLength,
      values₅ inputLength =
        caseFormulaConnectorStartValues (values inputLength) workCount
          outputSymbolIndex choiceValue := by
    intro inputLength
    simpa [values₅, connector, values₄, prepareReference, values₃,
      prepareSize, values₂, constant, values₁, members] using
      (caseFormulaConnectorStart_effect stateCount workCount stateIndex
        inputSymbolIndex outputSymbolIndex choiceValue workSymbolIndexAt
        (values inputLength) (hclean inputLength))
  have hvalues₅Loop : ∀ inputLength,
      values₅ inputLength Work.loop₃ = 0 := by
    intro inputLength
    rw [hvalues₅Start inputLength]
    simpa [caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex, Work.loop₃] using (hclean inputLength).loop₃
  have hvalues₅Reference₁ : ∀ inputLength,
      values₅ inputLength Work.reference₁ = 0 := by
    intro inputLength
    rw [hvalues₅Start inputLength]
    simp [caseFormulaConnectorStartValues, Work.reference₁]
  have hvalues₅Available : ∀ inputLength,
      values₅ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue + 2 := by
    intro inputLength
    rw [hvalues₅Start inputLength]
    simp [caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hvalues₅Reference₀ : ∀ inputLength,
      values₅ inputLength Work.reference₀ =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue - 1 := by
    intro inputLength
    rw [hvalues₅Start inputLength]
    simp [caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hvalues₅Offset : ∀ inputLength,
      values₅ inputLength Work.temporary₃ =
        caseReadSize (values inputLength Work.horizon) := by
    intro inputLength
    rw [hvalues₅Start inputLength]
    simp [caseFormulaConnectorStartValues, caseReadStartValues,
      Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₂, Work.temporary₃, Work.tapeIndex,
      Work.symbolIndex]
  have hreadConnectors : BinaryRoutine.SpaceBoundByWidthAt readConnectors
      initialSpace values₅ width := by
    apply emitPreviousCaseReadConnectors_spaceBoundByWidthAt (workCount + 2)
    · exact hvalues₅Loop
    · exact hvalues₅Reference₁
    · intro inputLength
      rw [hvalues₅Offset inputLength, hvalues₅Reference₀ inputLength]
      have hreadFit :
          caseReadSize (values inputLength Work.horizon) * (workCount + 2) ≤
            values inputLength Work.available +
              caseFormulaMembersSize workCount
                (values inputLength Work.horizon) choiceValue - 1 := by
        rw [caseFormulaMembersSize, Nat.mul_comm
          (caseReadSize (values inputLength Work.horizon)) (workCount + 2)]
        cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
      exact hreadFit
    · intro inputLength
      rw [hvalues₅Available inputLength]
      have hbound := hfrontier inputLength
      simp [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
      omega
    · intro inputLength
      rw [hvalues₅Available inputLength]
      omega
    · exact fun inputLength => hvalues₅Values inputLength Work.reference₀
    · exact fun inputLength => hvalues₅Values inputLength Work.temporary₃
  have hvalues₆Effect : ∀ inputLength,
      values₆ inputLength =
        Function.update
          (Function.update
            (Function.update (values₅ inputLength) Work.reference₀
              (values₅ inputLength Work.reference₀ -
                values₅ inputLength Work.temporary₃ *
                  (workCount + 2))) Work.available
            (values₅ inputLength Work.available + (workCount + 2)))
          Work.reference₁ 0 := by
    intro inputLength
    exact emitPreviousCaseReadConnectors_effect (workCount + 2)
      (values₅ inputLength) (hvalues₅Loop inputLength)
      (hvalues₅Reference₁ inputLength)
  have hvalues₆Available : ∀ inputLength,
      values₆ inputLength Work.available =
        values inputLength Work.available +
          caseFormulaMembersSize workCount
            (values inputLength Work.horizon) choiceValue + 2 +
          (workCount + 2) := by
    intro inputLength
    rw [hvalues₆Effect inputLength]
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.available ≠ Work.reference₁), ite_true]
    rw [hvalues₅Available inputLength]
  have hvalues₆Values : ∀ inputLength index,
      values₆ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₆Effect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.available
      · apply BinaryRoutine.values_update_le Work.reference₀
        · exact hvalues₅Values inputLength
        · exact (Nat.sub_le _ _).trans
            (hvalues₅Values inputLength Work.reference₀)
      · rw [hvalues₅Available inputLength]
        have hbound := hfrontier inputLength
        simp [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
        omega
    · exact Nat.zero_le _
  have hvalues₆Remaining : ∀ inputLength,
      values₆ inputLength Work.reference₀ =
        values inputLength Work.available +
          caseChoiceLiteralSize choiceValue := by
    intro inputLength
    rw [hvalues₆Effect inputLength]
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide : Work.reference₀ ≠ Work.reference₁),
      ite_eq_right (by decide : Work.reference₀ ≠ Work.available), ite_true]
    rw [hvalues₅Reference₀ inputLength, hvalues₅Offset inputLength,
      caseFormulaMembersSize, Nat.mul_comm
        (caseReadSize (values inputLength Work.horizon)) (workCount + 2)]
    cases choiceValue <;> simp [caseChoiceLiteralSize] <;> omega
  have hchoiceConnector : BinaryRoutine.SpaceBoundByWidthAt choiceConnector
      initialSpace values₆ width := by
    apply emitPreviousCaseChoiceConnector_spaceBoundByWidthAt
    · intro inputLength
      rw [hvalues₆Remaining inputLength]
      cases choiceValue <;> simp [caseChoiceLiteralSize]
    · exact fun inputLength => hvalues₆Values inputLength Work.reference₀
    · exact fun inputLength => hvalues₆Values inputLength Work.reference₁
    · intro inputLength
      rw [hvalues₆Available inputLength]
      have hbound := hfrontier inputLength
      simp [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
      omega
    · intro inputLength
      rw [hvalues₆Available inputLength]
      omega
  have hvalues₇Effect : ∀ inputLength,
      values₇ inputLength =
        Function.update
          (Function.update
            (Function.update (values₆ inputLength) Work.reference₀
              (values₆ inputLength Work.reference₀ - 1)) Work.available
            (values₆ inputLength Work.available + 1)) Work.reference₁
          0 := by
    intro inputLength
    exact emitPreviousCaseChoiceConnector_effect_internal
      (values₆ inputLength)
  have hvalues₇Values : ∀ inputLength index,
      values₇ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [hvalues₇Effect inputLength]
    apply BinaryRoutine.values_update_le Work.reference₁
    · apply BinaryRoutine.values_update_le Work.available
      · apply BinaryRoutine.values_update_le Work.reference₀
        · exact hvalues₆Values inputLength
        · exact (Nat.sub_le _ _).trans
            (hvalues₆Values inputLength Work.reference₀)
      · rw [hvalues₆Available inputLength]
        have hbound := hfrontier inputLength
        simp [caseFormulaScheduleSize, caseFormulaMemberCount] at hbound
        omega
    · exact Nat.zero_le _
  let clearReference := BinaryRoutine.clear Work.reference₀
  let values₈ : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearReference.effect (values₇ inputLength)
  let clearOffset := BinaryRoutine.clear Work.temporary₃
  let values₉ : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearOffset.effect (values₈ inputLength)
  let clearTape := BinaryRoutine.clear Work.tapeIndex
  let values₁₀ : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearTape.effect (values₉ inputLength)
  let clearSymbol := BinaryRoutine.clear Work.symbolIndex
  let values₁₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    clearSymbol.effect (values₁₀ inputLength)
  have hclearReference : BinaryRoutine.SpaceBoundByWidthAt clearReference
      initialSpace values₇ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₀
      (fun inputLength => hvalues₇Values inputLength Work.reference₀)
  have hvalues₈Values : ∀ inputLength index,
      values₈ inputLength index ≤ width inputLength := by
    intro inputLength
    exact BinaryRoutine.values_update_le Work.reference₀
      (hvalues₇Values inputLength) (Nat.zero_le _)
  have hclearOffset : BinaryRoutine.SpaceBoundByWidthAt clearOffset
      initialSpace values₈ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      (fun inputLength => hvalues₈Values inputLength Work.temporary₃)
  have hvalues₉Values : ∀ inputLength index,
      values₉ inputLength index ≤ width inputLength := by
    intro inputLength
    exact BinaryRoutine.values_update_le Work.temporary₃
      (hvalues₈Values inputLength) (Nat.zero_le _)
  have hclearTape : BinaryRoutine.SpaceBoundByWidthAt clearTape initialSpace
      values₉ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.tapeIndex
      (fun inputLength => hvalues₉Values inputLength Work.tapeIndex)
  have hvalues₁₀Values : ∀ inputLength index,
      values₁₀ inputLength index ≤ width inputLength := by
    intro inputLength
    exact BinaryRoutine.values_update_le Work.tapeIndex
      (hvalues₉Values inputLength) (Nat.zero_le _)
  have hclearSymbol : BinaryRoutine.SpaceBoundByWidthAt clearSymbol initialSpace
      values₁₀ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.symbolIndex
      (fun inputLength => hvalues₁₀Values inputLength Work.symbolIndex)
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace values₁₁ width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hmembers
    (BinaryRoutine.SpaceBoundByWidthAt.seq hconstant
      (BinaryRoutine.SpaceBoundByWidthAt.seq hprepareSize
        (BinaryRoutine.SpaceBoundByWidthAt.seq hprepareReference
          (BinaryRoutine.SpaceBoundByWidthAt.seq hconnector
            (BinaryRoutine.SpaceBoundByWidthAt.seq hreadConnectors
              (BinaryRoutine.SpaceBoundByWidthAt.seq hchoiceConnector
                (BinaryRoutine.SpaceBoundByWidthAt.seq hclearReference
                  (BinaryRoutine.SpaceBoundByWidthAt.seq hclearOffset
                    (BinaryRoutine.SpaceBoundByWidthAt.seq hclearTape
                      (BinaryRoutine.SpaceBoundByWidthAt.seq hclearSymbol
                        hid))))))))))
  simpa [emitCaseFormula, BinaryRoutine.seqList, members, values₁, constant,
    values₂, prepareSize, values₃, prepareReference, values₄,
    connector, values₅, readConnectors, values₆, choiceConnector,
    values₇, clearReference, values₈, clearOffset, values₉,
    clearTape, values₁₀, clearSymbol, values₁₁] using hroutine

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
