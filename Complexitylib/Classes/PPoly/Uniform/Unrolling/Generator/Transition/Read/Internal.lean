/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Read.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Control

/-!
# Direct-unrolling read-formula generator -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

theorem emitReadMember_sound_internal (stateCount tapeCount : ℕ) :
    (emitReadMember stateCount tapeCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact emitHeadReference_sound stateCount false
  · subst routine
    exact emitCellReference_sound stateCount tapeCount false
  · subst routine
    exact emitRecentGate_sound .and false false 2 1

theorem setReadFormulaLimit_sound_internal :
    setReadFormulaLimit.Sound :=
  (BinaryRoutine.binaryCopy_sound Work.horizon Work.limit₀
    Work.copyCounter).seq (BinaryRoutine.addConst_sound Work.limit₀ 1)

theorem emitReadMembers_sound_internal (stateCount tapeCount : ℕ) :
    (emitReadMembers stateCount tapeCount).Sound :=
  (emitReadMember_sound_internal stateCount tapeCount).binaryFor Work.position
    Work.limit₀

theorem emitReadIdentity_sound_internal : emitReadIdentity.Sound :=
  BinaryRoutine.emitRawGateStep_sound .and false true Work.emitCounter
    Work.available Work.reference₀ Work.reference₀

theorem emitReadConnector_sound_internal : emitReadConnector.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact prepareRecentReference_sound Work.reference₁ 1
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .or false false Work.emitCounter
      Work.available Work.reference₀ Work.reference₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₁

theorem emitReadNextConnector_sound_internal :
    emitReadNextConnector.Sound :=
  (BinaryRoutine.repeatRoutine_sound 3
    (BinaryRoutine.binaryPred Work.reference₀)
    (BinaryRoutine.binaryPred_sound Work.reference₀)).seq
      emitReadConnector_sound_internal

theorem emitReadFormula_sound_internal (stateCount tapeCount : ℕ) :
    (emitReadFormula stateCount tapeCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h | h | h | h | h
  · subst routine
    exact setReadFormulaLimit_sound_internal
  · subst routine
    exact emitReadMembers_sound_internal stateCount tapeCount
  · subst routine
    exact BinaryRoutine.clear_sound Work.position
  · subst routine
    exact emitReadIdentity_sound_internal
  · subst routine
    exact prepareRecentReference_sound Work.reference₀ 2
  · subst routine
    exact emitReadConnector_sound_internal
  · subst routine
    exact BinaryRoutine.set_sound Work.loop₀ 1
  · subst routine
    exact emitReadNextConnector_sound_internal.binaryFor Work.loop₀
      Work.limit₀
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

theorem emitReadMember_effect_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (emitReadMember stateCount tapeCount).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update values Work.available
                  (values Work.available + 3)) Work.reference₀ 0)
              Work.reference₁ 0) Work.temporary₀ 0) Work.temporary₁ 0)
        Work.temporary₂ 0 := by
  simp [emitReadMember, BinaryRoutine.seqList, BinaryRoutine.seq,
    emitHeadReference_effect, emitCellReference_effect,
    emitRecentGate_effect, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₀, Work.reference₁, Work.temporary₀,
    Work.temporary₁, Work.temporary₂]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem emitReadMember_emitted_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (emitReadMember stateCount tapeCount).emitted values =
      [CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position)),
        CircuitCode.RawGate.copy
          (transitionCellRef stateCount tapeCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position) (values Work.symbolIndex)),
        { op := .and
          input₀ := values Work.available
          input₁ := values Work.available + 1
          negated₀ := false
          negated₁ := false }].flatMap CircuitCode.RawGate.encode := by
  simp [emitReadMember, BinaryRoutine.seqList, BinaryRoutine.seq,
    emitHeadReference_effect, emitHeadReference_emitted,
    emitCellReference_effect, emitCellReference_emitted,
    emitRecentGate_emitted, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.horizon, Work.configBase, Work.available, Work.reference₀,
    Work.reference₁, Work.temporary₀,
    Work.temporary₁, Work.temporary₂, Work.tapeIndex,
    Work.position, Work.symbolIndex]

theorem emitReadMember_requires_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitReadMember stateCount tapeCount).requires values := by
  simp only [emitReadMember, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  have hhead := emitHeadReference_requires stateCount false values hadd
    hmultiply hemit
  have hcopyHead :
      (emitHeadReference stateCount false).effect values Work.copyCounter = 0 := by
    rw [emitHeadReference_effect]
    simpa [Work.temporary₀, Work.available, Work.reference₀,
      Work.copyCounter] using hcopy
  have haddHead :
      (emitHeadReference stateCount false).effect values Work.addCounter = 0 := by
    rw [emitHeadReference_effect]
    simpa [Work.temporary₀, Work.available, Work.reference₀,
      Work.addCounter] using hadd
  have hmultiplyHead :
      (emitHeadReference stateCount false).effect values
        Work.multiplyCounter = 0 := by
    rw [emitHeadReference_effect]
    simpa [Work.temporary₀, Work.available, Work.reference₀,
      Work.multiplyCounter] using hmultiply
  have hemitHead :
      (emitHeadReference stateCount false).effect values Work.emitCounter = 0 := by
    rw [emitHeadReference_effect]
    simpa [Work.temporary₀, Work.available, Work.reference₀,
      Work.emitCounter] using hemit
  let afterHead := (emitHeadReference stateCount false).effect values
  have hcell := emitCellReference_requires stateCount tapeCount false
    afterHead hcopyHead haddHead hmultiplyHead hemitHead
  have hcopyCell :
      (emitCellReference stateCount tapeCount false).effect afterHead
        Work.copyCounter = 0 := by
    rw [emitCellReference_effect]
    simpa [afterHead, Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Work.available, Work.reference₀, Work.copyCounter] using hcopyHead
  have hemitCell :
      (emitCellReference stateCount tapeCount false).effect afterHead
        Work.emitCounter = 0 := by
    rw [emitCellReference_effect]
    simpa [afterHead, Work.temporary₀, Work.temporary₁, Work.temporary₂,
      Work.available, Work.reference₀, Work.emitCounter] using hemitHead
  let afterCell :=
    (emitCellReference stateCount tapeCount false).effect afterHead
  have havailableCell :
      afterCell Work.available = values Work.available + 2 := by
    simp [afterCell, afterHead, emitCellReference_effect,
      emitHeadReference_effect, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.available, Work.reference₀]
  have hrecent :
      (emitRecentGate .and false false 2 1).requires afterCell := by
    rw [emitRecentGate_requires]
    rw [havailableCell]
    exact ⟨hcopyCell, by omega, by omega, hemitCell⟩
  exact ⟨hhead, hcell, hrecent, trivial⟩

private theorem emitReadMember_spaceBoundByWidthAt
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available + 2 ≤ width inputLength)
    (hheadCap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength)
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
          values inputLength Work.tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitReadMember stateCount tapeCount) initialSpace values width := by
  let head := emitHeadReference stateCount false
  let cell := emitCellReference stateCount tapeCount false
  let recent := emitRecentGate .and false false 2 1
  let afterHead : ℕ → BinaryValues WorkCount := fun inputLength =>
    head.effect (values inputLength)
  let afterCell : ℕ → BinaryValues WorkCount := fun inputLength =>
    cell.effect (afterHead inputLength)
  have hhead : BinaryRoutine.SpaceBoundByWidthAt head initialSpace values
      width :=
    emitHeadReference_spaceBoundByWidth stateCount false hvalues hheadCap
  have hafterHeadValues : ∀ inputLength index,
      afterHead inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [show afterHead inputLength = head.effect (values inputLength) by rfl,
      show head = emitHeadReference stateCount false by rfl,
      emitHeadReference_effect]
    by_cases htemporary : index = Work.temporary₀
    · subst index
      simp [Work.temporary₀, Work.available, Work.reference₀]
    by_cases havailableIndex : index = Work.available
    · subst index
      simp [Work.temporary₀, Work.available, Work.reference₀]
      have havailableBound := havailable inputLength
      simp only [Work.available] at havailableBound
      omega
    by_cases hreference : index = Work.reference₀
    · subst index
      simp [Work.temporary₀, Work.available, Work.reference₀]
    · simpa [Function.update_apply, htemporary, havailableIndex,
        hreference] using hvalues inputLength index
  have hafterHeadCellCap : ∀ inputLength,
      transitionCellRef stateCount tapeCount
          (afterHead inputLength Work.horizon)
          (afterHead inputLength Work.configBase)
          (afterHead inputLength Work.tapeIndex)
          (afterHead inputLength Work.position)
          (afterHead inputLength Work.symbolIndex) +
          (afterHead inputLength Work.tapeIndex *
                (afterHead inputLength Work.horizon + 2) +
              afterHead inputLength Work.position) +
          (afterHead inputLength Work.horizon + 2) + tapeCount +
          afterHead inputLength Work.tapeIndex + 4 ≤
        width inputLength := by
    intro inputLength
    rw [show afterHead inputLength = head.effect (values inputLength) by rfl,
      show head = emitHeadReference stateCount false by rfl,
      emitHeadReference_effect]
    simpa [Work.temporary₀, Work.available, Work.reference₀,
      Work.configBase, Work.horizon, Work.tapeIndex, Work.position,
      Work.symbolIndex] using hcellCap inputLength
  have hcell : BinaryRoutine.SpaceBoundByWidthAt cell initialSpace afterHead
      width :=
    emitCellReference_spaceBoundByWidth stateCount tapeCount false
      hafterHeadValues hafterHeadCellCap
  have hafterCellValues : ∀ inputLength index,
      afterCell inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [show afterCell inputLength = cell.effect (afterHead inputLength) by rfl,
      show cell = emitCellReference stateCount tapeCount false by rfl,
      emitCellReference_effect]
    by_cases htemporary₂ : index = Work.temporary₂
    · subst index
      simp [Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.available, Work.reference₀]
    by_cases htemporary₁ : index = Work.temporary₁
    · subst index
      simp [Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.available, Work.reference₀]
    by_cases htemporary₀ : index = Work.temporary₀
    · subst index
      simp [Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.available, Work.reference₀]
    by_cases havailableIndex : index = Work.available
    · subst index
      rw [show afterHead inputLength = head.effect (values inputLength) by rfl,
        show head = emitHeadReference stateCount false by rfl,
        emitHeadReference_effect]
      simp [Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.available, Work.reference₀]
      have havailableBound := havailable inputLength
      simp only [Work.available] at havailableBound
      omega
    by_cases hreference : index = Work.reference₀
    · subst index
      simp [Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.available, Work.reference₀]
    · simpa [Function.update_apply, htemporary₂, htemporary₁,
        htemporary₀, havailableIndex, hreference] using
        hafterHeadValues inputLength index
  have hrecent : BinaryRoutine.SpaceBoundByWidthAt recent initialSpace
      afterCell width := by
    apply emitRecentGate_spaceBoundByWidth .and false false 2 1
    · exact fun inputLength => hafterCellValues inputLength Work.available
    · exact fun inputLength => hafterCellValues inputLength Work.reference₀
    · exact fun inputLength => hafterCellValues inputLength Work.reference₁
    · intro inputLength
      simp [afterCell, afterHead, cell, head, emitCellReference_effect,
        emitHeadReference_effect, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.available, Work.reference₀]
    · intro inputLength
      simp [afterCell, afterHead, cell, head, emitCellReference_effect,
        emitHeadReference_effect, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.available, Work.reference₀]
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace (fun inputLength => recent.effect (afterCell inputLength))
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hhead
    (BinaryRoutine.SpaceBoundByWidthAt.seq hcell
      (BinaryRoutine.SpaceBoundByWidthAt.seq hrecent hid))
  simpa [emitReadMember, BinaryRoutine.seqList, head, cell, recent, afterHead,
    afterCell] using hroutine

theorem setReadFormulaLimit_effect_internal
    (values : BinaryValues WorkCount) :
    setReadFormulaLimit.effect values =
      Function.update values Work.limit₀ (values Work.horizon + 1) := by
  simp [setReadFormulaLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, Work.horizon, Work.limit₀]

theorem setReadFormulaLimit_emitted_internal
    (values : BinaryValues WorkCount) :
    setReadFormulaLimit.emitted values = [] := by
  rfl

theorem setReadFormulaLimit_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    setReadFormulaLimit.requires values := by
  have hcopy' : values 10 = 0 := by
    simpa [Work.copyCounter] using hcopy
  simp [setReadFormulaLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, hcopy', Work.horizon, Work.limit₀,
    Work.copyCounter]

private theorem setReadFormulaLimit_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hhorizon : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt setReadFormulaLimit initialSpace values
      width := by
  let copy := BinaryRoutine.binaryCopy Work.horizon Work.limit₀
    Work.copyCounter
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.horizon Work.limit₀
      Work.copyCounter (fun inputLength => hvalues inputLength Work.horizon)
      (fun inputLength => hvalues inputLength Work.limit₀)
  have hadd : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.addConst Work.limit₀ 1) initialSpace
      (fun inputLength => copy.effect (values inputLength)) width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simpa [copy, BinaryRoutine.binaryCopy] using hhorizon inputLength
  simpa [setReadFormulaLimit, copy] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy hadd)

theorem emitReadIdentity_effect_internal
    (values : BinaryValues WorkCount) :
    emitReadIdentity.effect values =
      Function.update values Work.available (values Work.available + 1) := by
  rfl

theorem emitReadIdentity_emitted_internal
    (values : BinaryValues WorkCount)
    (hreference : values Work.reference₀ = 0) :
    emitReadIdentity.emitted values =
      CircuitCode.RawGate.encode (CircuitCode.RawGate.constant 0 false) := by
  simp [emitReadIdentity, BinaryRoutine.emitRawGateStep,
    CircuitCode.RawGate.constant, hreference]

theorem emitReadIdentity_requires_internal
    (values : BinaryValues WorkCount)
    (hemit : values Work.emitCounter = 0) :
    emitReadIdentity.requires values := by
  change CircuitCode.Machine.RawGateStepDistinct 9 5 7 7 ∧ values 9 = 0
  exact ⟨⟨by decide, by decide, by decide, by decide, by decide⟩,
    by simpa [Work.emitCounter] using hemit⟩

theorem emitReadConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitReadConnector.effect values =
      Function.update
        (Function.update values Work.available (values Work.available + 1))
        Work.reference₁ 0 := by
  simp [emitReadConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₀, Work.reference₁]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem emitReadConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitReadConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.reference₀
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  simp [emitReadConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect, prepareRecentReference_emitted,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.available,
    Work.reference₀, Work.reference₁]

theorem emitReadConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitReadConnector.requires values := by
  have hprepare := (prepareRecentReference_requires Work.reference₁ 1 values
    (by decide) (by decide) (by decide)).2 ⟨hcopy, havailable⟩
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
      Work.available Work.reference₀ Work.reference₁ := by
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  simp only [emitReadConnector, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  refine ⟨hprepare, ⟨hdistinct, ?_⟩, trivial, trivial⟩
  rw [prepareRecentReference_effect]
  simpa [Work.reference₁, Work.emitCounter] using hemit

theorem emitReadConnector_spaceBoundByWidth_internal
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitReadConnector initialSpace values
      width := by
  let prepare := prepareRecentReference Work.reference₁ 1
  let emit := BinaryRoutine.emitRawGateStep .or false false
    Work.emitCounter Work.available Work.reference₀ Work.reference₁
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (values₁ inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width := by
    apply prepareRecentReference_spaceBoundByWidth Work.reference₁ 1
    · exact havailable
    · exact hreference₁
    · exact havailablePositive
  have hvalues₁Available : ∀ inputLength,
      values₁ inputLength Work.available ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare, prepareRecentReference_effect,
      Work.available, Work.reference₁] using
        havailable inputLength
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
    BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .or false false
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
  simpa [emitReadConnector, BinaryRoutine.seqList, prepare, emit, values₁,
    values₂] using hroutine

private theorem repeatReadReferencePred_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hwidthPositive : ∀ inputLength, 1 ≤ width inputLength)
    (hreferenceUpper : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine 3
        (BinaryRoutine.binaryPred Work.reference₀))
      initialSpace values width := by
  let pred := BinaryRoutine.binaryPred Work.reference₀
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    pred.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    pred.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    pred.effect (values₂ inputLength)
  have hpred₀ : BinaryRoutine.SpaceBoundByWidthAt pred initialSpace values
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro inputLength
    have hupper := hreferenceUpper inputLength
    have hpositive := hwidthPositive inputLength
    change values inputLength Work.reference₀ - 1 + 1 ≤
      width inputLength
    omega
  have hpred₁ : BinaryRoutine.SpaceBoundByWidthAt pred initialSpace values₁
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro inputLength
    have hupper := hreferenceUpper inputLength
    have hpositive := hwidthPositive inputLength
    simp only [values₁, pred, BinaryRoutine.binaryPred,
      Function.update_self]
    omega
  have hpred₂ : BinaryRoutine.SpaceBoundByWidthAt pred initialSpace values₂
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro inputLength
    have hupper := hreferenceUpper inputLength
    have hpositive := hwidthPositive inputLength
    simp only [values₂, values₁, pred, BinaryRoutine.binaryPred,
      Function.update_self]
    omega
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace values₃ width :=
    BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hpred₀
    (BinaryRoutine.SpaceBoundByWidthAt.seq hpred₁
      (BinaryRoutine.SpaceBoundByWidthAt.seq hpred₂ hid))
  simpa [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList, pred, values₁,
    values₂, values₃] using hroutine

private theorem repeatReadReferencePred_effect
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.repeatRoutine 3
      (BinaryRoutine.binaryPred Work.reference₀)).effect values =
      Function.update values Work.reference₀
        (values Work.reference₀ - 3) := by
  simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.binaryPred, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.reference₀]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> omega

private theorem emitReadNextConnector_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available)
    (hreferenceUpper : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt emitReadNextConnector initialSpace values
      width := by
  let repetition := BinaryRoutine.repeatRoutine 3
    (BinaryRoutine.binaryPred Work.reference₀)
  let repeated : ℕ → BinaryValues WorkCount := fun inputLength =>
    repetition.effect (values inputLength)
  have hrepeat : BinaryRoutine.SpaceBoundByWidthAt repetition initialSpace values
      width := by
    apply repeatReadReferencePred_spaceBoundByWidthAt
    · intro inputLength
      exact (havailablePositive inputLength).trans
        (havailable inputLength)
    · exact hreferenceUpper
  have hconnector : BinaryRoutine.SpaceBoundByWidthAt emitReadConnector
      initialSpace repeated width := by
    apply emitReadConnector_spaceBoundByWidth_internal
    · intro inputLength
      rw [show repeated inputLength = Function.update (values inputLength)
          Work.reference₀ (values inputLength Work.reference₀ - 3) by
        exact repeatReadReferencePred_effect (values inputLength)]
      simpa [Work.available, Work.reference₀] using havailable inputLength
    · intro inputLength
      rw [show repeated inputLength = Function.update (values inputLength)
          Work.reference₀ (values inputLength Work.reference₀ - 3) by
        exact repeatReadReferencePred_effect (values inputLength)]
      simpa [Work.available, Work.reference₀] using
        havailablePositive inputLength
    · intro inputLength
      rw [show repeated inputLength = Function.update (values inputLength)
          Work.reference₀ (values inputLength Work.reference₀ - 3) by
        exact repeatReadReferencePred_effect (values inputLength)]
      simp only [Function.update_self]
      exact (Nat.sub_le _ _).trans (hreferenceUpper inputLength)
    · intro inputLength
      rw [show repeated inputLength = Function.update (values inputLength)
          Work.reference₀ (values inputLength Work.reference₀ - 3) by
        exact repeatReadReferencePred_effect (values inputLength)]
      simpa [Work.reference₀, Work.reference₁] using
        hreference₁ inputLength
  simpa [emitReadNextConnector, repetition, repeated] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hrepeat hconnector)

private theorem repeatReadReferencePred_emitted
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.repeatRoutine 3
      (BinaryRoutine.binaryPred Work.reference₀)).emitted values = [] := by
  simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.binaryPred, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem repeatReadReferencePred_requires
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.repeatRoutine 3
      (BinaryRoutine.binaryPred Work.reference₀)).requires values ↔
      3 ≤ values Work.reference₀ := by
  simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.binaryPred, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.reference₀]
  omega

theorem emitReadNextConnector_effect_internal
    (values : BinaryValues WorkCount) :
    emitReadNextConnector.effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.reference₀ - 3)) Work.available
          (values Work.available + 1)) Work.reference₁ 0 := by
  change emitReadConnector.effect
      ((BinaryRoutine.repeatRoutine 3
        (BinaryRoutine.binaryPred Work.reference₀)).effect values) = _
  rw [repeatReadReferencePred_effect, emitReadConnector_effect_internal]
  funext i
  simp [Function.update_apply, Work.available, Work.reference₀,
    Work.reference₁]

theorem emitReadNextConnector_emitted_internal
    (values : BinaryValues WorkCount) :
    emitReadNextConnector.emitted values =
      CircuitCode.RawGate.encode
        { op := .or
          input₀ := values Work.reference₀ - 3
          input₁ := values Work.available - 1
          negated₀ := false
          negated₁ := false } := by
  rw [emitReadNextConnector, BinaryRoutine.seq]
  change
    (BinaryRoutine.repeatRoutine 3
      (BinaryRoutine.binaryPred Work.reference₀)).emitted values ++
      emitReadConnector.emitted
        ((BinaryRoutine.repeatRoutine 3
          (BinaryRoutine.binaryPred Work.reference₀)).effect values) = _
  rw [repeatReadReferencePred_emitted, repeatReadReferencePred_effect,
    emitReadConnector_emitted_internal]
  simp [Work.available, Work.reference₀]

theorem emitReadNextConnector_requires_internal
    (values : BinaryValues WorkCount)
    (hreference : 3 ≤ values Work.reference₀)
    (hcopy : values Work.copyCounter = 0)
    (havailable : 1 ≤ values Work.available)
    (hemit : values Work.emitCounter = 0) :
    emitReadNextConnector.requires values := by
  rw [emitReadNextConnector, BinaryRoutine.seq]
  refine ⟨(repeatReadReferencePred_requires values).2 hreference, ?_⟩
  rw [repeatReadReferencePred_effect]
  apply emitReadConnector_requires_internal
  · simpa [Work.reference₀, Work.copyCounter] using hcopy
  · simpa [Work.reference₀, Work.available] using havailable
  · simpa [Work.reference₀, Work.emitCounter] using hemit

private structure ReadMemberInvariant
    (values : BinaryValues WorkCount) : Prop where
  reference₀ : values Work.reference₀ = 0
  reference₁ : values Work.reference₁ = 0
  temporary₀ : values Work.temporary₀ = 0
  temporary₁ : values Work.temporary₁ = 0
  temporary₂ : values Work.temporary₂ = 0
  emitCounter : values Work.emitCounter = 0
  copyCounter : values Work.copyCounter = 0
  multiplyCounter : values Work.multiplyCounter = 0
  addCounter : values Work.addCounter = 0

private theorem ReadMemberInvariant.ofReadFormulaClean
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadMemberInvariant values :=
  ⟨hclean.reference₀, hclean.reference₁, hclean.temporary₀,
    hclean.temporary₁, hclean.temporary₂, hclean.emitCounter,
    hclean.copyCounter, hclean.multiplyCounter, hclean.addCounter⟩

private theorem ReadMemberInvariant.updateAvailable
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadMemberInvariant values) :
    ReadMemberInvariant (Function.update values Work.available amount) := by
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.available, Work.reference₀] using hinvariant.reference₀
  · simpa [Work.available, Work.reference₁] using hinvariant.reference₁
  · simpa [Work.available, Work.temporary₀] using hinvariant.temporary₀
  · simpa [Work.available, Work.temporary₁] using hinvariant.temporary₁
  · simpa [Work.available, Work.temporary₂] using hinvariant.temporary₂
  · simpa [Work.available, Work.emitCounter] using hinvariant.emitCounter
  · simpa [Work.available, Work.copyCounter] using hinvariant.copyCounter
  · simpa [Work.available, Work.multiplyCounter] using
      hinvariant.multiplyCounter
  · simpa [Work.available, Work.addCounter] using hinvariant.addCounter

private theorem ReadMemberInvariant.updatePosition
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadMemberInvariant values) :
    ReadMemberInvariant (Function.update values Work.position amount) := by
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.position, Work.reference₀] using hinvariant.reference₀
  · simpa [Work.position, Work.reference₁] using hinvariant.reference₁
  · simpa [Work.position, Work.temporary₀] using hinvariant.temporary₀
  · simpa [Work.position, Work.temporary₁] using hinvariant.temporary₁
  · simpa [Work.position, Work.temporary₂] using hinvariant.temporary₂
  · simpa [Work.position, Work.emitCounter] using hinvariant.emitCounter
  · simpa [Work.position, Work.copyCounter] using hinvariant.copyCounter
  · simpa [Work.position, Work.multiplyCounter] using
      hinvariant.multiplyCounter
  · simpa [Work.position, Work.addCounter] using hinvariant.addCounter

private theorem emitReadMember_effect_of_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) :
    (emitReadMember stateCount tapeCount).effect values =
      Function.update values Work.available (values Work.available + 3) := by
  rw [emitReadMember_effect_internal]
  have href₀ : values 7 = 0 := by
    simpa [Work.reference₀] using hinvariant.reference₀
  have href₁ : values 8 = 0 := by
    simpa [Work.reference₁] using hinvariant.reference₁
  have htemporary₀ : values 22 = 0 := by
    simpa [Work.temporary₀] using hinvariant.temporary₀
  have htemporary₁ : values 23 = 0 := by
    simpa [Work.temporary₁] using hinvariant.temporary₁
  have htemporary₂ : values 24 = 0 := by
    simpa [Work.temporary₂] using hinvariant.temporary₂
  funext i
  by_cases hi₂ : i = Work.temporary₂
  · subst i
    simpa [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
      htemporary₂.symm
  by_cases hi₁ : i = Work.temporary₁
  · subst i
    simpa [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
      htemporary₁.symm
  by_cases hi₀ : i = Work.temporary₀
  · subst i
    simpa [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
      htemporary₀.symm
  by_cases hiref₁ : i = Work.reference₁
  · subst i
    simpa [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
      href₁.symm
  by_cases hiref₀ : i = Work.reference₀
  · subst i
    simpa [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂] using
      href₀.symm
  by_cases hiavailable : i = Work.available
  · subst i
    simp [Work.available, Work.reference₀, Work.reference₁,
      Work.temporary₀, Work.temporary₁, Work.temporary₂]
  · simp [hi₂, hi₁, hi₀, hiref₁, hiref₀, hiavailable]

private theorem emitReadMember_binaryForValues
    (stateCount tapeCount : ℕ) (initial : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant initial) : ∀ count,
    BinaryRoutine.binaryForValues (emitReadMember stateCount tapeCount)
        Work.position initial count =
      Function.update
        (Function.update initial Work.available
          (initial Work.available + 3 * count)) Work.position
        (initial Work.position + count) := by
  intro count
  induction count with
  | zero =>
      simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      have hcurrent : ReadMemberInvariant
          (BinaryRoutine.binaryForValues
            (emitReadMember stateCount tapeCount) Work.position initial
            count) := by
        rw [ih]
        exact ReadMemberInvariant.updatePosition _ _
          (ReadMemberInvariant.updateAvailable _ _ hinvariant)
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        emitReadMember_effect_of_invariant stateCount tapeCount _ hcurrent,
        ih]
      funext i
      simp [Function.update_apply, Work.available, Work.position,
        Nat.mul_succ]
      split_ifs <;> omega

private theorem emitReadMembers_spaceBoundByWidthAt
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hinvariant : ∀ inputLength, ReadMemberInvariant (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hposition : ∀ inputLength,
      values inputLength Work.position < values inputLength Work.limit₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
            3 * (values inputLength Work.limit₀ -
              values inputLength Work.position) +
          2 ≤
        width inputLength)
    (hheadCap : ∀ inputLength position,
      values inputLength Work.position ≤ position →
      position < values inputLength Work.limit₀ →
      transitionHeadRef stateCount (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength)
    (hcellCap : ∀ inputLength position,
      values inputLength Work.position ≤ position →
      position < values inputLength Work.limit₀ →
      transitionCellRef stateCount tapeCount
            (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position
            (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
                (values inputLength Work.horizon + 2) + position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitReadMembers stateCount tapeCount) initialSpace values width := by
  let body := emitReadMember stateCount tapeCount
  let loopCount : ℕ → ℕ := fun inputLength =>
    BinaryRoutine.binaryForCount Work.position Work.limit₀
      (values inputLength)
  let pairedInput : ℕ → ℕ := fun code => code.unpair.1
  let pairedCount : ℕ → ℕ := fun code =>
    min code.unpair.2 (loopCount (pairedInput code) - 1)
  let pairedValues : ℕ → BinaryValues WorkCount := fun code =>
    BinaryRoutine.binaryForValues body Work.position
      (values (pairedInput code)) (pairedCount code)
  let pairedInitialSpace : ℕ → ℕ := fun code =>
    initialSpace (pairedInput code)
  let pairedWidth : ℕ → ℕ := fun code =>
    width (pairedInput code)
  have hpairedCount (code : ℕ) :
      pairedCount code ≤ loopCount (pairedInput code) := by
    have := Nat.min_le_right code.unpair.2
      (loopCount (pairedInput code) - 1)
    simp only [pairedCount]
    omega
  have hpairedPosition (code : ℕ) :
      values (pairedInput code) Work.position + pairedCount code <
        values (pairedInput code) Work.limit₀ := by
    have hcount := Nat.min_le_right code.unpair.2
      (loopCount (pairedInput code) - 1)
    have hstart := hposition (pairedInput code)
    simp only [pairedCount, loopCount, BinaryRoutine.binaryForCount]
    simp only [loopCount, BinaryRoutine.binaryForCount] at hcount
    omega
  have hpairedValues : ∀ code index,
      pairedValues code index ≤ pairedWidth code := by
    intro code index
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl,
      show body = emitReadMember stateCount tapeCount by rfl,
      emitReadMember_binaryForValues stateCount tapeCount _
        (hinvariant (pairedInput code))]
    by_cases hpositionIndex : index = Work.position
    · subst index
      simp [pairedWidth, Work.available, Work.position]
      exact (hpairedPosition code).le.trans
        (hvalues (pairedInput code) Work.limit₀)
    by_cases havailableIndex : index = Work.available
    · subst index
      simp [pairedWidth, Work.available, Work.position]
      have hcount := hpairedCount code
      have havailableBound := havailable (pairedInput code)
      simp only [loopCount, BinaryRoutine.binaryForCount] at hcount
      simp only [Work.available, Work.limit₀, Work.position] at havailableBound
      simp only [Work.limit₀, Work.position] at hcount
      omega
    · have hpositionIndex' : Work.position ≠ index :=
        Ne.symm hpositionIndex
      have havailableIndex' : Work.available ≠ index :=
        Ne.symm havailableIndex
      simpa [pairedWidth, Function.update_apply, hpositionIndex,
        havailableIndex, hpositionIndex', havailableIndex'] using
          hvalues (pairedInput code) index
  have hpairedAvailable : ∀ code,
      pairedValues code Work.available + 2 ≤ pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl,
      show body = emitReadMember stateCount tapeCount by rfl,
      emitReadMember_binaryForValues stateCount tapeCount _
        (hinvariant (pairedInput code))]
    simp [pairedWidth, Work.available, Work.position]
    have hcount := hpairedCount code
    have havailableBound := havailable (pairedInput code)
    simp only [loopCount, BinaryRoutine.binaryForCount] at hcount
    simp only [Work.available, Work.limit₀, Work.position] at havailableBound
    simp only [Work.limit₀, Work.position] at hcount
    omega
  have hpairedHeadCap : ∀ code,
      transitionHeadRef stateCount (pairedValues code Work.horizon)
            (pairedValues code Work.configBase)
            (pairedValues code Work.tapeIndex)
            (pairedValues code Work.position) +
          pairedValues code Work.tapeIndex +
          pairedValues code Work.horizon + 1 ≤
        pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl,
      show body = emitReadMember stateCount tapeCount by rfl,
      emitReadMember_binaryForValues stateCount tapeCount _
        (hinvariant (pairedInput code))]
    simpa [pairedWidth, Work.available, Work.position, Work.horizon,
      Work.configBase, Work.tapeIndex] using
        hheadCap (pairedInput code)
          (values (pairedInput code) Work.position + pairedCount code)
          (by omega) (hpairedPosition code)
  have hpairedCellCap : ∀ code,
      transitionCellRef stateCount tapeCount
            (pairedValues code Work.horizon)
            (pairedValues code Work.configBase)
            (pairedValues code Work.tapeIndex)
            (pairedValues code Work.position)
            (pairedValues code Work.symbolIndex) +
          (pairedValues code Work.tapeIndex *
                (pairedValues code Work.horizon + 2) +
              pairedValues code Work.position) +
          (pairedValues code Work.horizon + 2) + tapeCount +
          pairedValues code Work.tapeIndex + 4 ≤
        pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl,
      show body = emitReadMember stateCount tapeCount by rfl,
      emitReadMember_binaryForValues stateCount tapeCount _
        (hinvariant (pairedInput code))]
    simpa [pairedWidth, Work.available, Work.position, Work.horizon,
      Work.configBase, Work.tapeIndex, Work.symbolIndex] using
        hcellCap (pairedInput code)
          (values (pairedInput code) Work.position + pairedCount code)
          (by omega) (hpairedPosition code)
  have hbody := emitReadMember_spaceBoundByWidthAt stateCount tapeCount
      (initialSpace := pairedInitialSpace) (values := pairedValues)
      (width := pairedWidth) hpairedValues hpairedAvailable hpairedHeadCap
      hpairedCellCap
  rw [emitReadMembers]
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · exact fun inputLength => hvalues inputLength Work.limit₀
  · intro inputLength count hcount
    rw [emitReadMember_binaryForValues stateCount tapeCount _
        (hinvariant inputLength)]
    simp [Work.available, Work.position]
    have hlimit := hvalues inputLength Work.limit₀
    have hstart := hposition inputLength
    simp only [BinaryRoutine.binaryForCount] at hcount
    simp only [Work.limit₀, Work.position] at hcount hlimit hstart
    omega
  · exact hbody

private theorem emitReadMembers_effect_of_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) :
    (emitReadMembers stateCount tapeCount).effect values =
      Function.update
        (Function.update values Work.available
          (values Work.available +
            3 * (values Work.limit₀ - values Work.position)))
        Work.position
          (values Work.position +
            (values Work.limit₀ - values Work.position)) := by
  exact emitReadMember_binaryForValues stateCount tapeCount values hinvariant
    (values Work.limit₀ - values Work.position)

private theorem emitReadMember_binaryForValues_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) (count : ℕ) :
    ReadMemberInvariant
      (BinaryRoutine.binaryForValues (emitReadMember stateCount tapeCount)
        Work.position values count) := by
  rw [emitReadMember_binaryForValues stateCount tapeCount values hinvariant]
  exact ReadMemberInvariant.updatePosition _ _
    (ReadMemberInvariant.updateAvailable _ _ hinvariant)

private theorem emitReadMember_requires_of_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) :
    (emitReadMember stateCount tapeCount).requires values :=
  emitReadMember_requires_internal stateCount tapeCount values
    hinvariant.copyCounter hinvariant.addCounter hinvariant.multiplyCounter
    hinvariant.emitCounter

private theorem emitReadMember_preserves_position
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) :
    (emitReadMember stateCount tapeCount).effect values Work.position =
      values Work.position := by
  rw [emitReadMember_effect_of_invariant stateCount tapeCount values hinvariant]
  simp [show Work.position ≠ Work.available by decide]

private theorem emitReadMember_preserves_limit₀
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values) :
    (emitReadMember stateCount tapeCount).effect values Work.limit₀ =
      values Work.limit₀ := by
  rw [emitReadMember_effect_of_invariant stateCount tapeCount values hinvariant]
  simp [show Work.limit₀ ≠ Work.available by decide]

private theorem emitReadMembers_requires_of_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values)
    (hle : values Work.position ≤ values Work.limit₀) :
    (emitReadMembers stateCount tapeCount).requires values := by
  rw [emitReadMembers]
  refine ⟨by decide, hle, ?_⟩
  intro count _
  dsimp only
  generalize hcurrentEq :
    BinaryRoutine.binaryForValues (emitReadMember stateCount tapeCount)
      Work.position values count = current
  have hcurrent : ReadMemberInvariant current :=
    hcurrentEq ▸ emitReadMember_binaryForValues_invariant stateCount tapeCount
      values hinvariant count
  exact
    ⟨emitReadMember_requires_of_invariant stateCount tapeCount current
      hcurrent,
      emitReadMember_preserves_position stateCount tapeCount current hcurrent,
      emitReadMember_preserves_limit₀ stateCount tapeCount current hcurrent⟩

private theorem indexedGateBlocks_succ_last
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (count + 1) blockAt =
      indexedGateBlocks count blockAt ++ blockAt count := by
  induction count generalizing blockAt with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      change blockAt 0 ++
          indexedGateBlocks (count + 1) (fun index => blockAt (index + 1)) =
        (blockAt 0 ++ indexedGateBlocks count
          (fun index => blockAt (index + 1))) ++ blockAt (count + 1)
      rw [ih (fun index => blockAt (index + 1))]
      simp [List.append_assoc]

private theorem binaryForEmitted_eq_indexedGateBlocks
    (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hemitted : ∀ count,
      body.emitted
          (BinaryRoutine.binaryForValues body counterIdx initial count) =
        (blockAt count).flatMap CircuitCode.RawGate.encode) : ∀ count,
    BinaryRoutine.binaryForEmitted body counterIdx initial count =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih, hemitted,
        indexedGateBlocks_succ_last]
      simp only [List.flatMap_append]

private theorem emitReadMember_emitted_at_counter
    (stateCount tapeCount : ℕ) (initial : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant initial)
    (hposition : initial Work.position = 0) (count : ℕ) :
    (emitReadMember stateCount tapeCount).emitted
        (BinaryRoutine.binaryForValues
          (emitReadMember stateCount tapeCount) Work.position initial count) =
      (readFormulaMemberBlock stateCount tapeCount (initial Work.horizon)
        (initial Work.configBase) (initial Work.available)
        (initial Work.tapeIndex) (initial Work.symbolIndex) count).flatMap
          CircuitCode.RawGate.encode := by
  rw [emitReadMember_binaryForValues stateCount tapeCount initial hinvariant,
    emitReadMember_emitted_internal]
  have hposition' : initial 30 = 0 := by
    simpa [Work.position] using hposition
  simp [readFormulaMemberBlock, hposition', Work.horizon, Work.configBase,
    Work.available, Work.position, Work.tapeIndex, Work.symbolIndex]

private theorem emitReadMembers_emitted_of_invariant
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hinvariant : ReadMemberInvariant values)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₀ = values Work.horizon + 1) :
    (emitReadMembers stateCount tapeCount).emitted values =
      (readFormulaMemberGates stateCount tapeCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.symbolIndex)).flatMap
          CircuitCode.RawGate.encode := by
  change BinaryRoutine.binaryForEmitted
      (emitReadMember stateCount tapeCount) Work.position values
        (values Work.limit₀ - values Work.position) = _
  rw [hposition, hlimit]
  simp only [Nat.sub_zero, readFormulaMemberGates]
  apply binaryForEmitted_eq_indexedGateBlocks
  exact emitReadMember_emitted_at_counter stateCount tapeCount values
    hinvariant hposition

private structure ReadConnectorInvariant
    (values : BinaryValues WorkCount) : Prop where
  reference₁ : values Work.reference₁ = 0
  copyCounter : values Work.copyCounter = 0
  emitCounter : values Work.emitCounter = 0

private theorem ReadConnectorInvariant.updateAvailable
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadConnectorInvariant values) :
    ReadConnectorInvariant (Function.update values Work.available amount) :=
  ⟨by simpa [Work.available, Work.reference₁] using hinvariant.reference₁,
    by simpa [Work.available, Work.copyCounter] using hinvariant.copyCounter,
    by simpa [Work.available, Work.emitCounter] using hinvariant.emitCounter⟩

private theorem ReadConnectorInvariant.updateReference₀
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadConnectorInvariant values) :
    ReadConnectorInvariant (Function.update values Work.reference₀ amount) :=
  ⟨by simpa [Work.reference₀, Work.reference₁] using
      hinvariant.reference₁,
    by simpa [Work.reference₀, Work.copyCounter] using hinvariant.copyCounter,
    by simpa [Work.reference₀, Work.emitCounter] using hinvariant.emitCounter⟩

private theorem ReadConnectorInvariant.updateLoop₀
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadConnectorInvariant values) :
    ReadConnectorInvariant (Function.update values Work.loop₀ amount) :=
  ⟨by simpa [Work.loop₀, Work.reference₁] using hinvariant.reference₁,
    by simpa [Work.loop₀, Work.copyCounter] using hinvariant.copyCounter,
    by simpa [Work.loop₀, Work.emitCounter] using hinvariant.emitCounter⟩

private theorem emitReadNextConnector_effect_of_invariant
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values) :
    emitReadNextConnector.effect values =
      Function.update
        (Function.update values Work.reference₀
          (values Work.reference₀ - 3)) Work.available
        (values Work.available + 1) := by
  rw [emitReadNextConnector_effect_internal]
  funext i
  by_cases hireference₁ : i = Work.reference₁
  · subst i
    have href : values 8 = 0 := by
      simpa [Work.reference₁] using hinvariant.reference₁
    simpa [Work.available, Work.reference₀, Work.reference₁] using
      href.symm
  · simp [hireference₁]

private theorem emitReadNextConnector_binaryForValues
    (initial : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant initial) : ∀ count,
    BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ initial
        count =
      Function.update
        (Function.update
          (Function.update initial Work.available
            (initial Work.available + count)) Work.reference₀
          (initial Work.reference₀ - 3 * count)) Work.loop₀
        (initial Work.loop₀ + count) := by
  intro count
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues]
  | succ count ih =>
      have hcurrent : ReadConnectorInvariant
          (BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
            initial count) := by
        rw [ih]
        exact ReadConnectorInvariant.updateLoop₀ _ _
          (ReadConnectorInvariant.updateReference₀ _ _
            (ReadConnectorInvariant.updateAvailable _ _ hinvariant))
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        emitReadNextConnector_effect_of_invariant _ hcurrent, ih]
      funext i
      by_cases hiloop : i = Work.loop₀
      · subst i
        simp [Work.available, Work.reference₀, Work.loop₀]
        omega
      by_cases hireference : i = Work.reference₀
      · subst i
        simp [Work.available, Work.reference₀, Work.loop₀,
          Nat.mul_succ]
        omega
      by_cases hiavailable : i = Work.available
      · subst i
        simp [Work.available, Work.reference₀, Work.loop₀]
        omega
      · simp [hiloop, hireference, hiavailable]

private theorem emitReadNextConnector_binaryForValues_invariant
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values) (count : ℕ) :
    ReadConnectorInvariant
      (BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ values
        count) := by
  rw [emitReadNextConnector_binaryForValues values hinvariant]
  exact ReadConnectorInvariant.updateLoop₀ _ _
    (ReadConnectorInvariant.updateReference₀ _ _
      (ReadConnectorInvariant.updateAvailable _ _ hinvariant))

private theorem emitReadNextConnectors_spaceBoundByWidthAt
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hinvariant : ∀ inputLength,
      ReadConnectorInvariant (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hloop : ∀ inputLength,
      values inputLength Work.loop₀ ≤ values inputLength Work.limit₀)
    (havailable : ∀ inputLength,
      values inputLength Work.available +
          (values inputLength Work.limit₀ -
            values inputLength Work.loop₀) ≤
        width inputLength)
    (havailablePositive : ∀ inputLength,
      1 ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀ Work.limit₀)
      initialSpace values width := by
  let loopCount : ℕ → ℕ := fun inputLength =>
    BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀
      (values inputLength)
  let pairedInput : ℕ → ℕ := fun code => code.unpair.1
  let pairedCount : ℕ → ℕ := fun code =>
    min code.unpair.2 (loopCount (pairedInput code) - 1)
  let pairedValues : ℕ → BinaryValues WorkCount := fun code =>
    BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
      (values (pairedInput code)) (pairedCount code)
  let pairedInitialSpace : ℕ → ℕ := fun code =>
    initialSpace (pairedInput code)
  let pairedWidth : ℕ → ℕ := fun code =>
    width (pairedInput code)
  have hpairedCount (code : ℕ) :
      pairedCount code ≤ loopCount (pairedInput code) := by
    have := Nat.min_le_right code.unpair.2
      (loopCount (pairedInput code) - 1)
    simp only [pairedCount]
    omega
  have hpairedAvailable : ∀ code,
      pairedValues code Work.available ≤ pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
          (values (pairedInput code)) (pairedCount code) by rfl,
      emitReadNextConnector_binaryForValues _
        (hinvariant (pairedInput code))]
    simp [pairedWidth, Work.available, Work.reference₀, Work.loop₀]
    have hcount := hpairedCount code
    have havailableBound := havailable (pairedInput code)
    simp only [loopCount, BinaryRoutine.binaryForCount] at hcount
    simp only [Work.limit₀, Work.loop₀] at hcount
    simp only [Work.available, Work.limit₀, Work.loop₀] at havailableBound
    omega
  have hpairedAvailablePositive : ∀ code,
      1 ≤ pairedValues code Work.available := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
          (values (pairedInput code)) (pairedCount code) by rfl,
      emitReadNextConnector_binaryForValues _
        (hinvariant (pairedInput code))]
    simp [Work.available, Work.reference₀, Work.loop₀]
    have hpositive := havailablePositive (pairedInput code)
    simp only [Work.available] at hpositive
    omega
  have hpairedReference₀ : ∀ code,
      pairedValues code Work.reference₀ ≤ pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
          (values (pairedInput code)) (pairedCount code) by rfl,
      emitReadNextConnector_binaryForValues _
        (hinvariant (pairedInput code))]
    simp [pairedWidth, Work.available, Work.reference₀, Work.loop₀]
    have hupper := hvalues (pairedInput code) Work.reference₀
    simp only [Work.reference₀] at hupper
    omega
  have hpairedReference₁ : ∀ code,
      pairedValues code Work.reference₁ ≤ pairedWidth code := by
    intro code
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
          (values (pairedInput code)) (pairedCount code) by rfl,
      emitReadNextConnector_binaryForValues _
        (hinvariant (pairedInput code))]
    simpa [pairedWidth, Work.available, Work.reference₀, Work.reference₁,
      Work.loop₀] using hvalues (pairedInput code) Work.reference₁
  have hbody := emitReadNextConnector_spaceBoundByWidthAt
    (initialSpace := pairedInitialSpace) (values := pairedValues)
    (width := pairedWidth) hpairedAvailable hpairedAvailablePositive
    hpairedReference₀ hpairedReference₁
  apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
  · exact fun inputLength => hvalues inputLength Work.limit₀
  · intro inputLength count hcount
    rw [emitReadNextConnector_binaryForValues _ (hinvariant inputLength)]
    simp [Work.available, Work.reference₀, Work.loop₀]
    have hlimit := hvalues inputLength Work.limit₀
    have hstart := hloop inputLength
    simp only [BinaryRoutine.binaryForCount] at hcount
    simp only [Work.limit₀, Work.loop₀] at hcount hlimit hstart
    omega
  · exact hbody

private theorem emitReadNextConnector_preserves_loop₀
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values) :
    emitReadNextConnector.effect values Work.loop₀ = values Work.loop₀ := by
  rw [emitReadNextConnector_effect_of_invariant values hinvariant]
  simp [show Work.loop₀ ≠ Work.available by decide,
    show Work.loop₀ ≠ Work.reference₀ by decide]

private theorem emitReadNextConnector_preserves_limit₀
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values) :
    emitReadNextConnector.effect values Work.limit₀ = values Work.limit₀ := by
  rw [emitReadNextConnector_effect_of_invariant values hinvariant]
  simp [show Work.limit₀ ≠ Work.available by decide,
    show Work.limit₀ ≠ Work.reference₀ by decide]

private theorem emitReadNextConnectors_requires_of_invariant
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values)
    (hle : values Work.loop₀ ≤ values Work.limit₀)
    (hreference : ∀ count,
      count < BinaryRoutine.binaryForCount Work.loop₀ Work.limit₀ values →
        3 ≤ values Work.reference₀ - 3 * count)
    (havailable : 1 ≤ values Work.available) :
    (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
      Work.limit₀).requires values := by
  refine ⟨by decide, hle, ?_⟩
  intro count hcount
  dsimp only
  generalize hcurrentEq :
    BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ values
      count = current
  have hcurrent : ReadConnectorInvariant current :=
    hcurrentEq ▸ emitReadNextConnector_binaryForValues_invariant values
      hinvariant count
  have hcurrentValues := emitReadNextConnector_binaryForValues values
    hinvariant count
  have hreferenceCurrent : 3 ≤ current Work.reference₀ := by
    rw [← hcurrentEq, hcurrentValues]
    simpa [Work.available, Work.reference₀, Work.loop₀] using
      hreference count hcount
  have havailableCurrent : 1 ≤ current Work.available := by
    rw [← hcurrentEq, hcurrentValues]
    have havailable' : 1 ≤ values 5 := by
      simpa [Work.available] using havailable
    simp [Work.available, Work.reference₀, Work.loop₀]
    omega
  exact
    ⟨emitReadNextConnector_requires_internal current hreferenceCurrent
      hcurrent.copyCounter havailableCurrent hcurrent.emitCounter,
      emitReadNextConnector_preserves_loop₀ current hcurrent,
      emitReadNextConnector_preserves_limit₀ current hcurrent⟩

private theorem emitReadNextConnectors_effect_of_invariant
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values) :
    (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
      Work.limit₀).effect values =
      Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available +
              (values Work.limit₀ - values Work.loop₀)))
          Work.reference₀
            (values Work.reference₀ -
              3 * (values Work.limit₀ - values Work.loop₀)))
        Work.loop₀
          (values Work.loop₀ +
            (values Work.limit₀ - values Work.loop₀)) :=
  emitReadNextConnector_binaryForValues values hinvariant
    (values Work.limit₀ - values Work.loop₀)

private theorem prefixSize_fixedWidthSizeAt_of_le
    (count width upto : ℕ) (hupto : upto ≤ count) :
    prefixSize (fixedWidthSizeAt count width) upto = width * upto := by
  induction upto with
  | zero => simp [prefixSize]
  | succ upto ih =>
      have huptoLe : upto ≤ count := by omega
      have huptoLt : upto < count := by omega
      rw [prefixSize, ih huptoLe, fixedWidthSizeAt_of_lt huptoLt]
      ring

private theorem indexedReadConnector_eq
    (available count rank : ℕ) (hrank : rank < count) :
    indexedRightFoldConnector .or available count
        (fixedWidthSizeAt count 3) rank =
      { op := .or
        input₀ := available + 3 * (count - rank) - 1
        input₁ := available + 3 * count + rank
        negated₀ := false
        negated₁ := false } := by
  unfold indexedRightFoldConnector reverseMember
  dsimp only
  have hmemberEq : count - rank - 1 + 1 = count - rank := by omega
  rw [hmemberEq]
  rw [prefixSize_fixedWidthSizeAt_of_le count 3 (count - rank) (by omega),
    prefixSize_fixedWidthSizeAt_of_le count 3 count (by omega)]

private theorem binaryForEmitted_eq_indexedGateBlocks_bounded
    (body : BinaryRoutine n) (counterIdx : Fin n)
    (initial : BinaryValues n) (blockAt : ℕ → CircuitCode.RawCircuit)
    (count : ℕ)
    (hemitted : ∀ offset, offset < count →
      body.emitted
          (BinaryRoutine.binaryForValues body counterIdx initial offset) =
        (blockAt offset).flatMap CircuitCode.RawGate.encode) :
    BinaryRoutine.binaryForEmitted body counterIdx initial count =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted, indexedGateBlocks]
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted,
        ih (fun offset hoffset => hemitted offset (by omega)),
        hemitted count (by omega), indexedGateBlocks_succ_last]
      simp only [List.flatMap_append]

private theorem emitReadNextConnector_emitted_at_counter
    (initial : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant initial)
    (available memberCount offset : ℕ)
    (havailable : initial Work.available = available + 3 * memberCount + 2)
    (hreference :
      initial Work.reference₀ = available + 3 * memberCount - 1)
    (hrank : offset + 1 < memberCount) :
    emitReadNextConnector.emitted
        (BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀
          initial offset) =
      CircuitCode.RawGate.encode
        (indexedRightFoldConnector .or available memberCount
          (fixedWidthSizeAt memberCount 3) (offset + 1)) := by
  let current :=
    BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ initial
      offset
  have hcurrent := emitReadNextConnector_binaryForValues initial hinvariant
    offset
  have havailableCurrent :
      current Work.available = initial Work.available + offset := by
    change
      (BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ initial
        offset) Work.available = _
    rw [hcurrent]
    simp [Work.available, Work.reference₀, Work.loop₀]
  have hreferenceCurrent :
      current Work.reference₀ = initial Work.reference₀ - 3 * offset := by
    change
      (BinaryRoutine.binaryForValues emitReadNextConnector Work.loop₀ initial
        offset) Work.reference₀ = _
    rw [hcurrent]
    simp [Work.available, Work.reference₀, Work.loop₀]
  change emitReadNextConnector.emitted current = _
  rw [emitReadNextConnector_emitted_internal, havailableCurrent,
    hreferenceCurrent, havailable, hreference,
    indexedReadConnector_eq available memberCount (offset + 1) hrank]
  have hsplit :
      memberCount = offset + 1 + (memberCount - (offset + 1)) := by
    omega
  have hinput₀ :
      available + 3 * memberCount - 1 - 3 * offset - 3 =
        available + 3 * (memberCount - (offset + 1)) - 1 := by
    rw [hsplit]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hinput₁ :
      available + 3 * memberCount + 2 + offset - 1 =
        available + 3 * memberCount + (offset + 1) := by
    omega
  rw [hinput₀, hinput₁]

private theorem emitReadNextConnectors_emitted_of_invariant
    (values : BinaryValues WorkCount)
    (hinvariant : ReadConnectorInvariant values)
    (available memberCount : ℕ)
    (hloop : values Work.loop₀ = 1)
    (hlimit : values Work.limit₀ = memberCount)
    (havailable : values Work.available = available + 3 * memberCount + 2)
    (hreference :
      values Work.reference₀ = available + 3 * memberCount - 1)
    (hpositive : 0 < memberCount) :
    (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
      Work.limit₀).emitted values =
      (indexedGateBlocks (memberCount - 1) fun offset =>
        [indexedRightFoldConnector .or available memberCount
          (fixedWidthSizeAt memberCount 3) (offset + 1)]).flatMap
            CircuitCode.RawGate.encode := by
  change BinaryRoutine.binaryForEmitted emitReadNextConnector Work.loop₀
      values (values Work.limit₀ - values Work.loop₀) = _
  rw [hlimit, hloop]
  apply binaryForEmitted_eq_indexedGateBlocks_bounded
  intro offset hoffset
  simpa using emitReadNextConnector_emitted_at_counter values hinvariant
    available memberCount offset havailable hreference (by omega)

private theorem emitReadConnector_emitted_at_rank_zero
    (values : BinaryValues WorkCount) (available memberCount : ℕ)
    (havailable : values Work.available = available + 3 * memberCount + 1)
    (hreference :
      values Work.reference₀ = available + 3 * memberCount - 1)
    (hpositive : 0 < memberCount) :
    emitReadConnector.emitted values =
      CircuitCode.RawGate.encode
        (indexedRightFoldConnector .or available memberCount
          (fixedWidthSizeAt memberCount 3) 0) := by
  rw [emitReadConnector_emitted_internal,
    indexedReadConnector_eq available memberCount 0 hpositive]
  have havailable' : values 5 = available + 3 * memberCount + 1 := by
    simpa [Work.available] using havailable
  have hreference' : values 7 = available + 3 * memberCount - 1 := by
    simpa [Work.reference₀] using hreference
  simp [Work.available, Work.reference₀, havailable', hreference']

private theorem indexedGateBlocks_singleton
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate) :
    indexedGateBlocks count (fun index => [gateAt index]) =
      (List.range count).map gateAt := by
  induction count with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      rw [indexedGateBlocks_succ_last, List.range_succ, List.map_append, ih]
      rfl

private theorem indexedRightFoldConnectors_succ
    (op : AndOrOp) (available count : ℕ) (sizeAt : ℕ → ℕ) :
    indexedRightFoldConnectors op available (count + 1) sizeAt =
      [indexedRightFoldConnector op available (count + 1) sizeAt 0] ++
        indexedGateBlocks count (fun offset =>
          [indexedRightFoldConnector op available (count + 1) sizeAt
            (offset + 1)]) := by
  rw [show indexedRightFoldConnectors op available (count + 1) sizeAt =
      indexedGateBlocks (count + 1) (fun rank =>
        [indexedRightFoldConnector op available (count + 1) sizeAt rank]) by
    rw [indexedGateBlocks_singleton]
    rfl]
  rfl

private theorem ReadMemberInvariant.updateLimit₀
    (values : BinaryValues WorkCount) (amount : ℕ)
    (hinvariant : ReadMemberInvariant values) :
    ReadMemberInvariant (Function.update values Work.limit₀ amount) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.limit₀, Work.reference₀] using hinvariant.reference₀
  · simpa [Work.limit₀, Work.reference₁] using hinvariant.reference₁
  · simpa [Work.limit₀, Work.temporary₀] using hinvariant.temporary₀
  · simpa [Work.limit₀, Work.temporary₁] using hinvariant.temporary₁
  · simpa [Work.limit₀, Work.temporary₂] using hinvariant.temporary₂
  · simpa [Work.limit₀, Work.emitCounter] using hinvariant.emitCounter
  · simpa [Work.limit₀, Work.copyCounter] using hinvariant.copyCounter
  · simpa [Work.limit₀, Work.multiplyCounter] using
      hinvariant.multiplyCounter
  · simpa [Work.limit₀, Work.addCounter] using hinvariant.addCounter

private def readConnectorStartValues
    (values : BinaryValues WorkCount) : BinaryValues WorkCount :=
  Function.update
    (Function.update
      (Function.update
        (Function.update values Work.limit₀ (values Work.horizon + 1))
        Work.available
          (values Work.available + 3 * (values Work.horizon + 1) + 2))
      Work.reference₀
        (values Work.available + 3 * (values Work.horizon + 1) - 1))
    Work.loop₀ 1

private def readMembersDoneValues
    (values : BinaryValues WorkCount) : BinaryValues WorkCount :=
  Function.update
    (Function.update values Work.limit₀ (values Work.horizon + 1))
    Work.available
      (values Work.available + 3 * (values Work.horizon + 1))

private theorem readMembersDone_effect
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (BinaryRoutine.clear Work.position).effect
        ((emitReadMembers stateCount tapeCount).effect
          (setReadFormulaLimit.effect values)) =
      readMembersDoneValues values := by
  have hinvariant :=
    ReadMemberInvariant.updateLimit₀ values (values Work.horizon + 1)
      (ReadMemberInvariant.ofReadFormulaClean values hclean)
  rw [setReadFormulaLimit_effect_internal,
    emitReadMembers_effect_of_invariant stateCount tapeCount _ hinvariant]
  simp only [BinaryRoutine.clear]
  have hposition : values 30 = 0 := by
    simpa [Work.position] using hclean.position
  funext i
  by_cases hiposition : i = Work.position
  · subst i
    simpa [readMembersDoneValues, Work.horizon, Work.available, Work.limit₀,
      Work.position] using hposition.symm
  by_cases hiavailable : i = Work.available
  · subst i
    simp [readMembersDoneValues, hposition, Work.horizon,
      Work.available, Work.limit₀, Work.position]
  by_cases hilimit : i = Work.limit₀
  · subst i
    simp [readMembersDoneValues, hposition, Work.horizon,
      Work.available, Work.limit₀, Work.position]
  · simp [readMembersDoneValues, hiposition, hiavailable, hilimit]

private theorem readConnectorStartValues_invariant
    (values : BinaryValues WorkCount) (hclean : ReadFormulaClean values) :
    ReadConnectorInvariant (readConnectorStartValues values) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [readConnectorStartValues, Work.limit₀, Work.available,
      Work.reference₀, Work.reference₁, Work.loop₀] using
      hclean.reference₁
  · simpa [readConnectorStartValues, Work.limit₀, Work.available,
      Work.reference₀, Work.copyCounter, Work.loop₀] using
      hclean.copyCounter
  · simpa [readConnectorStartValues, Work.limit₀, Work.available,
      Work.reference₀, Work.emitCounter, Work.loop₀] using
      hclean.emitCounter

private theorem readFormula_prefix_effect
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (BinaryRoutine.set Work.loop₀ 1).effect
        (emitReadConnector.effect
          ((prepareRecentReference Work.reference₀ 2).effect
            (emitReadIdentity.effect
              ((BinaryRoutine.clear Work.position).effect
                ((emitReadMembers stateCount tapeCount).effect
                  (setReadFormulaLimit.effect values)))))) =
      readConnectorStartValues values := by
  rw [readMembersDone_effect stateCount tapeCount values hclean,
    emitReadIdentity_effect_internal, prepareRecentReference_effect,
    emitReadConnector_effect_internal]
  simp [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
    BinaryRoutine.addConst, readMembersDoneValues, readConnectorStartValues,
    Work.horizon, Work.available, Work.reference₀, Work.reference₁,
    Work.loop₀, Work.limit₀]
  funext i
  by_cases hireference₁ : i = Work.reference₁
  · subst i
    have hreference₁ : values 8 = 0 := by
      simpa [Work.reference₁] using hclean.reference₁
    simpa [Work.horizon, Work.available, Work.reference₀, Work.reference₁,
      Work.loop₀, Work.limit₀] using hreference₁.symm
  by_cases hiloop : i = Work.loop₀
  · subst i
    simp [Work.loop₀]
  by_cases hireference₀ : i = Work.reference₀
  · subst i
    simp [Work.reference₀]
  by_cases hiavailable : i = Work.available
  · subst i
    simp [Work.available]
  by_cases hilimit : i = Work.limit₀
  · subst i
    simp [Work.limit₀]
  · have havailable' : i ≠ 5 := by
      simpa [Work.available] using hiavailable
    have hreference₀' : i ≠ 7 := by
      simpa [Work.reference₀] using hireference₀
    have hreference₁' : i ≠ 8 := by
      simpa [Work.reference₁] using hireference₁
    have hloop' : i ≠ 14 := by
      simpa [Work.loop₀] using hiloop
    have hlimit' : i ≠ 15 := by
      simpa [Work.limit₀] using hilimit
    simp [havailable', hreference₀', hreference₁', hloop', hlimit']

private theorem readFormula_members_emitted
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadMembers stateCount tapeCount).emitted
        (setReadFormulaLimit.effect values) =
      (readFormulaMemberGates stateCount tapeCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.symbolIndex)).flatMap
          CircuitCode.RawGate.encode := by
  rw [setReadFormulaLimit_effect_internal]
  apply emitReadMembers_emitted_of_invariant
  · exact ReadMemberInvariant.updateLimit₀ values
      (values Work.horizon + 1)
      (ReadMemberInvariant.ofReadFormulaClean values hclean)
  · simpa [Work.limit₀, Work.position] using hclean.position
  · simp [Work.horizon, Work.limit₀]

private theorem readFormula_identity_emitted
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    emitReadIdentity.emitted
        ((BinaryRoutine.clear Work.position).effect
          ((emitReadMembers stateCount tapeCount).effect
            (setReadFormulaLimit.effect values))) =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.constant 0 false) := by
  rw [readMembersDone_effect stateCount tapeCount values hclean]
  apply emitReadIdentity_emitted_internal
  simpa [readMembersDoneValues, Work.limit₀, Work.available,
    Work.reference₀] using hclean.reference₀

private theorem readFormula_firstConnector_emitted
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    emitReadConnector.emitted
        ((prepareRecentReference Work.reference₀ 2).effect
          (emitReadIdentity.effect
            ((BinaryRoutine.clear Work.position).effect
              ((emitReadMembers stateCount tapeCount).effect
                (setReadFormulaLimit.effect values))))) =
      CircuitCode.RawGate.encode
        (indexedRightFoldConnector .or (values Work.available)
          (values Work.horizon + 1)
          (fixedWidthSizeAt (values Work.horizon + 1) 3) 0) := by
  rw [readMembersDone_effect stateCount tapeCount values hclean,
    emitReadIdentity_effect_internal, prepareRecentReference_effect]
  apply emitReadConnector_emitted_at_rank_zero
  · simp [readMembersDoneValues, Work.horizon, Work.available,
      Work.reference₀, Work.limit₀]
  · simp [readMembersDoneValues, Work.horizon, Work.available,
      Work.reference₀, Work.limit₀]
  · omega

private theorem readFormula_connectorTail_emitted
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
      Work.limit₀).emitted
        ((BinaryRoutine.set Work.loop₀ 1).effect
          (emitReadConnector.effect
            ((prepareRecentReference Work.reference₀ 2).effect
              (emitReadIdentity.effect
                ((BinaryRoutine.clear Work.position).effect
                  ((emitReadMembers stateCount tapeCount).effect
                    (setReadFormulaLimit.effect values))))))) =
      (indexedGateBlocks (values Work.horizon) fun offset =>
        [indexedRightFoldConnector .or (values Work.available)
          (values Work.horizon + 1)
          (fixedWidthSizeAt (values Work.horizon + 1) 3)
          (offset + 1)]).flatMap CircuitCode.RawGate.encode := by
  rw [readFormula_prefix_effect stateCount tapeCount values hclean]
  have htail := emitReadNextConnectors_emitted_of_invariant
    (readConnectorStartValues values)
    (readConnectorStartValues_invariant values hclean)
    (values Work.available) (values Work.horizon + 1)
    (by simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀])
    (by simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀])
    (by simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀])
    (by simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀]) (by omega)
  simpa using htail

theorem emitReadFormula_spaceBoundByWidth_internal
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, ReadFormulaClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hfrontier : ∀ inputLength,
      values inputLength Work.available +
          (4 * (values inputLength Work.horizon + 1) + 1) ≤
        width inputLength)
    (hheadCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
      transitionHeadRef stateCount (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength)
    (hcellCap : ∀ inputLength position,
      position ≤ values inputLength Work.horizon →
      transitionCellRef stateCount tapeCount
            (values inputLength Work.horizon)
            (values inputLength Work.configBase)
            (values inputLength Work.tapeIndex) position
            (values inputLength Work.symbolIndex) +
          (values inputLength Work.tapeIndex *
                (values inputLength Work.horizon + 2) + position) +
          (values inputLength Work.horizon + 2) + tapeCount +
          values inputLength Work.tapeIndex + 4 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitReadFormula stateCount tapeCount) initialSpace values width := by
  have hhorizonOne : ∀ inputLength,
      values inputLength Work.horizon + 1 ≤ width inputLength := by
    intro inputLength
    have hcap := hcellCap inputLength 0 (Nat.zero_le _)
    omega
  have hfour : ∀ inputLength, 4 ≤ width inputLength := by
    intro inputLength
    have hcap := hcellCap inputLength 0 (Nat.zero_le _)
    omega
  let r₁ := setReadFormulaLimit
  let r₂ := emitReadMembers stateCount tapeCount
  let r₃ := BinaryRoutine.clear Work.position
  let r₄ := emitReadIdentity
  let r₅ := prepareRecentReference Work.reference₀ 2
  let r₆ := emitReadConnector
  let r₇ := BinaryRoutine.set Work.loop₀ 1
  let r₈ := BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
    Work.limit₀
  let r₉ := BinaryRoutine.clear Work.loop₀
  let r₁₀ := BinaryRoutine.clear Work.limit₀
  let r₁₁ := BinaryRoutine.clear Work.reference₀
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₁.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₂.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₃.effect (values₂ inputLength)
  let values₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₄.effect (values₃ inputLength)
  let values₅ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₅.effect (values₄ inputLength)
  let values₆ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₆.effect (values₅ inputLength)
  let values₇ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₇.effect (values₆ inputLength)
  let values₈ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₈.effect (values₇ inputLength)
  let values₉ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₉.effect (values₈ inputLength)
  let values₁₀ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₁₀.effect (values₉ inputLength)
  let values₁₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    r₁₁.effect (values₁₀ inputLength)
  have h₁ : BinaryRoutine.SpaceBoundByWidthAt r₁ initialSpace values
      width :=
    setReadFormulaLimit_spaceBoundByWidthAt hvalues hhorizonOne
  have hvalues₁ : ∀ inputLength index,
      values₁ inputLength index ≤ width inputLength := by
    intro inputLength
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal]
    exact BinaryRoutine.values_update_le Work.limit₀
      (hvalues inputLength) (hhorizonOne inputLength)
  have hinvariant₁ : ∀ inputLength,
      ReadMemberInvariant (values₁ inputLength) := by
    intro inputLength
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal]
    exact ReadMemberInvariant.updateLimit₀ _ _
      (ReadMemberInvariant.ofReadFormulaClean _ (hclean inputLength))
  have hposition₁ : ∀ inputLength,
      values₁ inputLength Work.position < values₁ inputLength Work.limit₀ := by
    intro inputLength
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal]
    have hposition := (hclean inputLength).position
    simp [Work.horizon, Work.limit₀, Work.position]
    change values inputLength Work.position ≤
      values inputLength Work.horizon
    rw [hposition]
    exact Nat.zero_le _
  have havailable₁ : ∀ inputLength,
      values₁ inputLength Work.available +
            3 * (values₁ inputLength Work.limit₀ -
              values₁ inputLength Work.position) +
          2 ≤
        width inputLength := by
    intro inputLength
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal]
    have hposition := (hclean inputLength).position
    have hbound := hfrontier inputLength
    simp only [Work.position] at hposition
    simp [Work.horizon, Work.available, Work.limit₀, Work.position]
      at hbound ⊢
    omega
  have hheadCap₁ : ∀ inputLength position,
      values₁ inputLength Work.position ≤ position →
      position < values₁ inputLength Work.limit₀ →
      transitionHeadRef stateCount (values₁ inputLength Work.horizon)
            (values₁ inputLength Work.configBase)
            (values₁ inputLength Work.tapeIndex) position +
          values₁ inputLength Work.tapeIndex +
          values₁ inputLength Work.horizon + 1 ≤
        width inputLength := by
    intro inputLength position _ hposition
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal] at hposition ⊢
    have hposition' : position ≤ values inputLength Work.horizon := by
      simpa [Work.horizon, Work.limit₀] using hposition
    simpa [Work.horizon, Work.limit₀, Work.configBase, Work.tapeIndex,
      Work.position] using hheadCap inputLength position hposition'
  have hcellCap₁ : ∀ inputLength position,
      values₁ inputLength Work.position ≤ position →
      position < values₁ inputLength Work.limit₀ →
      transitionCellRef stateCount tapeCount
            (values₁ inputLength Work.horizon)
            (values₁ inputLength Work.configBase)
            (values₁ inputLength Work.tapeIndex) position
            (values₁ inputLength Work.symbolIndex) +
          (values₁ inputLength Work.tapeIndex *
                (values₁ inputLength Work.horizon + 2) + position) +
          (values₁ inputLength Work.horizon + 2) + tapeCount +
          values₁ inputLength Work.tapeIndex + 4 ≤
        width inputLength := by
    intro inputLength position _ hposition
    rw [show values₁ inputLength = r₁.effect (values inputLength) by rfl,
      show r₁ = setReadFormulaLimit by rfl,
      setReadFormulaLimit_effect_internal] at hposition ⊢
    have hposition' : position ≤ values inputLength Work.horizon := by
      simpa [Work.horizon, Work.limit₀] using hposition
    simpa [Work.horizon, Work.limit₀, Work.configBase, Work.tapeIndex,
      Work.position, Work.symbolIndex] using
        hcellCap inputLength position hposition'
  have h₂ : BinaryRoutine.SpaceBoundByWidthAt r₂ initialSpace values₁
      width :=
    emitReadMembers_spaceBoundByWidthAt stateCount tapeCount hinvariant₁
      hvalues₁ hposition₁ havailable₁ hheadCap₁ hcellCap₁
  have hposition₂ : ∀ inputLength,
      values₂ inputLength Work.position ≤ width inputLength := by
    intro inputLength
    rw [show values₂ inputLength = r₂.effect (values₁ inputLength) by rfl,
      show r₂ = emitReadMembers stateCount tapeCount by rfl,
      emitReadMembers_effect_of_invariant stateCount tapeCount _
        (hinvariant₁ inputLength)]
    simp only [Function.update_self]
    rw [Nat.add_sub_of_le (Nat.le_of_lt (hposition₁ inputLength))]
    exact hvalues₁ inputLength Work.limit₀
  have h₃ : BinaryRoutine.SpaceBoundByWidthAt r₃ initialSpace values₂
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.position hposition₂
  have hvalues₃ (inputLength : ℕ) :
      values₃ inputLength = readMembersDoneValues (values inputLength) := by
    exact readMembersDone_effect stateCount tapeCount (values inputLength)
      (hclean inputLength)
  have h₄ : BinaryRoutine.SpaceBoundByWidthAt r₄ initialSpace values₃
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .and false true
      Work.emitCounter Work.available Work.reference₀ Work.reference₀
    · intro inputLength
      rw [hvalues₃]
      have hbound := hfrontier inputLength
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.limit₀] at hbound ⊢
      omega
    · intro inputLength
      rw [hvalues₃]
      simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.reference₀] using hvalues inputLength Work.reference₀
    · intro inputLength
      rw [hvalues₃]
      simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.reference₀] using hvalues inputLength Work.reference₀
  have h₅ : BinaryRoutine.SpaceBoundByWidthAt r₅ initialSpace values₄
      width := by
    apply prepareRecentReference_spaceBoundByWidth Work.reference₀ 2
    · intro inputLength
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      have hbound := hfrontier inputLength
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.limit₀] at hbound ⊢
      omega
    · intro inputLength
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.reference₀] using hvalues inputLength Work.reference₀
    · intro inputLength
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.limit₀]
      omega
  have h₆ : BinaryRoutine.SpaceBoundByWidthAt r₆ initialSpace values₅
      width := by
    apply emitReadConnector_spaceBoundByWidth_internal
    · intro inputLength
      simp only [values₅, r₅, prepareRecentReference_effect]
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      have hbound := hfrontier inputLength
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀] at hbound ⊢
      omega
    · intro inputLength
      simp only [values₅, r₅, prepareRecentReference_effect]
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀]
    · intro inputLength
      simp only [values₅, r₅, prepareRecentReference_effect]
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      have hbound := hfrontier inputLength
      simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀] at hbound ⊢
      omega
    · intro inputLength
      simp only [values₅, r₅, prepareRecentReference_effect]
      simp only [values₄, r₄, emitReadIdentity_effect_internal]
      rw [hvalues₃]
      simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.reference₀, Work.reference₁] using
          hvalues inputLength Work.reference₁
  have h₇ : BinaryRoutine.SpaceBoundByWidthAt r₇ initialSpace values₆
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.set Work.loop₀ 1
    · intro inputLength
      simp [values₆, r₆, emitReadConnector_effect_internal, values₅,
        r₅, prepareRecentReference_effect, values₄, r₄,
        emitReadIdentity_effect_internal]
      rw [hvalues₃]
      simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.reference₀, Work.reference₁, Work.loop₀] using
          hvalues inputLength Work.loop₀
    · exact fun inputLength => (hfour inputLength).trans' (by omega)
  have hvalues₇ (inputLength : ℕ) :
      values₇ inputLength = readConnectorStartValues (values inputLength) := by
    exact readFormula_prefix_effect stateCount tapeCount (values inputLength)
      (hclean inputLength)
  have hinvariant₇ : ∀ inputLength,
      ReadConnectorInvariant (values₇ inputLength) := by
    intro inputLength
    rw [hvalues₇]
    exact readConnectorStartValues_invariant _ (hclean inputLength)
  have hallValues₇ : ∀ inputLength index,
      values₇ inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [hvalues₇]
    have hlimit := hhorizonOne inputLength
    have havailable : values inputLength Work.available +
          3 * (values inputLength Work.horizon + 1) + 2 ≤
        width inputLength := by
      have hbound := hfrontier inputLength
      omega
    have hreference : values inputLength Work.available +
          3 * (values inputLength Work.horizon + 1) - 1 ≤
        width inputLength := by
      have hpre : values inputLength Work.available +
            3 * (values inputLength Work.horizon + 1) ≤
          width inputLength := by
        have hbound := hfrontier inputLength
        omega
      exact (Nat.sub_le _ _).trans hpre
    have hlimitValues := BinaryRoutine.values_update_le Work.limit₀
      (hvalues inputLength) hlimit
    have havailableValues := BinaryRoutine.values_update_le Work.available
      hlimitValues havailable
    have hreferenceValues := BinaryRoutine.values_update_le Work.reference₀
      havailableValues hreference
    have hone : 1 ≤ width inputLength := by
      have := hfour inputLength
      omega
    have hloopValues := BinaryRoutine.values_update_le Work.loop₀
      hreferenceValues hone
    exact hloopValues index
  have hloop₇ : ∀ inputLength,
      values₇ inputLength Work.loop₀ ≤ values₇ inputLength Work.limit₀ := by
    intro inputLength
    rw [hvalues₇]
    simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀]
  have havailable₇ : ∀ inputLength,
      values₇ inputLength Work.available +
          (values₇ inputLength Work.limit₀ -
            values₇ inputLength Work.loop₀) ≤
        width inputLength := by
    intro inputLength
    rw [hvalues₇]
    have hbound := hfrontier inputLength
    simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀] at hbound ⊢
    omega
  have havailablePositive₇ : ∀ inputLength,
      1 ≤ values₇ inputLength Work.available := by
    intro inputLength
    rw [hvalues₇]
    simp [readConnectorStartValues, Work.horizon, Work.available,
      Work.reference₀, Work.loop₀, Work.limit₀]
  have h₈ : BinaryRoutine.SpaceBoundByWidthAt r₈ initialSpace values₇
      width :=
    emitReadNextConnectors_spaceBoundByWidthAt hinvariant₇ hallValues₇
      hloop₇ havailable₇ havailablePositive₇
  have hloop₈ : ∀ inputLength,
      values₈ inputLength Work.loop₀ ≤ width inputLength := by
    intro inputLength
    rw [show values₈ inputLength = r₈.effect (values₇ inputLength) by rfl,
      show r₈ = BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
        Work.limit₀ by rfl,
      emitReadNextConnectors_effect_of_invariant _
        (hinvariant₇ inputLength)]
    simp only [Function.update_self]
    rw [Nat.add_sub_of_le (hloop₇ inputLength)]
    exact hallValues₇ inputLength Work.limit₀
  have h₉ : BinaryRoutine.SpaceBoundByWidthAt r₉ initialSpace values₈
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.loop₀ hloop₈
  have hlimit₉ : ∀ inputLength,
      values₉ inputLength Work.limit₀ ≤ width inputLength := by
    intro inputLength
    simp [values₉, r₉, BinaryRoutine.clear, Work.loop₀, Work.limit₀]
    rw [show values₈ inputLength = r₈.effect (values₇ inputLength) by rfl,
      show r₈ = BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
        Work.limit₀ by rfl,
      emitReadNextConnectors_effect_of_invariant _
        (hinvariant₇ inputLength)]
    simp [Work.available, Work.reference₀, Work.loop₀]
    exact hallValues₇ inputLength Work.limit₀
  have h₁₀ : BinaryRoutine.SpaceBoundByWidthAt r₁₀ initialSpace values₉
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₀ hlimit₉
  have hreference₈ : ∀ inputLength,
      values₈ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    rw [show values₈ inputLength = r₈.effect (values₇ inputLength) by rfl,
      show r₈ = BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
        Work.limit₀ by rfl,
      emitReadNextConnectors_effect_of_invariant _
        (hinvariant₇ inputLength)]
    have hsub : values₇ inputLength Work.reference₀ -
          3 * (values₇ inputLength Work.limit₀ -
            values₇ inputLength Work.loop₀) ≤
        width inputLength :=
      (Nat.sub_le _ _).trans
        (hallValues₇ inputLength Work.reference₀)
    simpa [Work.available, Work.reference₀, Work.loop₀] using hsub
  have hreference₁₀ : ∀ inputLength,
      values₁₀ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    have hreference₉ :
        values₉ inputLength Work.reference₀ ≤ width inputLength := by
      simpa [values₉, r₉, BinaryRoutine.clear, Work.loop₀,
        Work.reference₀] using hreference₈ inputLength
    simpa [values₁₀, r₁₀, BinaryRoutine.clear, Work.limit₀,
      Work.reference₀] using hreference₉
  have h₁₁ : BinaryRoutine.SpaceBoundByWidthAt r₁₁ initialSpace values₁₀
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₀ hreference₁₀
  rw [emitReadFormula]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, trivial⟩

theorem emitReadFormula_requires_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).requires values := by
  have hlimit : setReadFormulaLimit.requires values :=
    setReadFormulaLimit_requires_internal values hclean.copyCounter
  have hmemberInvariant :=
    ReadMemberInvariant.updateLimit₀ values (values Work.horizon + 1)
      (ReadMemberInvariant.ofReadFormulaClean values hclean)
  have hmembers :
      (emitReadMembers stateCount tapeCount).requires
        (setReadFormulaLimit.effect values) := by
    rw [setReadFormulaLimit_effect_internal]
    apply emitReadMembers_requires_of_invariant stateCount tapeCount _
      hmemberInvariant
    have hposition : values 30 = 0 := by
      simpa [Work.position] using hclean.position
    simp [Work.limit₀, Work.position, hposition]
  have hidentity :
      emitReadIdentity.requires
        ((BinaryRoutine.clear Work.position).effect
          ((emitReadMembers stateCount tapeCount).effect
            (setReadFormulaLimit.effect values))) := by
    apply emitReadIdentity_requires_internal
    rw [readMembersDone_effect stateCount tapeCount values hclean]
    simpa [readMembersDoneValues, Work.limit₀, Work.available,
      Work.emitCounter] using hclean.emitCounter
  have hprepare :
      (prepareRecentReference Work.reference₀ 2).requires
        (emitReadIdentity.effect
          ((BinaryRoutine.clear Work.position).effect
            ((emitReadMembers stateCount tapeCount).effect
              (setReadFormulaLimit.effect values)))) := by
    rw [readMembersDone_effect stateCount tapeCount values hclean,
      emitReadIdentity_effect_internal]
    rw [prepareRecentReference_requires Work.reference₀ 2 _
      (by decide) (by decide) (by decide)]
    constructor
    · simpa [readMembersDoneValues, Work.limit₀, Work.available,
        Work.copyCounter] using hclean.copyCounter
    · simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.limit₀]
      omega
  have hconnector :
      emitReadConnector.requires
        ((prepareRecentReference Work.reference₀ 2).effect
          (emitReadIdentity.effect
            ((BinaryRoutine.clear Work.position).effect
              ((emitReadMembers stateCount tapeCount).effect
                (setReadFormulaLimit.effect values))))) := by
    rw [readMembersDone_effect stateCount tapeCount values hclean,
      emitReadIdentity_effect_internal, prepareRecentReference_effect]
    apply emitReadConnector_requires_internal
    · simpa [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀, Work.copyCounter] using
        hclean.copyCounter
    · simp [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀]
    · simpa [readMembersDoneValues, Work.horizon, Work.available,
        Work.reference₀, Work.limit₀, Work.emitCounter] using
        hclean.emitCounter
  have hconnectors :
      (BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
        Work.limit₀).requires
          ((BinaryRoutine.set Work.loop₀ 1).effect
            (emitReadConnector.effect
              ((prepareRecentReference Work.reference₀ 2).effect
                (emitReadIdentity.effect
                  ((BinaryRoutine.clear Work.position).effect
                    ((emitReadMembers stateCount tapeCount).effect
                      (setReadFormulaLimit.effect values))))))) := by
    rw [readFormula_prefix_effect stateCount tapeCount values hclean]
    apply emitReadNextConnectors_requires_of_invariant
      (readConnectorStartValues values)
      (readConnectorStartValues_invariant values hclean)
    · simp [readConnectorStartValues, Work.horizon, Work.available,
        Work.reference₀, Work.loop₀, Work.limit₀]
    · intro count hcount
      simp [BinaryRoutine.binaryForCount, readConnectorStartValues,
        Work.horizon, Work.available, Work.reference₀, Work.loop₀,
        Work.limit₀] at hcount ⊢
      omega
    · simp [readConnectorStartValues, Work.horizon, Work.available,
        Work.reference₀, Work.loop₀, Work.limit₀]
  simp only [emitReadFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  exact ⟨hlimit, hmembers, trivial, hidentity, hprepare, hconnector,
    (by exact ⟨trivial, trivial⟩), hconnectors, trivial,
    trivial, trivial, trivial⟩

theorem emitReadFormula_effect_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).effect values =
      Function.update values Work.available
        (values Work.available + (4 * (values Work.horizon + 1) + 1)) := by
  rw [emitReadFormula]
  change (BinaryRoutine.clear Work.reference₀).effect
      ((BinaryRoutine.clear Work.limit₀).effect
        ((BinaryRoutine.clear Work.loop₀).effect
          ((BinaryRoutine.binaryFor emitReadNextConnector Work.loop₀
            Work.limit₀).effect
            ((BinaryRoutine.set Work.loop₀ 1).effect
              (emitReadConnector.effect
                ((prepareRecentReference Work.reference₀ 2).effect
                  (emitReadIdentity.effect
                    ((BinaryRoutine.clear Work.position).effect
                      ((emitReadMembers stateCount tapeCount).effect
                        (setReadFormulaLimit.effect values)))))))))) = _
  rw [readFormula_prefix_effect stateCount tapeCount values hclean]
  rw [emitReadNextConnectors_effect_of_invariant _
    (readConnectorStartValues_invariant values hclean)]
  simp [BinaryRoutine.clear, readConnectorStartValues, Work.horizon,
    Work.available, Work.reference₀, Work.loop₀, Work.limit₀]
  funext i
  by_cases hiavailable : i = Work.available
  · subst i
    simp [Work.available]
    omega
  by_cases hireference₀ : i = Work.reference₀
  · subst i
    have hreference₀ : values 7 = 0 := by
      simpa [Work.reference₀] using hclean.reference₀
    simpa [Work.available, Work.reference₀, Work.loop₀, Work.limit₀]
      using hreference₀.symm
  by_cases hiloop : i = Work.loop₀
  · subst i
    have hloop₀ : values 14 = 0 := by
      simpa [Work.loop₀] using hclean.loop₀
    simpa [Work.available, Work.reference₀, Work.loop₀, Work.limit₀]
      using hloop₀.symm
  by_cases hilimit : i = Work.limit₀
  · subst i
    have hlimit₀ : values 15 = 0 := by
      simpa [Work.limit₀] using hclean.limit₀
    simpa [Work.available, Work.reference₀, Work.loop₀, Work.limit₀]
      using hlimit₀.symm
  · have havailable' : i ≠ 5 := by
      simpa [Work.available] using hiavailable
    have hreference₀' : i ≠ 7 := by
      simpa [Work.reference₀] using hireference₀
    have hloop' : i ≠ 14 := by
      simpa [Work.loop₀] using hiloop
    have hlimit' : i ≠ 15 := by
      simpa [Work.limit₀] using hilimit
    simp [havailable', hreference₀', hloop', hlimit']

theorem emitReadFormula_emitted_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hclean : ReadFormulaClean values) :
    (emitReadFormula stateCount tapeCount).emitted values =
      (readFormulaSchedule stateCount tapeCount (values Work.horizon)
        (values Work.configBase) (values Work.available)
        (values Work.tapeIndex) (values Work.symbolIndex)).flatMap
          CircuitCode.RawGate.encode := by
  simp only [emitReadFormula, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.identity, BinaryRoutine.emitBits]
  rw [setReadFormulaLimit_emitted_internal,
    readFormula_members_emitted stateCount tapeCount values hclean,
    readFormula_identity_emitted stateCount tapeCount values hclean,
    prepareRecentReference_emitted,
    readFormula_firstConnector_emitted stateCount tapeCount values hclean,
    readFormula_connectorTail_emitted stateCount tapeCount values hclean]
  simp [BinaryRoutine.clear, BinaryRoutine.set, BinaryRoutine.addConst,
    BinaryRoutine.seq]
  unfold readFormulaSchedule
  rw [indexedRightFoldConnectors_succ .or (values Work.available)
    (values Work.horizon)
    (fixedWidthSizeAt (values Work.horizon + 1) 3)]
  simp only [List.flatMap_append, List.flatMap_singleton]
  simp [List.append_assoc]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
