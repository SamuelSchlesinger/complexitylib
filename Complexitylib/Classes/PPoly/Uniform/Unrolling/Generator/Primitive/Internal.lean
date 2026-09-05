/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Primitive.Defs
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Arithmetic
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.List
public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.SpaceBounds
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Transition.Case.Defs
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

/-!
# Direct-unrolling generator primitives -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

/-- Arithmetic consequences of the single head-reference width envelope. -/
private structure HeadReferenceWidthBounds (stateCount configBase horizon
    tapeIndex position width : ℕ) : Prop where
  stateCount_le : stateCount ≤ width
  stateBase_le : stateCount + configBase ≤ width
  one_le : 1 ≤ width
  horizonOne_le : horizon + 1 ≤ width
  multiplyIntermediate_le :
    stateCount + configBase + tapeIndex * (horizon + 1) + tapeIndex ≤ width
  finalReference_le :
    stateCount + configBase + tapeIndex * (horizon + 1) + position ≤ width

private theorem HeadReferenceWidthBounds.of_cap
    (stateCount configBase horizon tapeIndex position width : ℕ)
    (hcap : configBase + stateCount + tapeIndex * (horizon + 1) +
        tapeIndex + position + horizon + 1 ≤ width) :
    HeadReferenceWidthBounds stateCount configBase horizon tapeIndex position
      width := by
  constructor <;> nlinarith

/-- Arithmetic consequences of the single cell-reference width envelope. -/
private structure CellReferenceWidthBounds (stateCount tapeCount configBase
    horizon tapeIndex position symbolIndex width : ℕ) : Prop where
  stateCount_le : stateCount ≤ width
  stateBase_le : stateCount + configBase ≤ width
  one_le : 1 ≤ width
  horizonOne_le : horizon + 1 ≤ width
  tapeCount_le : tapeCount ≤ width
  baseMultiplyIntermediate_le :
    stateCount + configBase + (horizon + 1) * tapeCount +
      (horizon + 1) ≤ width
  horizonTwo_le : horizon + 2 ≤ width
  offsetMultiplyIntermediate_le :
    tapeIndex * (horizon + 2) + tapeIndex ≤ width
  offset_le : tapeIndex * (horizon + 2) + position ≤ width
  four_le : 4 ≤ width
  finalMultiplyIntermediate_le :
    stateCount + configBase + tapeCount * (horizon + 1) +
        (tapeIndex * (horizon + 2) + position) * 4 +
      (tapeIndex * (horizon + 2) + position) ≤ width
  finalReference_le :
    stateCount + configBase + tapeCount * (horizon + 1) +
        (tapeIndex * (horizon + 2) + position) * 4 + symbolIndex ≤ width

private theorem CellReferenceWidthBounds.of_cap
    (stateCount tapeCount configBase horizon tapeIndex position symbolIndex
      width : ℕ)
    (hcap : configBase + stateCount + tapeCount * (horizon + 1) +
        (tapeIndex * (horizon + 2) + position) * 4 +
        (tapeIndex * (horizon + 2) + position) + symbolIndex +
        (horizon + 2) + tapeCount + tapeIndex + 4 ≤ width) :
    CellReferenceWidthBounds stateCount tapeCount configBase horizon tapeIndex
      position symbolIndex width := by
  constructor <;> nlinarith

private theorem repeatBinaryPred_effect (reference : Fin WorkCount) :
    ∀ offset values,
      (BinaryRoutine.repeatRoutine offset
        (BinaryRoutine.binaryPred reference)).effect values =
      Function.update values reference (values reference - offset) := by
  intro offset
  induction offset with
  | zero =>
      intro values
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits]
  | succ offset ih =>
      intro values
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.binaryPred]
      change
        (BinaryRoutine.repeatRoutine offset
          (BinaryRoutine.binaryPred reference)).effect
            (Function.update values reference (values reference - 1)) = _
      rw [ih]
      funext i
      by_cases hi : i = reference
      · subst i
        simp
        omega
      · simp [hi]

private theorem repeatBinaryPred_emitted (reference : Fin WorkCount) :
    ∀ offset values,
      (BinaryRoutine.repeatRoutine offset
        (BinaryRoutine.binaryPred reference)).emitted values = [] := by
  intro offset
  induction offset with
  | zero =>
      intro values
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits]
  | succ offset ih =>
      intro values
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.binaryPred]
      change [] ++
        (BinaryRoutine.repeatRoutine offset
          (BinaryRoutine.binaryPred reference)).emitted
            (Function.update values reference (values reference - 1)) = []
      rw [ih]
      rfl

private theorem repeatBinaryPred_requires (reference : Fin WorkCount) :
    ∀ offset values,
      (BinaryRoutine.repeatRoutine offset
        (BinaryRoutine.binaryPred reference)).requires values ↔
      offset ≤ values reference := by
  intro offset
  induction offset with
  | zero =>
      intro values
      simp [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList,
        BinaryRoutine.identity, BinaryRoutine.emitBits]
  | succ offset ih =>
      intro values
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.binaryPred]
      change 0 < values reference ∧
        (BinaryRoutine.repeatRoutine offset
          (BinaryRoutine.binaryPred reference)).requires
            (Function.update values reference (values reference - 1)) ↔ _
      rw [ih]
      simp only [Function.update_self]
      omega

private theorem repeatBinaryPred_spaceBoundByWidth
    (reference : Fin WorkCount) : ∀ offset,
    ∀ {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
      {width : ℕ → ℕ},
      (∀ inputLength, offset ≤ values inputLength reference) →
      (∀ inputLength,
        values inputLength reference ≤ width inputLength) →
      BinaryRoutine.SpaceBoundByWidthAt
        (BinaryRoutine.repeatRoutine offset
          (BinaryRoutine.binaryPred reference)) initialSpace values width := by
  intro offset
  induction offset with
  | zero =>
      intro initialSpace values width _ _
      simpa [BinaryRoutine.repeatRoutine, BinaryRoutine.seqList] using
        (BinaryRoutine.SpaceBoundByWidthAt.identity
          (initialSpace := initialSpace) (values := values) (width := width))
  | succ offset ih =>
      intro initialSpace values width hfit hreference
      rw [BinaryRoutine.repeatRoutine, List.replicate_succ,
        BinaryRoutine.seqList]
      apply BinaryRoutine.SpaceBoundByWidthAt.seq
      · apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
        intro inputLength
        have hpositive : 0 < values inputLength reference := by
          have := hfit inputLength
          omega
        have hpred : values inputLength reference - 1 + 1 =
            values inputLength reference := by
          omega
        rw [hpred]
        exact hreference inputLength
      · apply ih
        · intro inputLength
          simp only [BinaryRoutine.binaryPred, Function.update_self]
          have := hfit inputLength
          omega
        · intro inputLength
          simp only [BinaryRoutine.binaryPred, Function.update_self]
          exact (Nat.sub_le _ _).trans (hreference inputLength)

theorem prepareRecentReference_spaceBoundByWidth_internal
    (reference : Fin WorkCount) (offset : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference : ∀ inputLength,
      values inputLength reference ≤ width inputLength)
    (hoffset : ∀ inputLength,
      offset ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt (prepareRecentReference reference offset)
      initialSpace values width := by
  let copy := BinaryRoutine.binaryCopy Work.available reference
    Work.copyCounter
  let copied : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (values inputLength)
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.binaryCopy Work.available reference
      Work.copyCounter havailable hreference
  have hrepeat : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.repeatRoutine offset (BinaryRoutine.binaryPred reference))
      initialSpace copied width := by
    apply repeatBinaryPred_spaceBoundByWidth reference offset
    · intro inputLength
      simpa [copied, copy, BinaryRoutine.binaryCopy] using
        hoffset inputLength
    · intro inputLength
      simp [copied, copy, BinaryRoutine.binaryCopy]
      exact havailable inputLength
  simpa [prepareRecentReference, copy, copied] using
    (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy hrepeat)

theorem prepareRecentReference_sound_internal
    (reference : Fin WorkCount) (offset : ℕ) :
    (prepareRecentReference reference offset).Sound :=
  (BinaryRoutine.binaryCopy_sound Work.available reference
    Work.copyCounter).seq
      (BinaryRoutine.repeatRoutine_sound offset
        (BinaryRoutine.binaryPred reference)
        (BinaryRoutine.binaryPred_sound reference))

theorem prepareRecentReference_requires_internal
    (reference : Fin WorkCount) (offset : ℕ)
    (values : BinaryValues WorkCount)
    (havailableReference : Work.available ≠ reference)
    (havailableCounter : Work.available ≠ Work.copyCounter)
    (hreferenceCounter : reference ≠ Work.copyCounter) :
    (prepareRecentReference reference offset).requires values ↔
      values Work.copyCounter = 0 ∧ offset ≤ values Work.available := by
  rw [prepareRecentReference, BinaryRoutine.seq]
  change
    ((Work.available ≠ reference ∧
        Work.available ≠ Work.copyCounter ∧
        reference ≠ Work.copyCounter ∧
        values Work.copyCounter = 0) ∧
      (BinaryRoutine.repeatRoutine offset
        (BinaryRoutine.binaryPred reference)).requires
          (Function.update values reference (values Work.available))) ↔ _
  rw [repeatBinaryPred_requires]
  simp [havailableReference, havailableCounter, hreferenceCounter]

theorem prepareRecentReference_effect_internal
    (reference : Fin WorkCount) (offset : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareRecentReference reference offset).effect values =
      Function.update values reference (values Work.available - offset) := by
  rw [prepareRecentReference, BinaryRoutine.seq, repeatBinaryPred_effect]
  funext i
  by_cases hi : i = reference
  · subst i
    simp [BinaryRoutine.binaryCopy]
  · simp [BinaryRoutine.binaryCopy, hi]

theorem prepareRecentReference_emitted_internal
    (reference : Fin WorkCount) (offset : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareRecentReference reference offset).emitted values = [] := by
  rw [prepareRecentReference]
  change
    (BinaryRoutine.binaryCopy Work.available reference
      Work.copyCounter).emitted values ++
      (BinaryRoutine.repeatRoutine offset
        (BinaryRoutine.binaryPred reference)).emitted
          ((BinaryRoutine.binaryCopy Work.available reference
            Work.copyCounter).effect values) = []
  rw [repeatBinaryPred_emitted]
  rfl

theorem emitRecentGate_sound_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact prepareRecentReference_sound_internal Work.reference₀ offset₀
  · subst routine
    exact prepareRecentReference_sound_internal Work.reference₁ offset₁
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound op negated₀ negated₁
      Work.emitCounter Work.available Work.reference₀ Work.reference₁
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

theorem emitRecentGate_requires_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).requires
        values ↔
      values Work.copyCounter = 0 ∧
        offset₀ ≤ values Work.available ∧
        offset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 := by
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct
      Work.emitCounter Work.available Work.reference₀ Work.reference₁ := by
    refine
      { emitCounter_ne_available := by decide
        emitCounter_ne_input₀ := by decide
        emitCounter_ne_input₁ := by decide
        available_ne_input₀ := by decide
        available_ne_input₁ := by decide }
  simp [emitRecentGate, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference, BinaryRoutine.binaryCopy,
    repeatBinaryPred_requires, repeatBinaryPred_effect,
    BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₀, Work.reference₁, Work.emitCounter,
    Work.copyCounter]
  constructor
  · rintro ⟨⟨hcopy, hoffset₀⟩, ⟨_, hoffset₁⟩, _, hemit⟩
    exact ⟨hcopy, hoffset₀, hoffset₁, hemit⟩
  · rintro ⟨hcopy, hoffset₀, hoffset₁, hemit⟩
    exact ⟨⟨hcopy, hoffset₀⟩, ⟨hcopy, hoffset₁⟩, hdistinct, hemit⟩

theorem emitRecentGate_effect_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).effect
        values =
      Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available + 1)) Work.reference₀ 0)
        Work.reference₁ 0 := by
  simp [emitRecentGate, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect_internal, BinaryRoutine.emitRawGateStep,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    Work.available, Work.reference₀, Work.reference₁]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem emitRecentGate_spaceBoundByWidth_internal
    (op : AndOrOp) (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hoffset₀ : ∀ inputLength,
      offset₀ ≤ values inputLength Work.available)
    (hoffset₁ : ∀ inputLength,
      offset₁ ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitRecentGate op negated₀ negated₁ offset₀ offset₁)
      initialSpace values width := by
  let prepare₀ := prepareRecentReference Work.reference₀ offset₀
  let prepare₁ := prepareRecentReference Work.reference₁ offset₁
  let emit := BinaryRoutine.emitRawGateStep op negated₀ negated₁
    Work.emitCounter Work.available Work.reference₀ Work.reference₁
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare₀.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare₁.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (values₂ inputLength)
  let values₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.clear Work.reference₀).effect (values₃ inputLength)
  have hprepare₀ : BinaryRoutine.SpaceBoundByWidthAt prepare₀ initialSpace
      values width :=
    prepareRecentReference_spaceBoundByWidth_internal Work.reference₀ offset₀
      havailable hreference₀ hoffset₀
  have hvalues₁Available : ∀ inputLength,
      values₁ inputLength Work.available ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare₀, prepareRecentReference_effect_internal,
      Work.available, Work.reference₀] using havailable inputLength
  have hvalues₁Reference₁ : ∀ inputLength,
      values₁ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare₀, prepareRecentReference_effect_internal,
      Work.reference₀, Work.reference₁] using hreference₁ inputLength
  have hvalues₁Offset₁ : ∀ inputLength,
      offset₁ ≤ values₁ inputLength Work.available := by
    intro inputLength
    simpa [values₁, prepare₀, prepareRecentReference_effect_internal,
      Work.available, Work.reference₀] using hoffset₁ inputLength
  have hprepare₁ : BinaryRoutine.SpaceBoundByWidthAt prepare₁ initialSpace
      values₁ width :=
    prepareRecentReference_spaceBoundByWidth_internal Work.reference₁ offset₁
      hvalues₁Available hvalues₁Reference₁ hvalues₁Offset₁
  have hvalues₂Available : ∀ inputLength,
      values₂ inputLength Work.available ≤ width inputLength := by
    intro inputLength
    simpa [values₂, prepare₁, prepareRecentReference_effect_internal,
      Work.available, Work.reference₁] using hvalues₁Available inputLength
  have hvalues₂Reference₀ : ∀ inputLength,
      values₂ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    simp [values₂, prepare₁, prepareRecentReference_effect_internal,
      Work.reference₀, Work.reference₁]
    simp [values₁, prepare₀, prepareRecentReference_effect_internal,
      Work.reference₀]
    have := havailable inputLength
    omega
  have hvalues₂Reference₁ : ∀ inputLength,
      values₂ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simp [values₂, prepare₁, prepareRecentReference_effect_internal,
      Work.reference₁]
    have := hvalues₁Available inputLength
    omega
  have hemit : BinaryRoutine.SpaceBoundByWidthAt emit initialSpace values₂
      width :=
    BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep op negated₀ negated₁
      Work.emitCounter Work.available Work.reference₀ Work.reference₁
      hvalues₂Available hvalues₂Reference₀ hvalues₂Reference₁
  have hvalues₃Reference₀ : ∀ inputLength,
      values₃ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    simpa [values₃, emit, BinaryRoutine.emitRawGateStep,
      Work.available, Work.reference₀] using hvalues₂Reference₀ inputLength
  have hclear₀ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₀) initialSpace values₃ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₀
      hvalues₃Reference₀
  have hvalues₄Reference₁ : ∀ inputLength,
      values₄ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simp [values₄, values₃, emit, BinaryRoutine.clear,
      BinaryRoutine.emitRawGateStep, Work.available, Work.reference₀,
      Work.reference₁]
    exact hvalues₂Reference₁ inputLength
  have hclear₁ : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₁) initialSpace values₄ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₁
      hvalues₄Reference₁
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength =>
        (BinaryRoutine.clear Work.reference₁).effect (values₄ inputLength))
      width := BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hprepare₀
    (BinaryRoutine.SpaceBoundByWidthAt.seq hprepare₁
      (BinaryRoutine.SpaceBoundByWidthAt.seq hemit
        (BinaryRoutine.SpaceBoundByWidthAt.seq hclear₀
          (BinaryRoutine.SpaceBoundByWidthAt.seq hclear₁ hid))))
  simpa [emitRecentGate, BinaryRoutine.seqList, prepare₀, prepare₁, emit,
    values₁, values₂, values₃, values₄] using hroutine

theorem emitRecentGate_emitted_internal (op : AndOrOp)
    (negated₀ negated₁ : Bool) (offset₀ offset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitRecentGate op negated₀ negated₁ offset₀ offset₁).emitted
        values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available - offset₀
          input₁ := values Work.available - offset₁
          negated₀ := negated₀
          negated₁ := negated₁ } := by
  simp [emitRecentGate, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareRecentReference_effect_internal,
    prepareRecentReference_emitted_internal,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, Work.available,
    Work.reference₀, Work.reference₁]

theorem prepareStateReference_sound_internal (stateIndex : ℕ) :
    (prepareStateReference stateIndex).Sound :=
  (BinaryRoutine.set_sound Work.reference₀ stateIndex).seq
    (BinaryRoutine.add_sound Work.configBase Work.reference₀ Work.addCounter)

theorem prepareStateReference_requires_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).requires values ↔
      values Work.addCounter = 0 := by
  simp [prepareStateReference, BinaryRoutine.seq, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.add,
    Work.configBase, Work.reference₀, Work.addCounter]

theorem prepareStateReference_effect_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).effect values =
      Function.update values Work.reference₀
        (transitionStateRef (values Work.configBase) stateIndex) := by
  simp [prepareStateReference, BinaryRoutine.seq, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.add,
    transitionStateRef, Work.configBase, Work.reference₀, Work.addCounter,
    Nat.add_comm]

theorem prepareStateReference_emitted_internal (stateIndex : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareStateReference stateIndex).emitted values = [] := by
  simp [prepareStateReference, BinaryRoutine.seq, BinaryRoutine.set,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.add]

theorem prepareStateReference_spaceBoundByWidth_internal
    (stateIndex : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionStateRef (values inputLength Work.configBase) stateIndex ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (prepareStateReference stateIndex)
      initialSpace values width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · intro inputLength
      have := hcap inputLength
      simp only [transitionStateRef] at this
      omega
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          hvalues inputLength Work.configBase
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase,
        transitionStateRef, Nat.add_comm] using hcap inputLength

theorem prepareHeadReference_sound_internal (stateCount : ℕ) :
    (prepareHeadReference stateCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.reference₀ stateCount
  · subst routine
    exact BinaryRoutine.add_sound Work.configBase Work.reference₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₀ 1
  · subst routine
    exact BinaryRoutine.add_sound Work.horizon Work.temporary₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.tapeIndex Work.temporary₀
      Work.reference₀ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.add_sound Work.position Work.reference₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₀

theorem prepareHeadReference_requires_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareHeadReference stateCount).requires values := by
  simp [prepareHeadReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd,
    Work.horizon, Work.configBase, Work.reference₀, Work.multiplyCounter,
    Work.addCounter, Work.temporary₀, Work.tapeIndex, Work.position]
  refine ⟨hadd, ⟨?_, hmultiply, hadd⟩, hadd, ?_⟩
  · exact
      { left_ne_right := by decide
        left_ne_acc := by decide
        left_ne_mulCounter := by decide
        left_ne_addCounter := by decide
        right_ne_acc := by decide
        right_ne_mulCounter := by decide
        right_ne_addCounter := by decide
        acc_ne_mulCounter := by decide
        acc_ne_addCounter := by decide
        mulCounter_ne_addCounter := by decide }
  · trivial

theorem prepareHeadReference_effect_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareHeadReference stateCount).effect values =
      Function.update
        (Function.update values Work.reference₀
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position))) Work.temporary₀ 0 := by
  simp [prepareHeadReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, transitionHeadRef, Work.horizon, Work.configBase,
    Work.reference₀, Work.multiplyCounter, Work.addCounter, Work.temporary₀,
    Work.tapeIndex, Work.position]
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals ring

theorem prepareHeadReference_emitted_internal (stateCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareHeadReference stateCount).emitted values = [] := by
  simp [prepareHeadReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

theorem prepareHeadReference_spaceBoundByWidth_internal
    (stateCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt (prepareHeadReference stateCount)
      initialSpace values width := by
  have hbounds (inputLength : ℕ) := HeadReferenceWidthBounds.of_cap
    stateCount (values inputLength Work.configBase)
    (values inputLength Work.horizon) (values inputLength Work.tapeIndex)
    (values inputLength Work.position) (width inputLength)
    (by simpa [transitionHeadRef, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcap inputLength)
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · exact fun inputLength => (hbounds inputLength).stateCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          hvalues inputLength Work.configBase
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          (hbounds inputLength).stateBase_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀] using
          hvalues inputLength Work.temporary₀
    · exact fun inputLength => (hbounds inputLength).one_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon] using
          hvalues inputLength Work.horizon
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon, Nat.add_comm] using
          (hbounds inputLength).horizonOne_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon,
        Work.tapeIndex] using hvalues inputLength Work.tapeIndex
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon,
        Work.tapeIndex, Nat.add_comm] using
          (hbounds inputLength).horizonOne_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon,
        Work.tapeIndex, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (hbounds inputLength).multiplyIntermediate_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.reference₀, Work.configBase, Work.temporary₀, Work.horizon,
        Work.tapeIndex, Work.position] using
          hvalues inputLength Work.position
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
        Work.reference₀, Work.configBase, Work.temporary₀, Work.horizon,
        Work.tapeIndex, Work.position, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using (hbounds inputLength).finalReference_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
      BinaryRoutine.addConst, BinaryRoutine.add, BinaryRoutine.mulAdd,
      Work.reference₀, Work.configBase, Work.temporary₀, Work.horizon,
      Work.tapeIndex, Work.position, Nat.add_comm] using
        (hbounds inputLength).horizonOne_le
  · trivial

private theorem prepareCellReferenceBase_sound (stateCount tapeCount : ℕ) :
    (prepareCellReferenceBase stateCount tapeCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.reference₀ stateCount
  · subst routine
    exact BinaryRoutine.add_sound Work.configBase Work.reference₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₀ 1
  · subst routine
    exact BinaryRoutine.add_sound Work.horizon Work.temporary₀ Work.addCounter
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₁ tapeCount
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₀ Work.temporary₁
      Work.reference₀ Work.multiplyCounter Work.addCounter

private theorem prepareCellPositionOffset_sound :
    prepareCellPositionOffset.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h
  · subst routine
    exact BinaryRoutine.addConst_sound Work.temporary₀ 1
  · subst routine
    exact BinaryRoutine.binaryCopy_sound Work.tapeIndex Work.temporary₁
      Work.copyCounter
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₂
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₁ Work.temporary₀
      Work.temporary₂ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.add_sound Work.position Work.temporary₂ Work.addCounter

private theorem finishCellReference_sound : finishCellReference.Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h | h | h | h
  · subst routine
    exact BinaryRoutine.set_sound Work.temporary₁ 4
  · subst routine
    exact BinaryRoutine.mulAdd_sound Work.temporary₂ Work.temporary₁
      Work.reference₀ Work.multiplyCounter Work.addCounter
  · subst routine
    exact BinaryRoutine.add_sound Work.symbolIndex Work.reference₀ Work.addCounter
  all_goals
    subst routine
    exact BinaryRoutine.clear_sound _

theorem prepareCellReference_sound_internal (stateCount tapeCount : ℕ) :
    (prepareCellReference stateCount tapeCount).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact prepareCellReferenceBase_sound stateCount tapeCount
  · subst routine
    exact prepareCellPositionOffset_sound
  · subst routine
    exact finishCellReference_sound

private theorem prepareCellReferenceBase_effect (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareCellReferenceBase stateCount tapeCount).effect values =
      Function.update
        (Function.update
          (Function.update values Work.reference₀
            (values Work.configBase + stateCount +
              tapeCount * (values Work.horizon + 1)))
          Work.temporary₀ (values Work.horizon + 1))
        Work.temporary₁ tapeCount := by
  simp [prepareCellReferenceBase, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.horizon, Work.configBase, Work.reference₀,
    Work.multiplyCounter, Work.addCounter, Work.temporary₀, Work.temporary₁]
  funext i
  simp only [Function.update_apply]
  split_ifs
  all_goals simp_all
  all_goals ring

private theorem prepareCellReferenceBase_requires
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareCellReferenceBase stateCount tapeCount).requires values := by
  have hdistinct : TM.BinaryMulAddDistinct Work.temporary₀ Work.temporary₁
      Work.reference₀ Work.multiplyCounter Work.addCounter :=
    { left_ne_right := by decide
      left_ne_acc := by decide
      left_ne_mulCounter := by decide
      left_ne_addCounter := by decide
      right_ne_acc := by decide
      right_ne_mulCounter := by decide
      right_ne_addCounter := by decide
      acc_ne_mulCounter := by decide
      acc_ne_addCounter := by decide
      mulCounter_ne_addCounter := by decide }
  simp [prepareCellReferenceBase, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.horizon, Work.configBase, Work.reference₀,
    Work.multiplyCounter, Work.addCounter, Work.temporary₀, Work.temporary₁]
  aesop

private theorem prepareCellPositionOffset_effect
    (values : BinaryValues WorkCount) :
    prepareCellPositionOffset.effect values =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀
            (values Work.temporary₀ + 1)) Work.temporary₁
            (values Work.tapeIndex)) Work.temporary₂
          (values Work.tapeIndex * (values Work.temporary₀ + 1) +
            values Work.position) := by
  simp [prepareCellPositionOffset, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.binaryCopy,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.copyCounter, Work.multiplyCounter,
    Work.addCounter, Work.temporary₀, Work.temporary₁, Work.temporary₂,
    Work.tapeIndex, Work.position]

private theorem prepareCellPositionOffset_requires
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    prepareCellPositionOffset.requires values := by
  have hdistinct : TM.BinaryMulAddDistinct Work.temporary₁ Work.temporary₀
      Work.temporary₂ Work.multiplyCounter Work.addCounter :=
    { left_ne_right := by decide
      left_ne_acc := by decide
      left_ne_mulCounter := by decide
      left_ne_addCounter := by decide
      right_ne_acc := by decide
      right_ne_mulCounter := by decide
      right_ne_addCounter := by decide
      acc_ne_mulCounter := by decide
      acc_ne_addCounter := by decide
      mulCounter_ne_addCounter := by decide }
  simp [prepareCellPositionOffset, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.binaryCopy,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.copyCounter, Work.multiplyCounter,
    Work.addCounter, Work.temporary₀, Work.temporary₁, Work.temporary₂,
    Work.tapeIndex, Work.position]
  aesop

private theorem finishCellReference_effect (values : BinaryValues WorkCount) :
    finishCellReference.effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.reference₀
              (values Work.reference₀ + values Work.temporary₂ * 4 +
                values Work.symbolIndex)) Work.temporary₀ 0)
          Work.temporary₁ 0) Work.temporary₂ 0 := by
  simp [finishCellReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.reference₀, Work.multiplyCounter,
    Work.addCounter, Work.temporary₀, Work.temporary₁, Work.temporary₂,
    Work.symbolIndex]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all

private theorem finishCellReference_requires (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    finishCellReference.requires values := by
  have hdistinct : TM.BinaryMulAddDistinct Work.temporary₂ Work.temporary₁
      Work.reference₀ Work.multiplyCounter Work.addCounter :=
    { left_ne_right := by decide
      left_ne_acc := by decide
      left_ne_mulCounter := by decide
      left_ne_addCounter := by decide
      right_ne_acc := by decide
      right_ne_mulCounter := by decide
      right_ne_addCounter := by decide
      acc_ne_mulCounter := by decide
      acc_ne_addCounter := by decide
      mulCounter_ne_addCounter := by decide }
  simp [finishCellReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits, Work.reference₀, Work.multiplyCounter,
    Work.addCounter, Work.temporary₀, Work.temporary₁, Work.temporary₂,
    Work.symbolIndex]
  aesop

private theorem prepareCellReferenceBase_emitted
    (stateCount tapeCount : ℕ) (values : BinaryValues WorkCount) :
    (prepareCellReferenceBase stateCount tapeCount).emitted values = [] := by
  simp [prepareCellReferenceBase, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem prepareCellPositionOffset_emitted
    (values : BinaryValues WorkCount) :
    prepareCellPositionOffset.emitted values = [] := by
  simp [prepareCellPositionOffset, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.addConst, BinaryRoutine.binaryCopy,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem finishCellReference_emitted (values : BinaryValues WorkCount) :
    finishCellReference.emitted values = [] := by
  simp [finishCellReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.set, BinaryRoutine.clear, BinaryRoutine.addConst,
    BinaryRoutine.add, BinaryRoutine.mulAdd, BinaryRoutine.identity,
    BinaryRoutine.emitBits]

private theorem prepareCellReferenceBase_spaceBoundByWidth
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hbounds : ∀ inputLength,
      CellReferenceWidthBounds stateCount tapeCount
        (values inputLength Work.configBase)
        (values inputLength Work.horizon)
        (values inputLength Work.tapeIndex)
        (values inputLength Work.position)
        (values inputLength Work.symbolIndex) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt
      (prepareCellReferenceBase stateCount tapeCount) initialSpace values
      width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · exact fun inputLength => hvalues inputLength Work.reference₀
    · exact fun inputLength => (hbounds inputLength).stateCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          hvalues inputLength Work.configBase
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, Work.reference₀, Work.configBase] using
          (hbounds inputLength).stateBase_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀] using
          hvalues inputLength Work.temporary₀
    · exact fun inputLength => (hbounds inputLength).one_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon] using
          hvalues inputLength Work.horizon
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.horizon, Nat.add_comm] using
          (hbounds inputLength).horizonOne_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using hvalues inputLength Work.temporary₁
    · exact fun inputLength => (hbounds inputLength).tapeCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon, Nat.add_comm] using
          (hbounds inputLength).horizonOne_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon] using (hbounds inputLength).tapeCount_le
    · intro inputLength
      simpa [BinaryRoutine.set, BinaryRoutine.seq, BinaryRoutine.clear,
        BinaryRoutine.addConst, BinaryRoutine.add, Work.reference₀,
        Work.configBase, Work.temporary₀, Work.temporary₁,
        Work.horizon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        Nat.mul_comm] using
          (hbounds inputLength).baseMultiplyIntermediate_le
  · trivial

private theorem prepareCellPositionOffset_spaceBoundByWidth
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hbounds : ∀ inputLength,
      CellReferenceWidthBounds stateCount tapeCount
        (values inputLength Work.configBase)
        (values inputLength Work.horizon)
        (values inputLength Work.tapeIndex)
        (values inputLength Work.position)
        (values inputLength Work.symbolIndex) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt prepareCellPositionOffset initialSpace
      (fun inputLength =>
        (prepareCellReferenceBase stateCount tapeCount).effect
          (values inputLength)) width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simpa [prepareCellReferenceBase_effect, Work.temporary₀,
      Work.temporary₁, Nat.add_assoc] using
        (hbounds inputLength).horizonTwo_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        Work.reference₀, Work.temporary₀, Work.temporary₁,
        Work.tapeIndex] using hvalues inputLength Work.tapeIndex
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        Work.reference₀, Work.temporary₀, Work.temporary₁,
        Work.tapeIndex] using (hbounds inputLength).tapeCount_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
      BinaryRoutine.binaryCopy, Work.reference₀, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Work.tapeIndex] using
        hvalues inputLength Work.temporary₂
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        BinaryRoutine.binaryCopy, BinaryRoutine.clear, Work.reference₀,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.tapeIndex] using hvalues inputLength Work.tapeIndex
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        BinaryRoutine.binaryCopy, BinaryRoutine.clear, Work.reference₀,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.tapeIndex, Nat.add_assoc] using
          (hbounds inputLength).horizonTwo_le
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        BinaryRoutine.binaryCopy, BinaryRoutine.clear, Work.reference₀,
        Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.tapeIndex, Nat.add_assoc] using
          (hbounds inputLength).offsetMultiplyIntermediate_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        BinaryRoutine.binaryCopy, BinaryRoutine.clear, BinaryRoutine.mulAdd,
        Work.reference₀, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.tapeIndex, Work.position] using
          hvalues inputLength Work.position
    · intro inputLength
      simpa [prepareCellReferenceBase_effect, BinaryRoutine.addConst,
        BinaryRoutine.binaryCopy, BinaryRoutine.clear, BinaryRoutine.mulAdd,
        Work.reference₀, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.tapeIndex, Work.position, Nat.add_assoc] using
          (hbounds inputLength).offset_le
  · trivial

private theorem finishCellReference_spaceBoundByWidth
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hbounds : ∀ inputLength,
      CellReferenceWidthBounds stateCount tapeCount
        (values inputLength Work.configBase)
        (values inputLength Work.horizon)
        (values inputLength Work.tapeIndex)
        (values inputLength Work.position)
        (values inputLength Work.symbolIndex) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt finishCellReference initialSpace
      (fun inputLength => prepareCellPositionOffset.effect
        ((prepareCellReferenceBase stateCount tapeCount).effect
          (values inputLength))) width := by
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.set
    · intro inputLength
      simpa [prepareCellPositionOffset_effect,
        prepareCellReferenceBase_effect, Work.reference₀, Work.temporary₀,
        Work.temporary₁, Work.temporary₂, Work.tapeIndex] using
          hvalues inputLength Work.tapeIndex
    · exact fun inputLength => (hbounds inputLength).four_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.mulAdd
    · intro inputLength
      simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
        Work.reference₀, Work.temporary₀, Work.temporary₁, Work.temporary₂, Work.tapeIndex,
        Work.position]
      exact (hbounds inputLength).offset_le
    · intro inputLength
      simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
        Work.reference₀, Work.temporary₀, Work.temporary₁, Work.temporary₂, Work.tapeIndex,
        Work.position]
      exact (hbounds inputLength).four_le
    · intro inputLength
      simpa [prepareCellPositionOffset_effect,
        prepareCellReferenceBase_effect, BinaryRoutine.set,
        BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.addConst,
        Work.reference₀, Work.temporary₀, Work.temporary₁,
        Work.temporary₂, Work.tapeIndex, Work.position, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
          (hbounds inputLength).finalMultiplyIntermediate_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
        BinaryRoutine.mulAdd, Work.reference₀, Work.temporary₀, Work.temporary₁, Work.temporary₂,
        Work.tapeIndex, Work.position, Work.symbolIndex]
      exact hvalues inputLength Work.symbolIndex
    · intro inputLength
      simpa [prepareCellPositionOffset_effect,
        prepareCellReferenceBase_effect, BinaryRoutine.set,
        BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.addConst,
        BinaryRoutine.mulAdd, Work.reference₀, Work.temporary₀,
        Work.temporary₁, Work.temporary₂, Work.tapeIndex,
        Work.position, Work.symbolIndex, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, Nat.mul_comm] using
          (hbounds inputLength).finalReference_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
      BinaryRoutine.mulAdd, BinaryRoutine.add, Work.reference₀, Work.temporary₀, Work.temporary₁,
      Work.temporary₂, Work.tapeIndex, Work.position, Work.symbolIndex, Nat.add_assoc]
    exact (hbounds inputLength).horizonTwo_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
      BinaryRoutine.mulAdd, BinaryRoutine.add, BinaryRoutine.clear, Work.reference₀,
      Work.temporary₀, Work.temporary₁, Work.temporary₂, Work.tapeIndex, Work.position,
      Work.symbolIndex]
    exact (hbounds inputLength).four_le
  constructor
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simp [prepareCellPositionOffset_effect, prepareCellReferenceBase_effect, BinaryRoutine.set,
      BinaryRoutine.mulAdd, BinaryRoutine.add, BinaryRoutine.clear, Work.reference₀,
      Work.temporary₀, Work.temporary₁, Work.temporary₂, Work.tapeIndex, Work.position,
      Work.symbolIndex]
    exact (hbounds inputLength).offset_le
  · trivial

theorem prepareCellReference_requires_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0) :
    (prepareCellReference stateCount tapeCount).requires values := by
  simp only [prepareCellReference, BinaryRoutine.seqList, BinaryRoutine.seq]
  refine ⟨prepareCellReferenceBase_requires stateCount tapeCount values hadd
    hmultiply, ?_, ?_, trivial⟩
  · apply prepareCellPositionOffset_requires
    all_goals rw [prepareCellReferenceBase_effect]
    · simpa [Work.copyCounter, Work.reference₀, Work.temporary₀,
        Work.temporary₁] using hcopy
    · simpa [Work.addCounter, Work.reference₀, Work.temporary₀,
        Work.temporary₁] using hadd
    · simpa [Work.multiplyCounter, Work.reference₀, Work.temporary₀,
        Work.temporary₁] using hmultiply
  · apply finishCellReference_requires
    all_goals rw [prepareCellPositionOffset_effect,
      prepareCellReferenceBase_effect]
    · simpa [Work.addCounter, Work.reference₀, Work.temporary₀,
        Work.temporary₁, Work.temporary₂] using hadd
    · simpa [Work.multiplyCounter, Work.reference₀, Work.temporary₀,
        Work.temporary₁, Work.temporary₂] using hmultiply

theorem prepareCellReference_effect_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareCellReference stateCount tapeCount).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.reference₀
              (transitionCellRef stateCount tapeCount (values Work.horizon)
                (values Work.configBase) (values Work.tapeIndex)
                (values Work.position) (values Work.symbolIndex)))
            Work.temporary₀ 0) Work.temporary₁ 0) Work.temporary₂ 0 := by
  simp [prepareCellReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareCellReferenceBase_effect, prepareCellPositionOffset_effect,
    finishCellReference_effect, BinaryRoutine.identity, BinaryRoutine.emitBits,
    transitionCellRef, Work.horizon, Work.configBase, Work.reference₀,
    Work.temporary₀, Work.temporary₁, Work.temporary₂, Work.tapeIndex,
    Work.position, Work.symbolIndex]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all
  ring

theorem prepareCellReference_emitted_internal (stateCount tapeCount : ℕ)
    (values : BinaryValues WorkCount) :
    (prepareCellReference stateCount tapeCount).emitted values = [] := by
  simp [prepareCellReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    prepareCellReferenceBase_emitted, prepareCellPositionOffset_emitted,
    finishCellReference_emitted,
    BinaryRoutine.identity, BinaryRoutine.emitBits]

theorem prepareCellReference_spaceBoundByWidth_internal
    (stateCount tapeCount : ℕ) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
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
      (prepareCellReference stateCount tapeCount) initialSpace values width := by
  have hbounds (inputLength : ℕ) := CellReferenceWidthBounds.of_cap
    stateCount tapeCount (values inputLength Work.configBase)
    (values inputLength Work.horizon) (values inputLength Work.tapeIndex)
    (values inputLength Work.position) (values inputLength Work.symbolIndex)
    (width inputLength) (by
      simpa [transitionCellRef, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hcap inputLength)
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  exact ⟨prepareCellReferenceBase_spaceBoundByWidth stateCount tapeCount
      hvalues hbounds,
    prepareCellPositionOffset_spaceBoundByWidth stateCount tapeCount hvalues
      hbounds,
    finishCellReference_spaceBoundByWidth stateCount tapeCount hvalues hbounds,
    trivial⟩

theorem emitPreparedReference_sound_internal
    {prepare : BinaryRoutine WorkCount} (hprepare : prepare.Sound)
    (negated : Bool) :
    (emitPreparedReference prepare negated).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with h | h | h
  · subst routine
    exact hprepare
  · subst routine
    exact BinaryRoutine.emitRawGateStep_sound .and negated negated
      Work.emitCounter Work.available Work.reference₀ Work.reference₀
  · subst routine
    exact BinaryRoutine.clear_sound Work.reference₀

private theorem emitPreparedReference_requires
    (prepare : BinaryRoutine WorkCount) (negated : Bool)
    (values : BinaryValues WorkCount)
    (hprepare : prepare.requires values)
    (hemit : prepare.effect values Work.emitCounter = 0) :
    (emitPreparedReference prepare negated).requires values := by
  have hdistinct : CircuitCode.Machine.RawGateStepDistinct Work.emitCounter
      Work.available Work.reference₀ Work.reference₀ :=
    { emitCounter_ne_available := by decide
      emitCounter_ne_input₀ := by decide
      emitCounter_ne_input₁ := by decide
      available_ne_input₀ := by decide
      available_ne_input₁ := by decide }
  simp only [emitPreparedReference, BinaryRoutine.seqList, BinaryRoutine.seq]
  exact ⟨hprepare, ⟨hdistinct, hemit⟩, trivial, trivial⟩

private theorem emitPreparedReference_effect
    (prepare : BinaryRoutine WorkCount) (negated : Bool)
    (values : BinaryValues WorkCount) :
    (emitPreparedReference prepare negated).effect values =
      Function.update
        (Function.update (prepare.effect values) Work.available
          (prepare.effect values Work.available + 1)) Work.reference₀ 0 := by
  simp [emitPreparedReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits]

private theorem emitPreparedReference_emitted
    (prepare : BinaryRoutine WorkCount) (negated : Bool)
    (values : BinaryValues WorkCount) :
    (emitPreparedReference prepare negated).emitted values =
      prepare.emitted values ++
        CircuitCode.RawGate.encode
          (CircuitCode.RawGate.copy
            (prepare.effect values Work.reference₀) negated) := by
  simp [emitPreparedReference, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, CircuitCode.RawGate.copy]

private theorem emitPreparedReference_spaceBoundByWidth
    (prepare : BinaryRoutine WorkCount) (negated : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace values
      width)
    (havailable : ∀ inputLength,
      prepare.effect (values inputLength) Work.available ≤
        width inputLength)
    (hreference : ∀ inputLength,
      prepare.effect (values inputLength) Work.reference₀ ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPreparedReference prepare negated) initialSpace values width := by
  rw [emitPreparedReference]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
  refine ⟨hprepare, ?_, ?_, trivial⟩
  · exact BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep .and negated
      negated Work.emitCounter Work.available Work.reference₀ Work.reference₀
      havailable hreference hreference
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    simpa [BinaryRoutine.emitRawGateStep, Work.available, Work.reference₀]
      using hreference inputLength

theorem emitStateReference_sound_internal (stateIndex : ℕ)
    (negated : Bool) :
    (emitStateReference stateIndex negated).Sound :=
  emitPreparedReference_sound_internal
    (prepareStateReference_sound_internal stateIndex) negated

theorem emitHeadReference_sound_internal (stateCount : ℕ)
    (negated : Bool) :
    (emitHeadReference stateCount negated).Sound :=
  emitPreparedReference_sound_internal
    (prepareHeadReference_sound_internal stateCount) negated

theorem emitCellReference_sound_internal (stateCount tapeCount : ℕ)
    (negated : Bool) :
    (emitCellReference stateCount tapeCount negated).Sound :=
  emitPreparedReference_sound_internal
    (prepareCellReference_sound_internal stateCount tapeCount) negated

theorem emitStateReference_spaceBoundByWidth_internal
    (stateIndex : ℕ) (negated : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionStateRef (values inputLength Work.configBase) stateIndex ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitStateReference stateIndex negated) initialSpace values width := by
  rw [emitStateReference]
  apply emitPreparedReference_spaceBoundByWidth
  · exact prepareStateReference_spaceBoundByWidth_internal stateIndex
      hvalues hcap
  · intro inputLength
    rw [prepareStateReference_effect_internal]
    simpa [Work.available, Work.reference₀] using
      hvalues inputLength Work.available
  · intro inputLength
    rw [prepareStateReference_effect_internal]
    simpa using hcap inputLength

theorem emitHeadReference_spaceBoundByWidth_internal
    (stateCount : ℕ) (negated : Bool) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
      transitionHeadRef stateCount (values inputLength Work.horizon)
          (values inputLength Work.configBase)
          (values inputLength Work.tapeIndex)
          (values inputLength Work.position) +
          values inputLength Work.tapeIndex +
          values inputLength Work.horizon + 1 ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitHeadReference stateCount negated) initialSpace values width := by
  have hbounds (inputLength : ℕ) := HeadReferenceWidthBounds.of_cap
    stateCount (values inputLength Work.configBase)
    (values inputLength Work.horizon) (values inputLength Work.tapeIndex)
    (values inputLength Work.position) (width inputLength)
    (by simpa [transitionHeadRef, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcap inputLength)
  rw [emitHeadReference]
  apply emitPreparedReference_spaceBoundByWidth
  · exact prepareHeadReference_spaceBoundByWidth_internal stateCount
      hvalues hcap
  · intro inputLength
    rw [prepareHeadReference_effect_internal]
    simpa [Work.available, Work.reference₀, Work.temporary₀] using
      hvalues inputLength Work.available
  · intro inputLength
    rw [prepareHeadReference_effect_internal]
    simpa [transitionHeadRef, Work.reference₀, Work.temporary₀,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (hbounds inputLength).finalReference_le

theorem emitCellReference_spaceBoundByWidth_internal
    (stateCount tapeCount : ℕ) (negated : Bool)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (hcap : ∀ inputLength,
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
      (emitCellReference stateCount tapeCount negated) initialSpace values
      width := by
  have hbounds (inputLength : ℕ) := CellReferenceWidthBounds.of_cap
    stateCount tapeCount (values inputLength Work.configBase)
    (values inputLength Work.horizon) (values inputLength Work.tapeIndex)
    (values inputLength Work.position) (values inputLength Work.symbolIndex)
    (width inputLength) (by
      simpa [transitionCellRef, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hcap inputLength)
  rw [emitCellReference]
  apply emitPreparedReference_spaceBoundByWidth
  · exact prepareCellReference_spaceBoundByWidth_internal stateCount
      tapeCount hvalues hcap
  · intro inputLength
    rw [prepareCellReference_effect_internal]
    simpa [Work.available, Work.reference₀, Work.temporary₀,
      Work.temporary₁, Work.temporary₂] using
        hvalues inputLength Work.available
  · intro inputLength
    rw [prepareCellReference_effect_internal]
    simpa [transitionCellRef, Work.reference₀, Work.temporary₀,
      Work.temporary₁, Work.temporary₂, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using
        (hbounds inputLength).finalReference_le

theorem emitStateReference_requires_internal (stateIndex : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitStateReference stateIndex negated).requires values := by
  rw [emitStateReference]
  apply emitPreparedReference_requires
  · exact (prepareStateReference_requires_internal stateIndex values).2 hadd
  · rw [prepareStateReference_effect_internal]
    simpa [Work.emitCounter, Work.reference₀] using hemit

theorem emitHeadReference_requires_internal (stateCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitHeadReference stateCount negated).requires values := by
  rw [emitHeadReference]
  apply emitPreparedReference_requires
  · exact prepareHeadReference_requires_internal stateCount values hadd hmultiply
  · rw [prepareHeadReference_effect_internal]
    simpa [Work.emitCounter, Work.reference₀, Work.temporary₀] using hemit

theorem emitCellReference_requires_internal (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0)
    (hadd : values Work.addCounter = 0)
    (hmultiply : values Work.multiplyCounter = 0)
    (hemit : values Work.emitCounter = 0) :
    (emitCellReference stateCount tapeCount negated).requires values := by
  rw [emitCellReference]
  apply emitPreparedReference_requires
  · exact prepareCellReference_requires_internal stateCount tapeCount values
      hcopy hadd hmultiply
  · rw [prepareCellReference_effect_internal]
    simpa [Work.emitCounter, Work.reference₀, Work.temporary₀,
      Work.temporary₁, Work.temporary₂] using hemit

theorem emitStateReference_effect_internal (stateIndex : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitStateReference stateIndex negated).effect values =
      Function.update
        (Function.update values Work.available (values Work.available + 1))
        Work.reference₀ 0 := by
  rw [emitStateReference, emitPreparedReference_effect,
    prepareStateReference_effect_internal]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.available, Work.reference₀]

theorem emitHeadReference_effect_internal (stateCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitHeadReference stateCount negated).effect values =
      Function.update
        (Function.update
          (Function.update values Work.temporary₀ 0) Work.available
            (values Work.available + 1)) Work.reference₀ 0 := by
  rw [emitHeadReference, emitPreparedReference_effect,
    prepareHeadReference_effect_internal]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.available, Work.reference₀, Work.temporary₀]

theorem emitCellReference_effect_internal (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCellReference stateCount tapeCount negated).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.temporary₀ 0) Work.temporary₁ 0)
            Work.temporary₂ 0) Work.available (values Work.available + 1))
        Work.reference₀ 0 := by
  rw [emitCellReference, emitPreparedReference_effect,
    prepareCellReference_effect_internal]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.available, Work.reference₀, Work.temporary₀,
    Work.temporary₁, Work.temporary₂]

theorem emitStateReference_emitted_internal (stateIndex : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitStateReference stateIndex negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionStateRef (values Work.configBase) stateIndex) negated) := by
  rw [emitStateReference, emitPreparedReference_emitted,
    prepareStateReference_emitted_internal,
    prepareStateReference_effect_internal]
  simp

theorem emitHeadReference_emitted_internal (stateCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitHeadReference stateCount negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionHeadRef stateCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position)) negated) := by
  rw [emitHeadReference, emitPreparedReference_emitted,
    prepareHeadReference_emitted_internal,
    prepareHeadReference_effect_internal]
  simp [Work.reference₀, Work.temporary₀]

theorem emitCellReference_emitted_internal (stateCount tapeCount : ℕ)
    (negated : Bool) (values : BinaryValues WorkCount) :
    (emitCellReference stateCount tapeCount negated).emitted values =
      CircuitCode.RawGate.encode
        (CircuitCode.RawGate.copy
          (transitionCellRef stateCount tapeCount (values Work.horizon)
            (values Work.configBase) (values Work.tapeIndex)
            (values Work.position) (values Work.symbolIndex)) negated) := by
  rw [emitCellReference, emitPreparedReference_emitted,
    prepareCellReference_emitted_internal,
    prepareCellReference_effect_internal]
  simp [Work.reference₀, Work.temporary₀, Work.temporary₁,
    Work.temporary₂]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
