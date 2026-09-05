/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Offset
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset.Defs

/-!
# Polynomial recent-wire offsets -- proof internals
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem polynomialOffsetDistinct :
    DynamicRecentGateDistinct Work.temporary₃ Work.loop₃ := by
  apply DynamicRecentGateDistinct.mk
  · apply DynamicRecentDistinct.mk
    · exact ⟨by decide, by decide, by decide⟩
    all_goals decide
  all_goals decide

private theorem polynomialEvaluationDistinct :
    TM.BinaryPolynomialDistinct Work.horizon Work.temporary₃
      Work.polynomialScratch Work.multiplyCounter Work.addCounter := by
  constructor <;> decide

theorem preparePolynomialOffset_sound_internal (polynomial : Polynomial ℕ)
    (extra : ℕ) :
    (preparePolynomialOffset polynomial extra).Sound :=
  (BinaryRoutine.evalPolynomial_sound Work.horizon Work.temporary₃
    Work.polynomialScratch Work.multiplyCounter Work.addCounter
    polynomial).seq (BinaryRoutine.addConst_sound Work.temporary₃ extra)

theorem preparePolynomialOffset_requires_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 := by
  simp only [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]
  simp only [polynomialEvaluationDistinct, true_and, and_true]

theorem preparePolynomialOffset_effect_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).effect values =
      Function.update values Work.temporary₃
        (polynomial.eval (values Work.horizon) + extra) := by
  simp [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]

theorem preparePolynomialOffset_emitted_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (preparePolynomialOffset polynomial extra).emitted values = [] := by
  simp [preparePolynomialOffset, BinaryRoutine.seq,
    BinaryRoutine.evalPolynomial, BinaryRoutine.addConst]

theorem preparePolynomialOffset_spaceBoundByWidth_internal
    (polynomial : Polynomial ℕ) (extra : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap polynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (hoffset : ∀ inputLength,
      polynomial.eval (values inputLength Work.horizon) + extra ≤
        width inputLength) :
    BinaryRoutine.SpaceBoundByWidthAt
      (preparePolynomialOffset polynomial extra) initialSpace values width := by
  let evaluate := BinaryRoutine.evalPolynomial Work.horizon Work.temporary₃
    Work.polynomialScratch Work.multiplyCounter Work.addCounter polynomial
  have hevaluate : BinaryRoutine.SpaceBoundByWidthAt evaluate initialSpace
      values width :=
    BinaryRoutine.SpaceBoundByWidthAt.evalPolynomial Work.horizon
      Work.temporary₃ Work.polynomialScratch Work.multiplyCounter
      Work.addCounter polynomial hpolynomialCap
  have hadd : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.addConst Work.temporary₃ extra) initialSpace
      (fun inputLength => evaluate.effect (values inputLength)) width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.addConst
    intro inputLength
    simpa [evaluate, BinaryRoutine.evalPolynomial] using hoffset inputLength
  simpa [preparePolynomialOffset, evaluate] using
    BinaryRoutine.SpaceBoundByWidthAt.seq hevaluate hadd

theorem emitPolynomialRecentGate_spaceBoundByWidth_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap polynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hreference₁ : ∀ inputLength,
      values inputLength Work.reference₁ ≤ width inputLength)
    (hloop : ∀ inputLength, values inputLength Work.loop₃ = 0)
    (hoffsetAvailable : ∀ inputLength,
      polynomial.eval (values inputLength Work.horizon) + extra ≤
        values inputLength Work.available)
    (hfixedOffset₁ : ∀ inputLength,
      fixedOffset₁ ≤ values inputLength Work.available) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁) initialSpace values width := by
  have hoffsetWidth : ∀ inputLength,
      polynomial.eval (values inputLength Work.horizon) + extra ≤
        width inputLength := fun inputLength =>
    (hoffsetAvailable inputLength).trans (havailable inputLength)
  let prepare := preparePolynomialOffset polynomial extra
  let emit := emitDynamicRecentGate op negated₀ negated₁ Work.temporary₃
    Work.loop₃ fixedOffset₁
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (values₁ inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width :=
    preparePolynomialOffset_spaceBoundByWidth_internal polynomial extra
      hpolynomialCap hoffsetWidth
  have hvalues₁Available : ∀ inputLength,
      values₁ inputLength Work.available ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.available] using havailable inputLength
  have hvalues₁Reference₀ : ∀ inputLength,
      values₁ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.reference₀] using hreference₀ inputLength
  have hvalues₁Reference₁ : ∀ inputLength,
      values₁ inputLength Work.reference₁ ≤ width inputLength := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.reference₁] using hreference₁ inputLength
  have hvalues₁Loop : ∀ inputLength,
      values₁ inputLength Work.loop₃ = 0 := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.loop₃] using hloop inputLength
  have hvalues₁Offset : ∀ inputLength,
      values₁ inputLength Work.temporary₃ ≤
        values₁ inputLength Work.available := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.available] using hoffsetAvailable inputLength
  have hvalues₁FixedOffset : ∀ inputLength,
      fixedOffset₁ ≤ values₁ inputLength Work.available := by
    intro inputLength
    simpa [values₁, prepare, preparePolynomialOffset_effect_internal,
      Work.temporary₃, Work.available] using hfixedOffset₁ inputLength
  have hemit : BinaryRoutine.SpaceBoundByWidthAt emit initialSpace values₁
      width :=
    emitDynamicRecentGate_spaceBoundByWidth op negated₀ negated₁
      Work.temporary₃ Work.loop₃ fixedOffset₁ polynomialOffsetDistinct
      hvalues₁Available hvalues₁Reference₀ hvalues₁Reference₁ hvalues₁Loop
      hvalues₁Offset hvalues₁FixedOffset
  have hvalues₂Offset : ∀ inputLength,
      values₂ inputLength Work.temporary₃ ≤ width inputLength := by
    intro inputLength
    rw [show values₂ inputLength = emit.effect (values₁ inputLength) by rfl]
    rw [emitDynamicRecentGate_effect op negated₀ negated₁ Work.temporary₃
      Work.loop₃ fixedOffset₁ (values₁ inputLength)
      polynomialOffsetDistinct (hvalues₁Loop inputLength)]
    simpa [Work.temporary₃, Work.loop₃, Work.available, Work.reference₀,
      Work.reference₁, values₁, prepare,
      preparePolynomialOffset_effect_internal] using hoffsetWidth inputLength
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace values₂ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃ hvalues₂Offset
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength =>
        (BinaryRoutine.clear Work.temporary₃).effect (values₂ inputLength))
      width := BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hprepare
    (BinaryRoutine.SpaceBoundByWidthAt.seq hemit
      (BinaryRoutine.SpaceBoundByWidthAt.seq hclear hid))
  simpa [emitPolynomialRecentGate, BinaryRoutine.seqList, prepare, emit,
    values₁, values₂] using hroutine

theorem emitPolynomialRecentGate_sound_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).Sound := by
  apply BinaryRoutine.seqList_sound
  intro routine hroutine
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hroutine
  rcases hroutine with hroutine | hroutine | hroutine
  · subst routine
    exact preparePolynomialOffset_sound_internal polynomial extra
  · subst routine
    exact emitDynamicRecentGate_sound op negated₀ negated₁ Work.temporary₃
      Work.loop₃ fixedOffset₁
  · subst routine
    exact BinaryRoutine.clear_sound Work.temporary₃

theorem emitPolynomialRecentGate_requires_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.loop₃ = 0 ∧
        polynomial.eval (values Work.horizon) + extra ≤
          values Work.available ∧
        fixedOffset₁ ≤ values Work.available ∧
        values Work.emitCounter = 0 := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, and_true]
  rw [preparePolynomialOffset_requires_internal,
    emitDynamicRecentGate_requires,
    preparePolynomialOffset_effect_internal]
  simp only [polynomialOffsetDistinct, true_and]
  simp [Work.temporary₃, Work.loop₃,
    Work.copyCounter, Work.available, Work.emitCounter]
  tauto

theorem emitPolynomialRecentGate_effect_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.loop₃ 0) Work.available
                (values Work.available + 1)) Work.reference₀ 0)
          Work.reference₁ 0) Work.temporary₃ 0 := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, id_eq]
  rw [preparePolynomialOffset_effect_internal]
  rw [emitDynamicRecentGate_effect op negated₀ negated₁ Work.temporary₃
    Work.loop₃ fixedOffset₁ _ polynomialOffsetDistinct]
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · exact hloop

theorem emitPolynomialRecentGate_emitted_internal
    (polynomial : Polynomial ℕ) (extra : ℕ) (op : AndOrOp)
    (negated₀ negated₁ : Bool) (fixedOffset₁ : ℕ)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₃ = 0) :
    (emitPolynomialRecentGate polynomial extra op negated₀ negated₁
        fixedOffset₁).emitted values =
      CircuitCode.RawGate.encode
        { op := op
          input₀ := values Work.available -
            (polynomial.eval (values Work.horizon) + extra)
          input₁ := values Work.available - fixedOffset₁
          negated₀ := negated₀
          negated₁ := negated₁ } := by
  simp only [emitPolynomialRecentGate, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.clear, BinaryRoutine.identity,
    BinaryRoutine.emitBits, List.append_nil]
  rw [preparePolynomialOffset_emitted_internal,
    preparePolynomialOffset_effect_internal]
  rw [emitDynamicRecentGate_emitted op negated₀ negated₁ Work.temporary₃
    Work.loop₃ fixedOffset₁ _ polynomialOffsetDistinct]
  · simp [Work.temporary₃, Work.available]
  · exact hloop

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
