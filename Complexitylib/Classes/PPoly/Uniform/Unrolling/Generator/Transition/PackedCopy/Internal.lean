/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.PolynomialOffset
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy.Defs

/-!
# Delayed packed-formula copies -- proof internals
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem sound_with_stronger_requires (routine : BinaryRoutine WorkCount)
    (requires : BinaryValues WorkCount → Prop) (hsound : routine.Sound)
    (hrequires : ∀ values, requires values → routine.requires values) :
    ({ routine with requires := requires } : BinaryRoutine WorkCount).Sound := by
  refine
    { isTransducer := hsound.isTransducer
      hoareTimeSpace := ?_ }
  intro values inp₀ ys inputLength initialSpace hdomain hparked hinitialSpace
    hinputHead
  exact hsound.hoareTimeSpace values inp₀ ys inputLength initialSpace
    (hrequires values hdomain) hparked hinitialSpace hinputHead

theorem emitPackedFormulaCopy_spaceBoundByWidth_internal
    (sizePolynomial : Polynomial ℕ)
    {initialSpace : ℕ → ℕ} {values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hpolynomialCap : ∀ inputLength,
      2 * TM.binaryPolynomialValueCap sizePolynomial
          (values inputLength Work.horizon) ≤ width inputLength)
    (hcursorResult : ∀ inputLength,
      values inputLength Work.gateCount +
          sizePolynomial.eval (values inputLength Work.horizon) ≤
        width inputLength)
    (havailable : ∀ inputLength,
      values inputLength Work.available ≤ width inputLength)
    (hreference₀ : ∀ inputLength,
      values inputLength Work.reference₀ ≤ width inputLength)
    (hpositive : ∀ inputLength,
      0 < sizePolynomial.eval (values inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt
      (emitPackedFormulaCopy sizePolynomial) initialSpace values width := by
  have hevaluated : ∀ inputLength,
      sizePolynomial.eval (values inputLength Work.horizon) ≤
        width inputLength := by
    intro inputLength
    have hresult := hcursorResult inputLength
    omega
  let prepare := preparePolynomialOffset sizePolynomial
  let advance := BinaryRoutine.add Work.temporary₃ Work.gateCount
    Work.addCounter
  let copy := BinaryRoutine.binaryCopy Work.gateCount Work.reference₀
    Work.copyCounter
  let predecessor := BinaryRoutine.binaryPred Work.reference₀
  let emit := BinaryRoutine.emitRawGateStep .and false false
    Work.emitCounter Work.available Work.reference₀ Work.reference₀
  let values₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    prepare.effect (values inputLength)
  let values₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    advance.effect (values₁ inputLength)
  let values₃ : ℕ → BinaryValues WorkCount := fun inputLength =>
    copy.effect (values₂ inputLength)
  let values₄ : ℕ → BinaryValues WorkCount := fun inputLength =>
    predecessor.effect (values₃ inputLength)
  let values₅ : ℕ → BinaryValues WorkCount := fun inputLength =>
    emit.effect (values₄ inputLength)
  let values₆ : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.clear Work.reference₀).effect (values₅ inputLength)
  have hprepare : BinaryRoutine.SpaceBoundByWidthAt prepare initialSpace
      values width := by
    apply preparePolynomialOffset_spaceBoundByWidth sizePolynomial 0
    · exact hpolynomialCap
    · intro inputLength
      simpa using hevaluated inputLength
  have hadvance : BinaryRoutine.SpaceBoundByWidthAt advance initialSpace
      values₁ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.add
    · intro inputLength
      simpa [values₁, prepare, preparePolynomialOffset_effect,
        Work.temporary₃] using hevaluated inputLength
    · intro inputLength
      simpa [values₁, prepare, preparePolynomialOffset_effect,
        Work.temporary₃, Work.gateCount] using hcursorResult inputLength
  have hcopy : BinaryRoutine.SpaceBoundByWidthAt copy initialSpace values₂
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryCopy
    · intro inputLength
      simpa [values₂, advance, values₁, prepare,
        preparePolynomialOffset_effect, BinaryRoutine.add,
        Work.temporary₃, Work.gateCount] using hcursorResult inputLength
    · intro inputLength
      simpa [values₂, advance, values₁, prepare,
        preparePolynomialOffset_effect, BinaryRoutine.add,
        Work.temporary₃, Work.gateCount, Work.reference₀] using
          hreference₀ inputLength
  have hpredecessor : BinaryRoutine.SpaceBoundByWidthAt predecessor
      initialSpace values₃ width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryPred
    intro inputLength
    have hvalues₃ : values₃ inputLength Work.reference₀ =
        values inputLength Work.gateCount +
          sizePolynomial.eval (values inputLength Work.horizon) := by
      simp [values₃, copy, values₂, advance, values₁, prepare,
        preparePolynomialOffset_effect, BinaryRoutine.add,
        BinaryRoutine.binaryCopy, Work.temporary₃, Work.gateCount,
        Work.reference₀]
    rw [hvalues₃]
    have hresult := hcursorResult inputLength
    have hpositive' := hpositive inputLength
    omega
  have hvalues₄Reference₀ : ∀ inputLength,
      values₄ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    have hvalues₄ : values₄ inputLength Work.reference₀ =
        values inputLength Work.gateCount +
          sizePolynomial.eval (values inputLength Work.horizon) - 1 := by
      simp [values₄, predecessor, values₃, copy, values₂, advance,
        values₁, prepare, preparePolynomialOffset_effect,
        BinaryRoutine.binaryPred, BinaryRoutine.binaryCopy,
        BinaryRoutine.add, Work.reference₀, Work.gateCount,
        Work.temporary₃]
    rw [hvalues₄]
    exact (Nat.sub_le _ _).trans (hcursorResult inputLength)
  have hemit : BinaryRoutine.SpaceBoundByWidthAt emit initialSpace values₄
      width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.emitRawGateStep
    · intro inputLength
      simpa [values₄, predecessor, values₃, copy, values₂, advance,
        values₁, prepare, preparePolynomialOffset_effect,
        BinaryRoutine.binaryPred, BinaryRoutine.binaryCopy,
        BinaryRoutine.add, Work.available, Work.reference₀,
        Work.gateCount, Work.temporary₃] using havailable inputLength
    · exact hvalues₄Reference₀
    · exact hvalues₄Reference₀
  have hvalues₅Reference₀ : ∀ inputLength,
      values₅ inputLength Work.reference₀ ≤ width inputLength := by
    intro inputLength
    simpa [values₅, emit, BinaryRoutine.emitRawGateStep,
      Work.available, Work.reference₀] using hvalues₄Reference₀ inputLength
  have hclearReference : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.reference₀) initialSpace values₅ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.reference₀
      hvalues₅Reference₀
  have hvalues₆Temporary : ∀ inputLength,
      values₆ inputLength Work.temporary₃ ≤ width inputLength := by
    intro inputLength
    simpa [values₆, BinaryRoutine.clear, values₅, emit,
      BinaryRoutine.emitRawGateStep, values₄, predecessor,
      BinaryRoutine.binaryPred, values₃, copy, BinaryRoutine.binaryCopy,
      values₂, advance, BinaryRoutine.add, values₁, prepare,
      preparePolynomialOffset_effect, Work.reference₀, Work.available,
      Work.gateCount, Work.temporary₃] using hevaluated inputLength
  have hclearTemporary : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.temporary₃) initialSpace values₆ width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.temporary₃
      hvalues₆Temporary
  have hid : BinaryRoutine.SpaceBoundByWidthAt BinaryRoutine.identity
      initialSpace
      (fun inputLength =>
        (BinaryRoutine.clear Work.temporary₃).effect (values₆ inputLength))
      width := BinaryRoutine.SpaceBoundByWidthAt.identity
  have hroutine := BinaryRoutine.SpaceBoundByWidthAt.seq hprepare
    (BinaryRoutine.SpaceBoundByWidthAt.seq hadvance
      (BinaryRoutine.SpaceBoundByWidthAt.seq hcopy
        (BinaryRoutine.SpaceBoundByWidthAt.seq hpredecessor
          (BinaryRoutine.SpaceBoundByWidthAt.seq hemit
            (BinaryRoutine.SpaceBoundByWidthAt.seq hclearReference
              (BinaryRoutine.SpaceBoundByWidthAt.seq hclearTemporary hid))))))
  have hrestricted := BinaryRoutine.SpaceBoundByWidthAt.restrict
    (requires := fun current =>
      current Work.temporary₃ = 0 ∧
        current Work.polynomialScratch = 0 ∧
        current Work.multiplyCounter = 0 ∧
        current Work.addCounter = 0 ∧
        current Work.copyCounter = 0 ∧
        current Work.emitCounter = 0 ∧
        0 < sizePolynomial.eval (current Work.horizon)) hroutine
  simpa [emitPackedFormulaCopy, BinaryRoutine.seqList, BinaryRoutine.restrict,
    prepare, advance, copy, predecessor, emit, values₁, values₂, values₃,
    values₄, values₅, values₆] using hrestricted

theorem emitPackedFormulaCopy_requires_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).requires values ↔
      values Work.temporary₃ = 0 ∧
        values Work.polynomialScratch = 0 ∧
        values Work.multiplyCounter = 0 ∧
        values Work.addCounter = 0 ∧
        values Work.copyCounter = 0 ∧
        values Work.emitCounter = 0 ∧
        0 < sizePolynomial.eval (values Work.horizon) := by
  rfl

theorem emitPackedFormulaCopy_effect_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                sizePolynomial.eval (values Work.horizon)))
            Work.available (values Work.available + 1)) Work.reference₀ 0)
        Work.temporary₃ 0 := by
  simp only [emitPackedFormulaCopy, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.add, BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, id_eq]
  rw [preparePolynomialOffset_effect]
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp_all [Work.gateCount, Work.available,
    Work.reference₀, Work.temporary₃]

theorem emitPackedFormulaCopy_emitted_internal
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount) :
    (emitPackedFormulaCopy sizePolynomial).emitted values =
      (CircuitCode.RawGate.copy
        (values Work.gateCount +
          sizePolynomial.eval (values Work.horizon) - 1)).encode := by
  simp only [emitPackedFormulaCopy, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.add, BinaryRoutine.binaryCopy, BinaryRoutine.binaryPred,
    BinaryRoutine.emitRawGateStep, BinaryRoutine.clear,
    BinaryRoutine.identity, BinaryRoutine.emitBits, List.nil_append,
    List.append_nil]
  rw [preparePolynomialOffset_emitted, preparePolynomialOffset_effect]
  simp [CircuitCode.RawGate.copy, Work.temporary₃, Work.gateCount,
    Work.reference₀]

theorem emitPackedFormulaCopy_sound_internal
    (sizePolynomial : Polynomial ℕ) :
    (emitPackedFormulaCopy sizePolynomial).Sound := by
  let routine := BinaryRoutine.seqList
    [preparePolynomialOffset sizePolynomial,
      BinaryRoutine.add Work.temporary₃ Work.gateCount Work.addCounter,
      BinaryRoutine.binaryCopy Work.gateCount Work.reference₀
        Work.copyCounter,
      BinaryRoutine.binaryPred Work.reference₀,
      BinaryRoutine.emitRawGateStep .and false false Work.emitCounter
        Work.available Work.reference₀ Work.reference₀,
      BinaryRoutine.clear Work.reference₀,
      BinaryRoutine.clear Work.temporary₃]
  have hroutine : routine.Sound := by
    apply BinaryRoutine.seqList_sound
    intro member hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember | hmember | hmember | hmember |
      hmember | hmember
    · subst member
      exact preparePolynomialOffset_sound sizePolynomial
    · subst member
      exact BinaryRoutine.add_sound Work.temporary₃ Work.gateCount
        Work.addCounter
    · subst member
      exact BinaryRoutine.binaryCopy_sound Work.gateCount Work.reference₀
        Work.copyCounter
    · subst member
      exact BinaryRoutine.binaryPred_sound Work.reference₀
    · subst member
      exact BinaryRoutine.emitRawGateStep_sound .and false false
        Work.emitCounter Work.available Work.reference₀ Work.reference₀
    all_goals
      subst member
      exact BinaryRoutine.clear_sound _
  apply sound_with_stronger_requires routine _ hroutine
  intro values hrequires
  rcases hrequires with
    ⟨htemporary, hscratch, hmultiply, hadd, hcopy, hemit, hpositive⟩
  simp only [routine, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.clear, BinaryRoutine.identity, BinaryRoutine.emitBits,
    and_true]
  rw [preparePolynomialOffset_requires,
    preparePolynomialOffset_effect]
  simp [BinaryRoutine.add, BinaryRoutine.binaryCopy,
    BinaryRoutine.binaryPred, BinaryRoutine.emitRawGateStep,
    Work.horizon, Work.temporary₃, Work.polynomialScratch,
    Work.multiplyCounter, Work.addCounter, Work.gateCount,
    Work.copyCounter, Work.reference₀, Work.emitCounter, Work.available]
  refine ⟨⟨htemporary, hscratch, hmultiply, hadd⟩, hadd, hcopy,
    Or.inr hpositive, ?_, hemit⟩
  exact
    { emitCounter_ne_available := by decide
      emitCounter_ne_input₀ := by decide
      emitCounter_ne_input₁ := by decide
      available_ne_input₀ := by decide
      available_ne_input₁ := by decide }

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
