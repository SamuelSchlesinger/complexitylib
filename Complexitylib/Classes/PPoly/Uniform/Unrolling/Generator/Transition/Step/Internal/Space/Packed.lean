/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Space.Common

/-!
# Packed-copy space bound for one direct transition step

This module certifies the delayed-copy suffix after the next-formula stream has
been emitted. The proof follows the exact rolling formula cursor through the
state, head, and cell regions and bounds every loop prefix by the shared step
width envelope.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem StepWidthEnvelope.statePolynomialCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) (state : tm.Q) :
    2 * TM.binaryPolynomialValueCap (stateNextFormulaPolynomial tm state)
      (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap state .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  omega

private theorem StepWidthEnvelope.headPolynomialCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) (tape : TapeSlot k) :
    2 * TM.binaryPolynomialValueCap (headNextFormulaPolynomial tm tape)
      (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart tape .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  omega

private theorem StepWidthEnvelope.writtenPolynomialCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) (tape : WritableSlot k)
    (symbol : Γ) :
    2 * TM.binaryPolynomialValueCap
      (writtenNextFormulaPolynomial tm tape symbol)
      (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input tape symbol 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  omega

private theorem StepWidthEnvelope.onePolynomialCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    2 * TM.binaryPolynomialValueCap (Polynomial.C 1)
      (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  omega

private theorem StepWidthEnvelope.frontier_add_writtenCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) (tape : WritableSlot k)
    (symbol : Γ) :
    values Work.available + stepFormulasEffectSizeInternal tm
          (values Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap
          (writtenNextFormulaPolynomial tm tape symbol)
          (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input tape symbol 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
  omega

private theorem StepWidthEnvelope.frontier_add_oneCap_le_packed
    {tm : NTM k} {values : BinaryValues WorkCount} {width : ℕ}
    (henvelope : StepWidthEnvelope tm values width) :
    values Work.available + stepFormulasEffectSizeInternal tm
          (values Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k (values Work.horizon) +
        2 * TM.binaryPolynomialValueCap (Polynomial.C 1)
          (values Work.horizon) ≤ width := by
  have hcap := henvelope.cap tm.qstart .input .output .zero 0 0 0 0
    (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) (by omega) (by omega) (by omega)
  rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
  omega

private theorem stepFormulaSizeAtSpecialized_state_eq_eval_packed
    (tm : NTM k) (T : ℕ) (index : Fin (Fintype.card tm.Q)) :
    stepFormulaSizeAtSpecializedInternal tm T index.val =
      (stateNextFormulaPolynomial tm
        ((Fintype.equivFin tm.Q).symm index)).eval T := by
  rw [stateNextFormulaPolynomial_eval]
  exact stepFormulaSizeAtSpecialized_state_forSpace_internal tm T index

private theorem binaryForValues_copy_effect_packed
    (body : BinaryRoutine WorkCount) (sizeAt : ℕ → ℕ) (outputCount : ℕ)
    (values : BinaryValues WorkCount)
    (hbody : ∀ current : BinaryValues WorkCount,
      current Work.horizon = values Work.horizon →
      body.effect current =
        Function.update
          (Function.update
            (Function.update
              (Function.update current Work.gateCount
                (current Work.gateCount + sizeAt (current Work.position)))
              Work.available (current Work.available + outputCount))
          Work.reference₀ 0) Work.temporary₃ 0)
    (hposition : values Work.position = 0)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) (count : ℕ) :
    BinaryRoutine.binaryForValues body Work.position values count =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.position count) Work.gateCount
                (values Work.gateCount + prefixSize sizeAt count))
            Work.available (values Work.available + outputCount * count))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  cases count with
  | zero =>
      simp only [BinaryRoutine.binaryForValues, prefixSize, Nat.add_zero,
        Nat.mul_zero]
      symm
      have hpositionUpdate := Function.update_eq_self Work.position values
      simp only [hposition] at hpositionUpdate
      rw [hpositionUpdate, Function.update_eq_self, Function.update_eq_self]
      have hreferenceUpdate := Function.update_eq_self Work.reference₀ values
      simp only [hreference] at hreferenceUpdate
      rw [hreferenceUpdate]
      have htemporaryUpdate := Function.update_eq_self Work.temporary₃ values
      simp only [htemporary] at htemporaryUpdate
      exact htemporaryUpdate
  | succ count =>
      simpa [Nat.succ_eq_add_one] using
        binaryForValues_copy_succ_effect_forSpace_internal body sizeAt
          outputCount values hbody hposition count

private theorem prefixSize_const_packed (size count : ℕ) :
    prefixSize (fun _ => size) count = count * size := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [prefixSize_succ, ih]
      ring

private noncomputable def writableCopySizeAtPacked
    (tm : NTM k) (tape : WritableSlot k) (T position index : ℕ) : ℕ :=
  if hindex : index < 4 then
    let symbol := symbolEquiv.symm (⟨index, hindex⟩ : Fin 4)
    if position = 0 then 1 else
      (writtenNextFormulaPolynomial tm tape symbol).eval T
  else 0

private theorem writableCopySizeAt_sum_packed
    (tm : NTM k) (tape : WritableSlot k) (T position : ℕ) :
    prefixSize (writableCopySizeAtPacked tm tape T position) 4 =
      stepCellPositionEffectSizeInternal tm tape.toTapeSlot T position := by
  rw [prefixSize_eq_sum_ofFn]
  cases tape with
  | work index =>
      unfold stepCellPositionEffectSizeInternal
      apply congrArg List.sum
      apply List.ext_getElem
      · simp
      · intro i hleft hright
        simp [writableCopySizeAtPacked, writtenNextFormulaPolynomial_eval]
  | output =>
      unfold stepCellPositionEffectSizeInternal
      apply congrArg List.sum
      apply List.ext_getElem
      · simp
      · intro i hleft hright
        simp [writableCopySizeAtPacked, writtenNextFormulaPolynomial_eval]

private theorem emitStepStateCopies_spaceBoundByWidthAt_packed
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hgateCount : ∀ inputLength,
      values inputLength Work.gateCount =
        baseValues inputLength Work.available)
    (havailable : ∀ inputLength,
      values inputLength Work.available =
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepStateCopies tm)
      initialSpace values width := by
  let stateCount := Fintype.card tm.Q
  let stateAt : Fin stateCount → tm.Q := (Fintype.equivFin tm.Q).symm
  let sizeAt : ℕ → ℕ → ℕ := fun inputLength index =>
    stepFormulaSizeAtSpecializedInternal tm
      (baseValues inputLength Work.horizon) index
  let trajectory : ℕ → ℕ → BinaryValues WorkCount := fun count inputLength =>
    Function.update
      (Function.update
        (Function.update
          (Function.update (values inputLength) Work.gateCount
            (baseValues inputLength Work.available +
              prefixSize (sizeAt inputLength) count))
          Work.available
            (baseValues inputLength Work.available +
              stepFormulasEffectSizeInternal tm
                (baseValues inputLength Work.horizon) + count))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count inputLength : ℕ) :
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    have h := hhorizonEq inputLength
    simp [Work.horizon] at h
    simpa [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃] using h
  have htrajectoryGateCount (count inputLength : ℕ) :
      trajectory count inputLength Work.gateCount =
        baseValues inputLength Work.available +
          prefixSize (sizeAt inputLength) count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have htrajectoryAvailable (count inputLength : ℕ) :
      trajectory count inputLength Work.available =
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) + count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hzero : trajectory 0 = values := by
    funext inputLength index
    have href :=
      (hclean inputLength).caseFormulaClean_forSpace_internal.reference₀
    have htemporary :=
      (hclean inputLength).caseFormulaClean_forSpace_internal.temporary₃
    by_cases hgate : index = Work.gateCount
    · subst index
      simpa [trajectory, sizeAt, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃] using (hgateCount inputLength).symm
    · by_cases havail : index = Work.available
      · subst index
        simpa [trajectory, sizeAt, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃] using (havailable inputLength).symm
      · by_cases hreference : index = Work.reference₀
        · subst index
          simpa [trajectory, sizeAt, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃] using href.symm
        · by_cases htemporaryIndex : index = Work.temporary₃
          · subst index
            simpa [trajectory, sizeAt, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using htemporary.symm
          · simp [trajectory, sizeAt, hgate, havail, hreference,
              htemporaryIndex]
  have hspace (index : Fin stateCount) :
      BinaryRoutine.SpaceBoundByWidthAt
        (emitPackedFormulaCopy (stateNextFormulaPolynomial tm (stateAt index)))
        initialSpace (trajectory index.val) width := by
    apply emitPackedFormulaCopy_spaceBoundByWidth
    · intro inputLength
      rw [htrajectoryHorizon]
      exact (henvelope inputLength).statePolynomialCap_le_packed (stateAt index)
    · intro inputLength
      have hprefix := prefixSize_mono (sizeAt inputLength)
        (show index.val + 1 ≤ stateCount by omega)
      rw [← stepStateFormulasEffectSize_eq_prefixSize_internal] at hprefix
      have hfinal := (henvelope inputLength).finalFrontier_le_internal
      have hsize : sizeAt inputLength index.val =
          (stateNextFormulaPolynomial tm (stateAt index)).eval
            (baseValues inputLength Work.horizon) := by
        simpa [sizeAt, stateAt] using
          stepFormulaSizeAtSpecialized_state_eq_eval_packed tm
            (baseValues inputLength Work.horizon) index
      rw [htrajectoryGateCount, htrajectoryHorizon]
      rw [← hsize]
      have hstateLe : stepStateFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) ≤
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) := by
        unfold stepFormulasEffectSizeInternal
        omega
      calc
        baseValues inputLength Work.available +
              prefixSize (sizeAt inputLength) index.val +
            sizeAt inputLength index.val =
            baseValues inputLength Work.available +
              prefixSize (sizeAt inputLength) (index.val + 1) := by
                rw [prefixSize_succ]
                omega
        _ ≤ baseValues inputLength Work.available +
              stepStateFormulasEffectSizeInternal tm
                (baseValues inputLength Work.horizon) := by omega
        _ ≤ baseValues inputLength Work.available +
              stepFormulasEffectSizeInternal tm
                (baseValues inputLength Work.horizon) := by omega
        _ ≤ width inputLength := by omega
    · intro inputLength
      have hfinal := (henvelope inputLength).finalFrontier_le_internal
      rw [htrajectoryAvailable]
      unfold stepAtomCount at hfinal
      omega
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      rw [htrajectoryHorizon]
      exact stateNextFormulaPolynomial_eval_pos_internal tm (stateAt index)
        (baseValues inputLength Work.horizon)
  have hstep (index : Fin stateCount) (inputLength : ℕ) :
      (emitPackedFormulaCopy
          (stateNextFormulaPolynomial tm (stateAt index))).effect
          (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength := by
    rw [emitPackedFormulaCopy_effect]
    have hsize : sizeAt inputLength index.val =
        (stateNextFormulaPolynomial tm (stateAt index)).eval
          (baseValues inputLength Work.horizon) := by
      simpa [sizeAt, stateAt] using
        stepFormulaSizeAtSpecialized_state_eq_eval_packed tm
          (baseValues inputLength Work.horizon) index
    rw [htrajectoryHorizon, ← hsize]
    funext register
    by_cases hgate : register = Work.gateCount
    · subst register
      simp [trajectory, sizeAt, prefixSize_succ, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
      omega
    · by_cases havail : register = Work.available
      · subst register
        simp [trajectory, sizeAt, prefixSize_succ, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
        omega
      · by_cases hreference : register = Work.reference₀
        · subst register
          simp [trajectory, sizeAt, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃, Work.horizon]
        · by_cases htemporary : register = Work.temporary₃
          · subst register
            simp [trajectory, sizeAt, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.horizon]
          · have hgateNum : register ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : register ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using hreference
            have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemporary
            simp [trajectory, sizeAt, hgateNum, havailNum, hreferenceNum,
              htemporaryNum, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
  unfold emitStepStateCopies
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact seqList_ofFn_spaceBoundByWidthAt_internal stateCount
    (fun index =>
      emitPackedFormulaCopy (stateNextFormulaPolynomial tm (stateAt index)))
    trajectory hzero hspace hstep

private theorem emitStepHeadTapeCopies_spaceBoundByWidthAt_packed
    (tm : NTM k) (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hposition : ∀ inputLength, values inputLength Work.position = 0)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 1)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount +
          (baseValues inputLength Work.horizon + 1) *
            (headNextFormulaPolynomial tm tape).eval
              (baseValues inputLength Work.horizon) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available +
          (baseValues inputLength Work.horizon + 1) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepHeadTapeCopies tm tape)
      initialSpace values width := by
  let polynomial := headNextFormulaPolynomial tm tape
  let body := emitPackedFormulaCopy polynomial
  let pairedInput : ℕ → ℕ := fun code => (Nat.unpair code).1
  let pairedCount : ℕ → ℕ := fun code =>
    min (Nat.unpair code).2
      (BinaryRoutine.binaryForCount Work.position Work.limit₁
        (values (pairedInput code)) - 1)
  let pairedValues := BinaryRoutine.binaryForClampedValues body Work.position
    Work.limit₁ values
  let pairedInitialSpace : ℕ → ℕ := fun code => initialSpace (pairedInput code)
  let pairedWidth : ℕ → ℕ := fun code => width (pairedInput code)
  have hpairedCount (code : ℕ) :
      pairedCount code < baseValues (pairedInput code) Work.horizon + 1 := by
    have hmin := Nat.min_le_right (Nat.unpair code).2
      (baseValues (pairedInput code) Work.horizon)
    have htotal : BinaryRoutine.binaryForCount Work.position Work.limit₁
          (values (pairedInput code)) =
        baseValues (pairedInput code) Work.horizon + 1 := by
      simp [BinaryRoutine.binaryForCount, hlimit, hposition]
    simp only [pairedCount, htotal] at hmin ⊢
    omega
  have hpairedEffect (code : ℕ) :
      pairedValues code =
        Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (values (pairedInput code)) Work.position
                  (pairedCount code))
                Work.gateCount
                  (values (pairedInput code) Work.gateCount +
                    prefixSize
                      (fun _ => polynomial.eval
                        (values (pairedInput code) Work.horizon))
                      (pairedCount code)))
              Work.available
                (values (pairedInput code) Work.available + pairedCount code))
            Work.reference₀ 0) Work.temporary₃ 0 := by
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl]
    simpa using binaryForValues_copy_effect_packed body
      (fun _ => polynomial.eval (values (pairedInput code) Work.horizon)) 1
      (values (pairedInput code)) (by
        intro current hcurrentHorizon
        rw [emitPackedFormulaCopy_effect, hcurrentHorizon])
      (hposition (pairedInput code)) (hreference (pairedInput code))
      (htemporary (pairedInput code)) (pairedCount code)
  have hpairedHorizon (code : ℕ) :
      pairedValues code Work.horizon =
        baseValues (pairedInput code) Work.horizon := by
    rw [hpairedEffect]
    have h := hhorizonEq (pairedInput code)
    simp [Work.horizon] at h
    simpa [Work.horizon, Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃] using h
  have hpairedGateCount (code : ℕ) :
      pairedValues code Work.gateCount =
        values (pairedInput code) Work.gateCount +
          pairedCount code * polynomial.eval
            (baseValues (pairedInput code) Work.horizon) := by
    rw [hpairedEffect, hhorizonEq (pairedInput code)]
    simp [prefixSize_const_packed, Work.horizon, Work.position,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
      polynomial]
  have hpairedAvailable (code : ℕ) :
      pairedValues code Work.available =
        values (pairedInput code) Work.available + pairedCount code := by
    rw [hpairedEffect]
    simp [Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  have hpairedReference (code : ℕ) :
      pairedValues code Work.reference₀ = 0 := by
    rw [hpairedEffect]
    simp [Work.reference₀, Work.temporary₃]
  have hbodySpace : BinaryRoutine.SpaceBoundByWidthAt body pairedInitialSpace
      pairedValues pairedWidth := by
    apply emitPackedFormulaCopy_spaceBoundByWidth
    · intro code
      rw [hpairedHorizon]
      exact (henvelope (pairedInput code)).headPolynomialCap_le_packed tape
    · intro code
      have hbound := hgateEnd (pairedInput code)
      have hcount := hpairedCount code
      have hfinal := (henvelope (pairedInput code)).finalFrontier_le_internal
      rw [hpairedGateCount, hpairedHorizon]
      dsimp only [pairedWidth]
      simp only [polynomial] at hbound ⊢
      have hmul := Nat.mul_le_mul_right
        ((headNextFormulaPolynomial tm tape).eval
          (baseValues (pairedInput code) Work.horizon))
        (show pairedCount code + 1 ≤
            baseValues (pairedInput code) Work.horizon + 1 by omega)
      have hrearrange :
          values (pairedInput code) Work.gateCount +
                pairedCount code *
                  (headNextFormulaPolynomial tm tape).eval
                    (baseValues (pairedInput code) Work.horizon) +
              (headNextFormulaPolynomial tm tape).eval
                (baseValues (pairedInput code) Work.horizon) =
            values (pairedInput code) Work.gateCount +
              (pairedCount code + 1) *
                (headNextFormulaPolynomial tm tape).eval
                  (baseValues (pairedInput code) Work.horizon) := by ring
      rw [hrearrange]
      omega
    · intro code
      have hbound := havailableEnd (pairedInput code)
      have hcount := hpairedCount code
      have hfinal := (henvelope (pairedInput code)).finalFrontier_le_internal
      rw [hpairedAvailable]
      dsimp only [pairedWidth]
      omega
    · intro code
      rw [hpairedReference]
      exact Nat.zero_le _
    · intro code
      rw [hpairedHorizon]
      exact headNextFormulaPolynomial_eval_pos_internal tm tape
        (baseValues (pairedInput code) Work.horizon)
  rw [emitStepHeadTapeCopies]
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    · intro inputLength
      rw [hlimit inputLength]
      exact le_trans (by omega)
        (henvelope inputLength).horizon_add_two_le_internal
    · intro inputLength count hcount
      have heffect := binaryForValues_copy_effect_packed body
        (fun _ => polynomial.eval (values inputLength Work.horizon)) 1
        (values inputLength) (by
          intro current hcurrentHorizon
          rw [emitPackedFormulaCopy_effect, hcurrentHorizon])
        (hposition inputLength) (hreference inputLength)
        (htemporary inputLength) count
      rw [heffect]
      simp [Work.position, Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃]
      have hlimitBound := (henvelope inputLength).horizon_add_two_le_internal
      simp only [BinaryRoutine.binaryForCount] at hcount
      rw [hlimit inputLength, hposition inputLength] at hcount
      omega
    · simpa [pairedInitialSpace, pairedWidth, pairedValues, pairedInput,
        pairedCount, body] using hbodySpace
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    change BinaryRoutine.binaryForValues body Work.position
        (values inputLength)
        (values inputLength Work.limit₁ - values inputLength Work.position)
          Work.position ≤ width inputLength
    have heffect := binaryForValues_copy_effect_packed body
      (fun _ => polynomial.eval (values inputLength Work.horizon)) 1
      (values inputLength) (by
        intro current hcurrentHorizon
        rw [emitPackedFormulaCopy_effect, hcurrentHorizon])
      (hposition inputLength) (hreference inputLength)
      (htemporary inputLength)
      (values inputLength Work.limit₁ - values inputLength Work.position)
    rw [heffect]
    simp [Work.position, Work.limit₁, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
    have hlimitBound := (henvelope inputLength).horizon_add_two_le_internal
    have hpositionZero := hposition inputLength
    simp [Work.position] at hpositionZero
    have hlimitEq := hlimit inputLength
    simp [Work.limit₁] at hlimitEq
    omega

private theorem emitStepImmutableCellCopies_spaceBoundByWidthAt_packed
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount + 4 ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available + 4 ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SpaceBoundByWidthAt emitStepImmutableCellCopies
      initialSpace values width := by
  let routine := emitPackedFormulaCopy (Polynomial.C 1)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount := fun count inputLength =>
    Function.update
      (Function.update
        (Function.update
          (Function.update (values inputLength) Work.gateCount
            (values inputLength Work.gateCount + count))
          Work.available (values inputLength Work.available + count))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count inputLength : ℕ) :
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [show trajectory count inputLength Work.horizon =
        values inputLength Work.horizon by
      simp [trajectory, Work.horizon, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hhorizonEq inputLength
  have htrajectoryGateCount (count inputLength : ℕ) :
      trajectory count inputLength Work.gateCount =
        values inputLength Work.gateCount + count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have htrajectoryAvailable (count inputLength : ℕ) :
      trajectory count inputLength Work.available =
        values inputLength Work.available + count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hzero : trajectory 0 = values := by
    funext inputLength
    dsimp only [trajectory]
    simp only [Nat.add_zero]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate :=
      Function.update_eq_self Work.reference₀ (values inputLength)
    simp only [hreference inputLength] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate :=
      Function.update_eq_self Work.temporary₃ (values inputLength)
    simp only [htemporary inputLength] at htemporaryUpdate
    exact htemporaryUpdate
  have hspace (index : Fin 4) :
      BinaryRoutine.SpaceBoundByWidthAt routine initialSpace
        (trajectory index.val) width := by
    apply emitPackedFormulaCopy_spaceBoundByWidth
    · intro inputLength
      rw [htrajectoryHorizon]
      exact (henvelope inputLength).onePolynomialCap_le_packed
    · intro inputLength
      have hbound := hgateEnd inputLength
      have hfinal := (henvelope inputLength).finalFrontier_le_internal
      rw [htrajectoryGateCount]
      simp
      omega
    · intro inputLength
      have hbound := havailableEnd inputLength
      have hfinal := (henvelope inputLength).finalFrontier_le_internal
      rw [htrajectoryAvailable]
      omega
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      simp
  have hstep (index : Fin 4) (inputLength : ℕ) :
      routine.effect (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength := by
    rw [show routine.effect (trajectory index.val inputLength) =
        (emitPackedFormulaCopy (Polynomial.C 1)).effect
          (trajectory index.val inputLength) by rfl,
      emitPackedFormulaCopy_effect]
    funext register
    by_cases hgate : register = Work.gateCount
    · subst register
      simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃]
      omega
    · by_cases havail : register = Work.available
      · subst register
        simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
        omega
      · by_cases hreferenceIndex : register = Work.reference₀
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIndex : register = Work.temporary₃
          · subst register
            simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
          · have hgateNum : register ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : register ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using hreferenceIndex
            have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemporaryIndex
            simp [trajectory, hgateNum, havailNum, hreferenceNum,
              htemporaryNum, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
  unfold emitStepImmutableCellCopies BinaryRoutine.repeatRoutine
  rw [show List.replicate 4 routine = List.ofFn (fun _ : Fin 4 => routine) by
    simp]
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact seqList_ofFn_spaceBoundByWidthAt_internal 4 (fun _ => routine)
    trajectory hzero hspace hstep

private theorem emitStepWritableCellCopies_spaceBoundByWidthAt_packed
    (tm : NTM k) (tape : WritableSlot k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount +
          stepCellPositionEffectSizeInternal tm tape.toTapeSlot
            (baseValues inputLength Work.horizon)
            (values inputLength Work.position) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available + 4 ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepWritableCellCopies tm tape)
      initialSpace values width := by
  let symbolAt : Fin 4 → Γ := symbolEquiv.symm
  let routineAt : Fin 4 → BinaryRoutine WorkCount := fun index =>
    BinaryRoutine.branchZero Work.position
      (emitPackedFormulaCopy (Polynomial.C 1))
      (emitPackedFormulaCopy
        (writtenNextFormulaPolynomial tm tape (symbolAt index)))
  let sizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    writableCopySizeAtPacked tm tape
      (baseValues inputLength Work.horizon)
      (values inputLength Work.position)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount := fun count inputLength =>
    Function.update
      (Function.update
        (Function.update
          (Function.update (values inputLength) Work.gateCount
            (values inputLength Work.gateCount +
              prefixSize (sizeAt inputLength) count))
          Work.available (values inputLength Work.available + count))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count inputLength : ℕ) :
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [show trajectory count inputLength Work.horizon =
        values inputLength Work.horizon by
      simp [trajectory, Work.horizon, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hhorizonEq inputLength
  have htrajectoryPosition (count inputLength : ℕ) :
      trajectory count inputLength Work.position =
        values inputLength Work.position := by
    simp [trajectory, Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  have htrajectoryGateCount (count inputLength : ℕ) :
      trajectory count inputLength Work.gateCount =
        values inputLength Work.gateCount +
          prefixSize (sizeAt inputLength) count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have htrajectoryAvailable (count inputLength : ℕ) :
      trajectory count inputLength Work.available =
        values inputLength Work.available + count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hzero : trajectory 0 = values := by
    funext inputLength
    dsimp only [trajectory]
    simp only [prefixSize, Nat.add_zero]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate :=
      Function.update_eq_self Work.reference₀ (values inputLength)
    simp only [hreference inputLength] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate :=
      Function.update_eq_self Work.temporary₃ (values inputLength)
    simp only [htemporary inputLength] at htemporaryUpdate
    exact htemporaryUpdate
  have hgateBefore (index : Fin 4) (inputLength : ℕ) :
      trajectory index.val inputLength Work.gateCount ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) := by
    rw [htrajectoryGateCount]
    have hprefix := prefixSize_mono (sizeAt inputLength)
      (show index.val ≤ 4 by omega)
    rw [writableCopySizeAt_sum_packed] at hprefix
    have hbound := hgateEnd inputLength
    simpa [sizeAt] using Nat.add_le_add_left hprefix
      (values inputLength Work.gateCount) |>.trans hbound
  have havailableBefore (index : Fin 4) (inputLength : ℕ) :
      trajectory index.val inputLength Work.available ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon) := by
    rw [htrajectoryAvailable]
    have hbound := havailableEnd inputLength
    omega
  have honeSpace (index : Fin 4) :
      BinaryRoutine.SpaceBoundByWidthAt
        (emitPackedFormulaCopy (Polynomial.C 1)) initialSpace
        (trajectory index.val) width := by
    apply emitPackedFormulaCopy_spaceBoundByWidth
    · intro inputLength
      rw [htrajectoryHorizon]
      exact (henvelope inputLength).onePolynomialCap_le_packed
    · intro inputLength
      rw [htrajectoryHorizon]
      have hgate := hgateBefore index inputLength
      have hcap := (henvelope inputLength).frontier_add_oneCap_le_packed
      have heval := TM.binaryPolynomial_eval_le_valueCap (Polynomial.C 1)
        (baseValues inputLength Work.horizon)
      simp only [Polynomial.eval_C] at heval ⊢
      omega
    · exact fun inputLength => le_trans
        (havailableBefore index inputLength)
        (henvelope inputLength).finalFrontier_le_internal
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      simp
  have hwrittenSpace (index : Fin 4) :
      BinaryRoutine.SpaceBoundByWidthAt
        (emitPackedFormulaCopy
          (writtenNextFormulaPolynomial tm tape (symbolAt index)))
        initialSpace (trajectory index.val) width := by
    apply emitPackedFormulaCopy_spaceBoundByWidth
    · intro inputLength
      rw [htrajectoryHorizon]
      exact (henvelope inputLength).writtenPolynomialCap_le_packed tape
        (symbolAt index)
    · intro inputLength
      rw [htrajectoryHorizon]
      have hgate := hgateBefore index inputLength
      have hcap :=
        (henvelope inputLength).frontier_add_writtenCap_le_packed tape
          (symbolAt index)
      have heval := TM.binaryPolynomial_eval_le_valueCap
        (writtenNextFormulaPolynomial tm tape (symbolAt index))
        (baseValues inputLength Work.horizon)
      omega
    · exact fun inputLength => le_trans
        (havailableBefore index inputLength)
        (henvelope inputLength).finalFrontier_le_internal
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      rw [htrajectoryHorizon]
      exact writtenNextFormulaPolynomial_eval_pos_internal tm tape
        (symbolAt index) (baseValues inputLength Work.horizon)
  have hspace (index : Fin 4) :
      BinaryRoutine.SpaceBoundByWidthAt (routineAt index) initialSpace
        (trajectory index.val) width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.branchZero
    · exact honeSpace index
    · exact hwrittenSpace index
  have hstep (index : Fin 4) (inputLength : ℕ) :
      (routineAt index).effect (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength := by
    have hsize : sizeAt inputLength index.val =
        if values inputLength Work.position = 0 then 1 else
          (writtenNextFormulaPolynomial tm tape (symbolAt index)).eval
            (baseValues inputLength Work.horizon) := by
      simp [sizeAt, writableCopySizeAtPacked, symbolAt, index.isLt]
    have heffect : (routineAt index).effect
          (trajectory index.val inputLength) =
        Function.update
          (Function.update
            (Function.update
              (Function.update (trajectory index.val inputLength)
                Work.gateCount
                  (trajectory index.val inputLength Work.gateCount +
                    sizeAt inputLength index.val))
              Work.available
                (trajectory index.val inputLength Work.available + 1))
            Work.reference₀ 0) Work.temporary₃ 0 := by
      by_cases hpositionZero : values inputLength Work.position = 0
      · simp [routineAt, BinaryRoutine.branchZero, htrajectoryPosition,
          hpositionZero, emitPackedFormulaCopy_effect, hsize]
      · simp [routineAt, BinaryRoutine.branchZero, htrajectoryPosition,
          hpositionZero, emitPackedFormulaCopy_effect, hsize,
          htrajectoryHorizon]
    rw [heffect]
    funext register
    by_cases hgate : register = Work.gateCount
    · subst register
      simp [trajectory, prefixSize_succ, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
      omega
    · by_cases havail : register = Work.available
      · subst register
        simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
        omega
      · by_cases hreferenceIndex : register = Work.reference₀
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIndex : register = Work.temporary₃
          · subst register
            simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
          · have hgateNum : register ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : register ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using hreferenceIndex
            have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemporaryIndex
            simp [trajectory, hgateNum, havailNum, hreferenceNum,
              htemporaryNum, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
  unfold emitStepWritableCellCopies
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  exact seqList_ofFn_spaceBoundByWidthAt_internal 4 routineAt trajectory
    hzero hspace hstep

private noncomputable def cellCopyBodyPacked (tm : NTM k) :
    TapeSlot k → BinaryRoutine WorkCount
  | .input => emitStepImmutableCellCopies
  | .work index => emitStepWritableCellCopies tm (.work index)
  | .output => emitStepWritableCellCopies tm .output

private theorem cellCopyBody_effect_packed (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount) :
    (cellCopyBodyPacked tm tape).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + stepCellPositionEffectSizeInternal tm
                tape (values Work.horizon) (values Work.position)))
            Work.available (values Work.available + 4))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  cases tape with
  | input =>
      simpa [stepCellPositionEffectSizeInternal]
        using! emitStepImmutableCellCopies_effect_internal values
  | work index =>
      simpa using! emitStepWritableCellCopies_effect_internal tm (.work index)
        values
  | output =>
      simpa using! emitStepWritableCellCopies_effect_internal tm .output values

private theorem emitStepCellTapeCopies_spaceBoundByWidthAt_packed
    (tm : NTM k) (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hposition : ∀ inputLength, values inputLength Work.position = 0)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 2)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount +
          prefixSize (stepCellPositionEffectSizeInternal tm tape
            (baseValues inputLength Work.horizon))
            (baseValues inputLength Work.horizon + 2) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available +
          4 * (baseValues inputLength Work.horizon + 2) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepCellTapeCopies tm tape)
      initialSpace values width := by
  let body : BinaryRoutine WorkCount := cellCopyBodyPacked tm tape
  let sizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    stepCellPositionEffectSizeInternal tm tape
      (baseValues inputLength Work.horizon)
  let pairedInput : ℕ → ℕ := fun code => (Nat.unpair code).1
  let pairedCount : ℕ → ℕ := fun code =>
    min (Nat.unpair code).2
      (BinaryRoutine.binaryForCount Work.position Work.limit₁
        (values (pairedInput code)) - 1)
  let pairedValues := BinaryRoutine.binaryForClampedValues body Work.position
    Work.limit₁ values
  let pairedBaseValues : ℕ → BinaryValues WorkCount := fun code =>
    baseValues (pairedInput code)
  let pairedInitialSpace : ℕ → ℕ := fun code => initialSpace (pairedInput code)
  let pairedWidth : ℕ → ℕ := fun code => width (pairedInput code)
  have hpairedCount (code : ℕ) :
      pairedCount code < baseValues (pairedInput code) Work.horizon + 2 := by
    have hmin := Nat.min_le_right (Nat.unpair code).2
      (baseValues (pairedInput code) Work.horizon + 1)
    have htotal : BinaryRoutine.binaryForCount Work.position Work.limit₁
          (values (pairedInput code)) =
        baseValues (pairedInput code) Work.horizon + 2 := by
      simp [BinaryRoutine.binaryForCount, hlimit, hposition]
    simp only [pairedCount, htotal] at hmin ⊢
    omega
  have hpairedEffect (code : ℕ) :
      pairedValues code =
        Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (values (pairedInput code)) Work.position
                  (pairedCount code))
                Work.gateCount
                  (values (pairedInput code) Work.gateCount +
                    prefixSize (sizeAt (pairedInput code))
                      (pairedCount code)))
              Work.available
                (values (pairedInput code) Work.available +
                  4 * pairedCount code))
            Work.reference₀ 0) Work.temporary₃ 0 := by
    rw [show pairedValues code =
        BinaryRoutine.binaryForValues body Work.position
          (values (pairedInput code)) (pairedCount code) by rfl]
    simpa using binaryForValues_copy_effect_packed body
      (sizeAt (pairedInput code)) 4 (values (pairedInput code)) (by
        intro current hcurrentHorizon
        rw [show body.effect current =
          (cellCopyBodyPacked tm tape).effect current by rfl,
          cellCopyBody_effect_packed]
        rw [hcurrentHorizon, hhorizonEq (pairedInput code)])
      (hposition (pairedInput code)) (hreference (pairedInput code))
      (htemporary (pairedInput code)) (pairedCount code)
  have hpairedHorizon (code : ℕ) :
      pairedValues code Work.horizon =
        baseValues (pairedInput code) Work.horizon := by
    rw [hpairedEffect]
    have h := hhorizonEq (pairedInput code)
    simp [Work.horizon] at h
    simpa [Work.horizon, Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃] using h
  have hpairedPosition (code : ℕ) :
      pairedValues code Work.position = pairedCount code := by
    rw [hpairedEffect]
    simp [Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hpairedGateCount (code : ℕ) :
      pairedValues code Work.gateCount =
        values (pairedInput code) Work.gateCount +
          prefixSize (sizeAt (pairedInput code)) (pairedCount code) := by
    rw [hpairedEffect]
    simp [Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hpairedAvailable (code : ℕ) :
      pairedValues code Work.available =
        values (pairedInput code) Work.available + 4 * pairedCount code := by
    rw [hpairedEffect]
    simp [Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hpairedReference (code : ℕ) :
      pairedValues code Work.reference₀ = 0 := by
    rw [hpairedEffect]
    simp [Work.reference₀, Work.temporary₃]
  have hpairedTemporary (code : ℕ) :
      pairedValues code Work.temporary₃ = 0 := by
    rw [hpairedEffect]
    simp [Work.temporary₃]
  have hbodySpace : BinaryRoutine.SpaceBoundByWidthAt body pairedInitialSpace
      pairedValues pairedWidth := by
    have hgateCurrent : ∀ code,
        pairedValues code Work.gateCount +
            sizeAt (pairedInput code) (pairedValues code Work.position) ≤
          baseValues (pairedInput code) Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues (pairedInput code) Work.horizon) := by
      intro code
      rw [hpairedGateCount, hpairedPosition]
      have hprefix := prefixSize_mono (sizeAt (pairedInput code))
        (show pairedCount code + 1 ≤
          baseValues (pairedInput code) Work.horizon + 2 by
            exact hpairedCount code)
      rw [prefixSize_succ] at hprefix
      have htotal := hgateEnd (pairedInput code)
      change values (pairedInput code) Work.gateCount +
          prefixSize (sizeAt (pairedInput code))
            (baseValues (pairedInput code) Work.horizon + 2) ≤ _ at htotal
      omega
    have havailableCurrent : ∀ code,
        pairedValues code Work.available + 4 ≤
          baseValues (pairedInput code) Work.available +
              stepFormulasEffectSizeInternal tm
                (baseValues (pairedInput code) Work.horizon) +
            stepAtomCount (Fintype.card tm.Q) k
              (baseValues (pairedInput code) Work.horizon) := by
      intro code
      rw [hpairedAvailable]
      have hcount := hpairedCount code
      have hbound := havailableEnd (pairedInput code)
      omega
    cases tape with
    | input =>
        simpa [body, cellCopyBodyPacked, pairedBaseValues, pairedInitialSpace,
          pairedWidth] using
          emitStepImmutableCellCopies_spaceBoundByWidthAt_packed tm
            (initialSpace := pairedInitialSpace)
            (baseValues := pairedBaseValues) (values := pairedValues)
            (width := pairedWidth)
            (fun code => henvelope (pairedInput code)) hpairedHorizon
            hgateCurrent havailableCurrent hpairedReference hpairedTemporary
    | work index =>
        simpa [body, cellCopyBodyPacked, sizeAt, pairedBaseValues,
          pairedInitialSpace, pairedWidth] using
          emitStepWritableCellCopies_spaceBoundByWidthAt_packed tm
            (.work index) (initialSpace := pairedInitialSpace)
            (baseValues := pairedBaseValues) (values := pairedValues)
            (width := pairedWidth)
            (fun code => henvelope (pairedInput code)) hpairedHorizon
            hgateCurrent havailableCurrent hpairedReference hpairedTemporary
    | output =>
        simpa [body, cellCopyBodyPacked, sizeAt, pairedBaseValues,
          pairedInitialSpace, pairedWidth] using
          emitStepWritableCellCopies_spaceBoundByWidthAt_packed tm
            .output (initialSpace := pairedInitialSpace)
            (baseValues := pairedBaseValues) (values := pairedValues)
            (width := pairedWidth)
            (fun code => henvelope (pairedInput code)) hpairedHorizon
            hgateCurrent havailableCurrent hpairedReference hpairedTemporary
  have hdefinition : emitStepCellTapeCopies tm tape =
      BinaryRoutine.seq
        (BinaryRoutine.binaryFor body Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position) := by
    cases tape <;> rfl
  rw [hdefinition]
  apply BinaryRoutine.SpaceBoundByWidthAt.seq
  · apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    · intro inputLength
      rw [hlimit inputLength]
      exact (henvelope inputLength).horizon_add_two_le_internal
    · intro inputLength count hcount
      have heffect := binaryForValues_copy_effect_packed body
        (sizeAt inputLength) 4 (values inputLength) (by
          intro current hcurrentHorizon
          rw [show body.effect current =
            (cellCopyBodyPacked tm tape).effect current by rfl,
            cellCopyBody_effect_packed]
          rw [hcurrentHorizon, hhorizonEq inputLength])
        (hposition inputLength) (hreference inputLength)
        (htemporary inputLength) count
      rw [heffect]
      simp [Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
      have hlimitBound := (henvelope inputLength).horizon_add_two_le_internal
      simp [BinaryRoutine.binaryForCount, Work.position, Work.limit₁] at hcount
      have hpositionZero := hposition inputLength
      simp [Work.position] at hpositionZero
      have hlimitEq := hlimit inputLength
      simp [Work.limit₁] at hlimitEq
      omega
    · simpa [pairedInitialSpace, pairedWidth, pairedValues, pairedInput,
        pairedCount, body] using hbodySpace
  · apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    change BinaryRoutine.binaryForValues body Work.position
        (values inputLength)
        (values inputLength Work.limit₁ - values inputLength Work.position)
          Work.position ≤ width inputLength
    have heffect := binaryForValues_copy_effect_packed body
      (sizeAt inputLength) 4 (values inputLength) (by
        intro current hcurrentHorizon
        rw [show body.effect current =
          (cellCopyBodyPacked tm tape).effect current by rfl,
          cellCopyBody_effect_packed]
        rw [hcurrentHorizon, hhorizonEq inputLength])
      (hposition inputLength) (hreference inputLength)
      (htemporary inputLength)
      (values inputLength Work.limit₁ - values inputLength Work.position)
    rw [heffect]
    simp [Work.position, Work.limit₁, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
    have hlimitBound := (henvelope inputLength).horizon_add_two_le_internal
    have hpositionZero := hposition inputLength
    simp [Work.position] at hpositionZero
    have hlimitEq := hlimit inputLength
    simp [Work.limit₁] at hlimitEq
    omega

private noncomputable def headCopyBlockSizeAtPacked
    (tm : NTM k) (T index : ℕ) : ℕ :=
  if hindex : index < k + 2 then
    (T + 1) * (headNextFormulaPolynomial tm
      ((tapeSlotEquiv k).symm ⟨index, hindex⟩)).eval T
  else 0

private theorem headCopyBlockSizeAt_sum_packed (tm : NTM k) (T : ℕ) :
    prefixSize (headCopyBlockSizeAtPacked tm T) (k + 2) =
      stepHeadFormulasEffectSizeInternal tm T := by
  rw [prefixSize_eq_sum_ofFn]
  unfold stepHeadFormulasEffectSizeInternal
  rw [List.map_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [headCopyBlockSizeAtPacked, headNextFormulaPolynomial_eval]

private noncomputable def cellCopyBlockSizeAtPacked
    (tm : NTM k) (T index : ℕ) : ℕ :=
  if hindex : index < k + 2 then
    prefixSize (stepCellPositionEffectSizeInternal tm
      ((tapeSlotEquiv k).symm ⟨index, hindex⟩) T) (T + 2)
  else 0

private theorem cellCopyBlockSizeAt_sum_packed (tm : NTM k) (T : ℕ) :
    prefixSize (cellCopyBlockSizeAtPacked tm T) (k + 2) =
      stepCellFormulasEffectSizeInternal tm T := by
  rw [prefixSize_eq_sum_ofFn]
  unfold stepCellFormulasEffectSizeInternal
  rw [List.map_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp [cellCopyBlockSizeAtPacked]

private theorem emitStepHeadTapeCopiesList_seqListSpaceBoundByWidthAt_packed
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hposition : ∀ inputLength, values inputLength Work.position = 0)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 1)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount +
          stepHeadFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available +
          (k + 2) * (baseValues inputLength Work.horizon + 1) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepHeadTapeCopies tm)) initialSpace values width := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let blockSizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    headCopyBlockSizeAtPacked tm (baseValues inputLength Work.horizon)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount := fun count inputLength =>
    Function.update
      (Function.update
        (Function.update
          (Function.update (values inputLength) Work.gateCount
            (values inputLength Work.gateCount +
              prefixSize (blockSizeAt inputLength) count))
          Work.available
            (values inputLength Work.available +
              count * (baseValues inputLength Work.horizon + 1)))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count inputLength : ℕ) :
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [show trajectory count inputLength Work.horizon =
        values inputLength Work.horizon by
      simp [trajectory, Work.horizon, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hhorizonEq inputLength
  have htrajectoryPosition (count inputLength : ℕ) :
      trajectory count inputLength Work.position = 0 := by
    rw [show trajectory count inputLength Work.position =
        values inputLength Work.position by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hposition inputLength
  have htrajectoryLimit (count inputLength : ℕ) :
      trajectory count inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 1 := by
    rw [show trajectory count inputLength Work.limit₁ =
        values inputLength Work.limit₁ by
      simp [trajectory, Work.limit₁, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hlimit inputLength
  have htrajectoryGateCount (count inputLength : ℕ) :
      trajectory count inputLength Work.gateCount =
        values inputLength Work.gateCount +
          prefixSize (blockSizeAt inputLength) count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have htrajectoryAvailable (count inputLength : ℕ) :
      trajectory count inputLength Work.available =
        values inputLength Work.available +
          count * (baseValues inputLength Work.horizon + 1) := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hzero : trajectory 0 = values := by
    funext inputLength
    dsimp only [trajectory]
    simp only [prefixSize, Nat.add_zero, Nat.zero_mul]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate :=
      Function.update_eq_self Work.reference₀ (values inputLength)
    simp only [hreference inputLength] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate :=
      Function.update_eq_self Work.temporary₃ (values inputLength)
    simp only [htemporary inputLength] at htemporaryUpdate
    exact htemporaryUpdate
  have hspace (index : Fin (k + 2)) :
      BinaryRoutine.SpaceBoundByWidthAt
        (emitStepHeadTapeCopies tm (tapeAt index)) initialSpace
        (trajectory index.val) width := by
    apply emitStepHeadTapeCopies_spaceBoundByWidthAt_packed tm (tapeAt index)
      henvelope (htrajectoryHorizon index.val)
      (htrajectoryPosition index.val) (htrajectoryLimit index.val)
    · intro inputLength
      rw [htrajectoryGateCount]
      have hblock : blockSizeAt inputLength index.val =
          (baseValues inputLength Work.horizon + 1) *
            (headNextFormulaPolynomial tm (tapeAt index)).eval
              (baseValues inputLength Work.horizon) := by
        simp [blockSizeAt, headCopyBlockSizeAtPacked, tapeAt, index.isLt]
      rw [← hblock, Nat.add_assoc, ← prefixSize_succ]
      have hprefix := prefixSize_mono (blockSizeAt inputLength)
        (show index.val + 1 ≤ k + 2 by omega)
      rw [headCopyBlockSizeAt_sum_packed] at hprefix
      exact le_trans (Nat.add_le_add_left hprefix _)
        (hgateEnd inputLength)
    · intro inputLength
      rw [htrajectoryAvailable]
      calc
        values inputLength Work.available +
              index.val * (baseValues inputLength Work.horizon + 1) +
            (baseValues inputLength Work.horizon + 1) =
            values inputLength Work.available +
              (index.val + 1) *
                (baseValues inputLength Work.horizon + 1) := by ring
        _ ≤ values inputLength Work.available +
              (k + 2) * (baseValues inputLength Work.horizon + 1) := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right
              (baseValues inputLength Work.horizon + 1)
              (show index.val + 1 ≤ k + 2 by omega)) _
        _ ≤ _ := havailableEnd inputLength
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      simp [trajectory, Work.temporary₃]
  have hstep (index : Fin (k + 2)) (inputLength : ℕ) :
      (emitStepHeadTapeCopies tm (tapeAt index)).effect
          (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength := by
    rw [emitStepHeadTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val inputLength) (htrajectoryPosition _ _)]
    · funext register
      have hblock : blockSizeAt inputLength index.val =
          (baseValues inputLength Work.horizon + 1) *
            nextHeadFormulaScheduleSize (transitionCases tm).length k
              (baseValues inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm (tapeAt index))
              (effectCaseChoiceAt tm) := by
        simp [blockSizeAt, headCopyBlockSizeAtPacked, tapeAt, index.isLt,
          headNextFormulaPolynomial_eval]
      have hhorizonNum : values inputLength (1 : Fin WorkCount) =
          baseValues inputLength (1 : Fin WorkCount) := by
        simpa [Work.horizon] using hhorizonEq inputLength
      by_cases hgate : register = Work.gateCount
      · subst register
        simp [trajectory, prefixSize_succ, hblock, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
        rw [hhorizonNum]
        exact Nat.add_assoc _ _ _
      · by_cases havail : register = Work.available
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃, Work.horizon]
          rw [hhorizonNum]
          ring
        · by_cases hreferenceIndex : register = Work.reference₀
          · subst register
            simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃, Work.horizon]
          · by_cases htemporaryIndex : register = Work.temporary₃
            · subst register
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]
            · have hgateNum : register ≠ (4 : Fin WorkCount) := by
                simpa [Work.gateCount] using hgate
              have havailNum : register ≠ (5 : Fin WorkCount) := by
                simpa [Work.available] using havail
              have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
                simpa [Work.reference₀] using hreferenceIndex
              have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
                simpa [Work.temporary₃] using htemporaryIndex
              simp [trajectory, hgateNum, havailNum, hreferenceNum,
                htemporaryNum, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]
    · rw [htrajectoryLimit, htrajectoryHorizon]
  rw [List.map_ofFn]
  exact seqList_ofFn_spaceBoundByWidthAt_internal (k + 2)
    (fun index => emitStepHeadTapeCopies tm (tapeAt index)) trajectory
    hzero hspace hstep

private theorem emitStepCellTapeCopiesList_seqListSpaceBoundByWidthAt_packed
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hposition : ∀ inputLength, values inputLength Work.position = 0)
    (hlimit : ∀ inputLength,
      values inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 2)
    (hgateEnd : ∀ inputLength,
      values inputLength Work.gateCount +
          stepCellFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (havailableEnd : ∀ inputLength,
      values inputLength Work.available +
          (k + 2) * (4 * (baseValues inputLength Work.horizon + 2)) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon))
    (hreference : ∀ inputLength, values inputLength Work.reference₀ = 0)
    (htemporary : ∀ inputLength, values inputLength Work.temporary₃ = 0) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepCellTapeCopies tm)) initialSpace values width := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let blockSizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    cellCopyBlockSizeAtPacked tm (baseValues inputLength Work.horizon)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount := fun count inputLength =>
    Function.update
      (Function.update
        (Function.update
          (Function.update (values inputLength) Work.gateCount
            (values inputLength Work.gateCount +
              prefixSize (blockSizeAt inputLength) count))
          Work.available
            (values inputLength Work.available +
              count * (4 * (baseValues inputLength Work.horizon + 2))))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count inputLength : ℕ) :
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [show trajectory count inputLength Work.horizon =
        values inputLength Work.horizon by
      simp [trajectory, Work.horizon, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hhorizonEq inputLength
  have htrajectoryPosition (count inputLength : ℕ) :
      trajectory count inputLength Work.position = 0 := by
    rw [show trajectory count inputLength Work.position =
        values inputLength Work.position by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hposition inputLength
  have htrajectoryLimit (count inputLength : ℕ) :
      trajectory count inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 2 := by
    rw [show trajectory count inputLength Work.limit₁ =
        values inputLength Work.limit₁ by
      simp [trajectory, Work.limit₁, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hlimit inputLength
  have htrajectoryGateCount (count inputLength : ℕ) :
      trajectory count inputLength Work.gateCount =
        values inputLength Work.gateCount +
          prefixSize (blockSizeAt inputLength) count := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have htrajectoryAvailable (count inputLength : ℕ) :
      trajectory count inputLength Work.available =
        values inputLength Work.available +
          count * (4 * (baseValues inputLength Work.horizon + 2)) := by
    simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hzero : trajectory 0 = values := by
    funext inputLength
    dsimp only [trajectory]
    simp only [prefixSize, Nat.add_zero, Nat.zero_mul]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate :=
      Function.update_eq_self Work.reference₀ (values inputLength)
    simp only [hreference inputLength] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate :=
      Function.update_eq_self Work.temporary₃ (values inputLength)
    simp only [htemporary inputLength] at htemporaryUpdate
    exact htemporaryUpdate
  have hspace (index : Fin (k + 2)) :
      BinaryRoutine.SpaceBoundByWidthAt
        (emitStepCellTapeCopies tm (tapeAt index)) initialSpace
        (trajectory index.val) width := by
    apply emitStepCellTapeCopies_spaceBoundByWidthAt_packed tm (tapeAt index)
      henvelope (htrajectoryHorizon index.val)
      (htrajectoryPosition index.val) (htrajectoryLimit index.val)
    · intro inputLength
      rw [htrajectoryGateCount]
      have hblock : blockSizeAt inputLength index.val =
          prefixSize
            (stepCellPositionEffectSizeInternal tm (tapeAt index)
              (baseValues inputLength Work.horizon))
            (baseValues inputLength Work.horizon + 2) := by
        simp [blockSizeAt, cellCopyBlockSizeAtPacked, tapeAt, index.isLt]
      rw [← hblock, Nat.add_assoc, ← prefixSize_succ]
      have hprefix := prefixSize_mono (blockSizeAt inputLength)
        (show index.val + 1 ≤ k + 2 by omega)
      rw [cellCopyBlockSizeAt_sum_packed] at hprefix
      exact le_trans (Nat.add_le_add_left hprefix _)
        (hgateEnd inputLength)
    · intro inputLength
      rw [htrajectoryAvailable]
      calc
        values inputLength Work.available +
              index.val *
                (4 * (baseValues inputLength Work.horizon + 2)) +
            4 * (baseValues inputLength Work.horizon + 2) =
            values inputLength Work.available +
              (index.val + 1) *
                (4 * (baseValues inputLength Work.horizon + 2)) := by ring
        _ ≤ values inputLength Work.available +
              (k + 2) *
                (4 * (baseValues inputLength Work.horizon + 2)) := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_right
              (4 * (baseValues inputLength Work.horizon + 2))
              (show index.val + 1 ≤ k + 2 by omega)) _
        _ ≤ _ := havailableEnd inputLength
    · intro inputLength
      simp [trajectory, Work.reference₀, Work.temporary₃]
    · intro inputLength
      simp [trajectory, Work.temporary₃]
  have hstep (index : Fin (k + 2)) (inputLength : ℕ) :
      (emitStepCellTapeCopies tm (tapeAt index)).effect
          (trajectory index.val inputLength) =
        trajectory (index.val + 1) inputLength := by
    rw [emitStepCellTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val inputLength) (htrajectoryPosition _ _)]
    · funext register
      have hblock : blockSizeAt inputLength index.val =
          prefixSize
            (stepCellPositionEffectSizeInternal tm (tapeAt index)
              (baseValues inputLength Work.horizon))
            (baseValues inputLength Work.horizon + 2) := by
        simp [blockSizeAt, cellCopyBlockSizeAtPacked, tapeAt, index.isLt]
      have hhorizonNum : values inputLength (1 : Fin WorkCount) =
          baseValues inputLength (1 : Fin WorkCount) := by
        simpa [Work.horizon] using hhorizonEq inputLength
      by_cases hgate : register = Work.gateCount
      · subst register
        simp [trajectory, prefixSize_succ, hblock, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
        rw [hhorizonNum]
        exact Nat.add_assoc _ _ _
      · by_cases havail : register = Work.available
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃, Work.horizon]
          rw [hhorizonNum]
          ring
        · by_cases hreferenceIndex : register = Work.reference₀
          · subst register
            simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃, Work.horizon]
          · by_cases htemporaryIndex : register = Work.temporary₃
            · subst register
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]
            · have hgateNum : register ≠ (4 : Fin WorkCount) := by
                simpa [Work.gateCount] using hgate
              have havailNum : register ≠ (5 : Fin WorkCount) := by
                simpa [Work.available] using havail
              have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
                simpa [Work.reference₀] using hreferenceIndex
              have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
                simpa [Work.temporary₃] using htemporaryIndex
              simp [trajectory, hgateNum, havailNum, hreferenceNum,
                htemporaryNum, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]
    · rw [htrajectoryLimit, htrajectoryHorizon]
  rw [List.map_ofFn]
  exact seqList_ofFn_spaceBoundByWidthAt_internal (k + 2)
    (fun index => emitStepCellTapeCopies tm (tapeAt index)) trajectory
    hzero hspace hstep

private theorem emitStepHeadTapeCopiesList_effect_packed
    (tm : NTM k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeCopies tm))).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                stepHeadFormulasEffectSizeInternal tm
                  (values Work.horizon)))
            Work.available
              (values Work.available + (k + 2) *
                (values Work.horizon + 1)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let blockSizeAt : ℕ → ℕ :=
    headCopyBlockSizeAtPacked tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update
        (Function.update
          (Function.update values Work.gateCount
            (values Work.gateCount + prefixSize blockSizeAt count))
          Work.available
            (values Work.available + count * (values Work.horizon + 1)))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count : ℕ) :
      trajectory count Work.horizon = values Work.horizon := by
    simp [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  have htrajectoryPosition (count : ℕ) :
      trajectory count Work.position = 0 := by
    rw [show trajectory count Work.position = values Work.position by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hposition
  have htrajectoryLimit (count : ℕ) :
      trajectory count Work.limit₁ = trajectory count Work.horizon + 1 := by
    rw [htrajectoryHorizon]
    rw [show trajectory count Work.limit₁ = values Work.limit₁ by
      simp [trajectory, Work.limit₁, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hlimit
  have hzero : trajectory 0 = values := by
    dsimp only [trajectory]
    simp only [prefixSize, Nat.add_zero, Nat.zero_mul]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate := Function.update_eq_self Work.reference₀ values
    simp only [hreference] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate := Function.update_eq_self Work.temporary₃ values
    simp only [htemporary] at htemporaryUpdate
    exact htemporaryUpdate
  have hstep (index : Fin (k + 2)) :
      (emitStepHeadTapeCopies tm (tapeAt index)).effect
          (trajectory index.val) = trajectory (index.val + 1) := by
    rw [emitStepHeadTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val) (htrajectoryPosition _)
      (htrajectoryLimit _)]
    funext register
    have hblock : blockSizeAt index.val =
        (values Work.horizon + 1) *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm (tapeAt index))
            (effectCaseChoiceAt tm) := by
      simp [blockSizeAt, headCopyBlockSizeAtPacked, tapeAt, index.isLt,
        headNextFormulaPolynomial_eval]
    by_cases hgate : register = Work.gateCount
    · subst register
      simp [trajectory, prefixSize_succ, hblock,
        Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃, Work.horizon]
      exact Nat.add_assoc _ _ _
    · by_cases havail : register = Work.available
      · subst register
        simp [trajectory, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.horizon]
        ring
      · by_cases hreferenceIndex : register = Work.reference₀
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIndex : register = Work.temporary₃
          · subst register
            simp [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · have hgateNum : register ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : register ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using hreferenceIndex
            have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemporaryIndex
            simp [trajectory, hgateNum, havailNum, hreferenceNum,
              htemporaryNum, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.horizon]
  calc
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeCopies tm))).effect values = trajectory (k + 2) := by
        rw [List.map_ofFn]
        exact BinaryRoutine.seqList_ofFn_effect_eq_trajectory (k + 2)
          (fun index => emitStepHeadTapeCopies tm (tapeAt index)) values
          trajectory hzero hstep
    _ = _ := by
      dsimp only [trajectory, blockSizeAt]
      rw [headCopyBlockSizeAt_sum_packed]

private theorem emitStepCellTapeCopiesList_effect_packed
    (tm : NTM k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepCellTapeCopies tm))).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                stepCellFormulasEffectSizeInternal tm
                  (values Work.horizon)))
            Work.available
              (values Work.available + (k + 2) *
                (4 * (values Work.horizon + 2))))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let blockSizeAt : ℕ → ℕ :=
    cellCopyBlockSizeAtPacked tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update
        (Function.update
          (Function.update values Work.gateCount
            (values Work.gateCount + prefixSize blockSizeAt count))
          Work.available
            (values Work.available + count *
              (4 * (values Work.horizon + 2))))
        Work.reference₀ 0) Work.temporary₃ 0
  have htrajectoryHorizon (count : ℕ) :
      trajectory count Work.horizon = values Work.horizon := by
    simp [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  have htrajectoryPosition (count : ℕ) :
      trajectory count Work.position = 0 := by
    rw [show trajectory count Work.position = values Work.position by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hposition
  have htrajectoryLimit (count : ℕ) :
      trajectory count Work.limit₁ = trajectory count Work.horizon + 2 := by
    rw [htrajectoryHorizon]
    rw [show trajectory count Work.limit₁ = values Work.limit₁ by
      simp [trajectory, Work.limit₁, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]]
    exact hlimit
  have hzero : trajectory 0 = values := by
    dsimp only [trajectory]
    simp only [prefixSize, Nat.add_zero, Nat.zero_mul]
    rw [Function.update_eq_self, Function.update_eq_self]
    have hreferenceUpdate := Function.update_eq_self Work.reference₀ values
    simp only [hreference] at hreferenceUpdate
    rw [hreferenceUpdate]
    have htemporaryUpdate := Function.update_eq_self Work.temporary₃ values
    simp only [htemporary] at htemporaryUpdate
    exact htemporaryUpdate
  have hstep (index : Fin (k + 2)) :
      (emitStepCellTapeCopies tm (tapeAt index)).effect
          (trajectory index.val) = trajectory (index.val + 1) := by
    rw [emitStepCellTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val) (htrajectoryPosition _)
      (htrajectoryLimit _)]
    funext register
    have hblock : blockSizeAt index.val =
        prefixSize
          (stepCellPositionEffectSizeInternal tm (tapeAt index)
            (values Work.horizon)) (values Work.horizon + 2) := by
      simp [blockSizeAt, cellCopyBlockSizeAtPacked, tapeAt, index.isLt]
    by_cases hgate : register = Work.gateCount
    · subst register
      simp [trajectory, prefixSize_succ, hblock,
        Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃, Work.horizon]
      exact Nat.add_assoc _ _ _
    · by_cases havail : register = Work.available
      · subst register
        simp [trajectory, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.horizon]
        ring
      · by_cases hreferenceIndex : register = Work.reference₀
        · subst register
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIndex : register = Work.temporary₃
          · subst register
            simp [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · have hgateNum : register ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : register ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hreferenceNum : register ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using hreferenceIndex
            have htemporaryNum : register ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemporaryIndex
            simp [trajectory, hgateNum, havailNum, hreferenceNum,
              htemporaryNum, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.horizon]
  calc
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepCellTapeCopies tm))).effect values = trajectory (k + 2) := by
        rw [List.map_ofFn]
        exact BinaryRoutine.seqList_ofFn_effect_eq_trajectory (k + 2)
          (fun index => emitStepCellTapeCopies tm (tapeAt index)) values
          trajectory hzero hstep
    _ = _ := by
      dsimp only [trajectory, blockSizeAt]
      rw [cellCopyBlockSizeAt_sum_packed]

/-- The delayed packed-copy phase stays within the shared width envelope. -/
theorem emitStepPackedCopies_spaceBoundByWidth_internal (tm : NTM k)
    {initialSpace : ℕ → ℕ} {baseValues values : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (hvalues : ∀ inputLength index,
      values inputLength index ≤ width inputLength)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hhorizonEq : ∀ inputLength,
      values inputLength Work.horizon = baseValues inputLength Work.horizon)
    (hgateCount : ∀ inputLength,
      values inputLength Work.gateCount =
        baseValues inputLength Work.available)
    (havailable : ∀ inputLength,
      values inputLength Work.available =
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepPackedCopies tm)
      initialSpace values width := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let afterState : ℕ → BinaryValues WorkCount := fun inputLength =>
    (emitStepStateCopies tm).effect (values inputLength)
  let afterLimit₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    (setStepPositionLimit 1).effect (afterState inputLength)
  let afterHeads : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList
      (tapes.map (emitStepHeadTapeCopies tm))).effect
        (afterLimit₁ inputLength)
  let afterLimit₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    (setStepPositionLimit 2).effect (afterHeads inputLength)
  let afterCells : ℕ → BinaryValues WorkCount := fun inputLength =>
    (BinaryRoutine.seqList
      (tapes.map (emitStepCellTapeCopies tm))).effect
        (afterLimit₂ inputLength)
  have hreference : ∀ inputLength,
      values inputLength Work.reference₀ = 0 := by
    intro inputLength
    exact (hclean inputLength).caseFormulaClean_forSpace_internal.reference₀
  have htemporary : ∀ inputLength,
      values inputLength Work.temporary₃ = 0 := by
    intro inputLength
    exact (hclean inputLength).caseFormulaClean_forSpace_internal.temporary₃
  have hhorizonNum (inputLength : ℕ) :
      values inputLength (1 : Fin WorkCount) =
        baseValues inputLength (1 : Fin WorkCount) := by
    simpa [Work.horizon] using hhorizonEq inputLength
  have hgateCountNum (inputLength : ℕ) :
      values inputLength (4 : Fin WorkCount) =
        baseValues inputLength (5 : Fin WorkCount) := by
    simpa [Work.gateCount, Work.available] using hgateCount inputLength
  have havailableNum (inputLength : ℕ) :
      values inputLength (5 : Fin WorkCount) =
        baseValues inputLength (5 : Fin WorkCount) +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength (1 : Fin WorkCount)) := by
    simpa [Work.available, Work.horizon] using havailable inputLength
  have hstateEffect (inputLength : ℕ) :
      afterState inputLength =
        Function.update
          (Function.update
            (Function.update
              (Function.update (values inputLength) Work.gateCount
                (values inputLength Work.gateCount +
                  stepStateFormulasEffectSizeInternal tm
                    (values inputLength Work.horizon)))
              Work.available
                (values inputLength Work.available + Fintype.card tm.Q))
            Work.reference₀ 0) Work.temporary₃ 0 := by
    dsimp only [afterState]
    exact emitStepStateCopies_effect_internal tm (values inputLength)
  have hstateSpace : BinaryRoutine.SpaceBoundByWidthAt
      (emitStepStateCopies tm) initialSpace values width :=
    emitStepStateCopies_spaceBoundByWidthAt_packed tm hclean henvelope
      hhorizonEq hgateCount havailable
  have hafterStateValues : ∀ inputLength index,
      afterState inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [hstateEffect]
    by_cases hgate : index = Work.gateCount
    · subst index
      simp [Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃]
      change values inputLength Work.gateCount +
          stepStateFormulasEffectSizeInternal tm
            (values inputLength Work.horizon) ≤ width inputLength
      rw [hgateCount inputLength, hhorizonEq inputLength]
      have hfinal :=
        (henvelope inputLength).finalFrontier_le_internal
      unfold stepFormulasEffectSizeInternal at hfinal
      omega
    · by_cases havail : index = Work.available
      · subst index
        simp [Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
        change values inputLength Work.available + Fintype.card tm.Q ≤
          width inputLength
        rw [havailable inputLength]
        have hfinal :=
          (henvelope inputLength).finalFrontier_le_internal
        unfold stepAtomCount at hfinal
        omega
      · by_cases href : index = Work.reference₀
        · subst index
          simp [Work.reference₀, Work.temporary₃]
        · by_cases htemp : index = Work.temporary₃
          · subst index
            simp [Work.temporary₃]
          · have hgateNum : index ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : index ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hrefNum : index ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using href
            have htempNum : index ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemp
            simpa [hgateNum, havailNum, hrefNum, htempNum,
              Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃] using hvalues inputLength index
  have hlimit₁Result (inputLength : ℕ) :
      afterState inputLength Work.horizon + 1 ≤ width inputLength := by
    rw [hstateEffect]
    simp [Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    change values inputLength Work.horizon < width inputLength
    rw [hhorizonEq inputLength]
    have hbound := (henvelope inputLength).horizon_add_two_le_internal
    omega
  have hlimit₁Space : BinaryRoutine.SpaceBoundByWidthAt
      (setStepPositionLimit 1) initialSpace afterState width :=
    setStepPositionLimit_spaceBoundByWidthAt_internal 1 hafterStateValues
      hlimit₁Result
  have hlimit₁Effect (inputLength : ℕ) :
      afterLimit₁ inputLength =
        Function.update (afterState inputLength) Work.limit₁
          (afterState inputLength Work.horizon + 1) := by
    dsimp only [afterLimit₁]
    exact setStepPositionLimit_effect_local_internal 1
      (afterState inputLength)
  have hafterLimit₁Values : ∀ inputLength index,
      afterLimit₁ inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [hlimit₁Effect]
    exact BinaryRoutine.values_update_le Work.limit₁
      (hafterStateValues inputLength) (hlimit₁Result inputLength) index
  have hheadHorizon (inputLength : ℕ) :
      afterLimit₁ inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [hlimit₁Effect, hstateEffect]
    simpa [Work.limit₁, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃] using hhorizonEq inputLength
  have hheadPosition (inputLength : ℕ) :
      afterLimit₁ inputLength Work.position = 0 := by
    rw [hlimit₁Effect, hstateEffect]
    simpa [Work.limit₁, Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃] using (hclean inputLength).position
  have hheadLimit (inputLength : ℕ) :
      afterLimit₁ inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 1 := by
    rw [hlimit₁Effect]
    simp [Work.limit₁]
    rw [hstateEffect]
    simp [Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    change values inputLength Work.horizon =
      baseValues inputLength Work.horizon
    exact hhorizonEq inputLength
  have hheadLimitLocal (inputLength : ℕ) :
      afterLimit₁ inputLength Work.limit₁ =
        afterLimit₁ inputLength Work.horizon + 1 := by
    rw [hheadLimit, hheadHorizon]
  have hheadGateStart (inputLength : ℕ) :
      afterLimit₁ inputLength Work.gateCount =
        baseValues inputLength Work.available +
          stepStateFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) := by
    rw [hlimit₁Effect, hstateEffect]
    simp [Work.limit₁, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    change values inputLength Work.gateCount +
        stepStateFormulasEffectSizeInternal tm
          (values inputLength Work.horizon) =
      baseValues inputLength Work.available +
        stepStateFormulasEffectSizeInternal tm
          (baseValues inputLength Work.horizon)
    rw [hgateCount inputLength, hhorizonEq inputLength]
  have hheadAvailableStart (inputLength : ℕ) :
      afterLimit₁ inputLength Work.available =
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          Fintype.card tm.Q := by
    rw [hlimit₁Effect, hstateEffect]
    simp [Work.limit₁, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    change values inputLength Work.available =
      baseValues inputLength Work.available +
        stepFormulasEffectSizeInternal tm
          (baseValues inputLength Work.horizon)
    exact havailable inputLength
  have hheadHorizonNum (inputLength : ℕ) :
      afterLimit₁ inputLength (1 : Fin WorkCount) =
        baseValues inputLength (1 : Fin WorkCount) := by
    simpa [Work.horizon] using hheadHorizon inputLength
  have hheadGateStartNum (inputLength : ℕ) :
      afterLimit₁ inputLength (4 : Fin WorkCount) =
        baseValues inputLength (5 : Fin WorkCount) +
          stepStateFormulasEffectSizeInternal tm
            (baseValues inputLength (1 : Fin WorkCount)) := by
    simpa [Work.gateCount, Work.available, Work.horizon] using
      hheadGateStart inputLength
  have hheadAvailableStartNum (inputLength : ℕ) :
      afterLimit₁ inputLength (5 : Fin WorkCount) =
        baseValues inputLength (5 : Fin WorkCount) +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength (1 : Fin WorkCount)) +
          Fintype.card tm.Q := by
    simpa [Work.available, Work.horizon] using
      hheadAvailableStart inputLength
  have hheadGateEnd (inputLength : ℕ) :
      afterLimit₁ inputLength Work.gateCount +
          stepHeadFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) := by
    rw [hheadGateStart]
    unfold stepFormulasEffectSizeInternal
    omega
  have hheadAvailableEnd (inputLength : ℕ) :
      afterLimit₁ inputLength Work.available +
          (k + 2) * (baseValues inputLength Work.horizon + 1) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon) := by
    rw [hheadAvailableStart]
    unfold stepAtomCount
    omega
  have hheadReference (inputLength : ℕ) :
      afterLimit₁ inputLength Work.reference₀ = 0 := by
    rw [hlimit₁Effect, hstateEffect]
    simp [Work.limit₁, Work.reference₀, Work.temporary₃]
  have hheadTemporary (inputLength : ℕ) :
      afterLimit₁ inputLength Work.temporary₃ = 0 := by
    rw [hlimit₁Effect, hstateEffect]
    simp [Work.limit₁, Work.temporary₃]
  have hheadSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (tapes.map (emitStepHeadTapeCopies tm)) initialSpace afterLimit₁
        width := by
    simpa only [tapes] using
      emitStepHeadTapeCopiesList_seqListSpaceBoundByWidthAt_packed tm
        henvelope hheadHorizon hheadPosition hheadLimit hheadGateEnd
        hheadAvailableEnd hheadReference hheadTemporary
  have hheadsEffect (inputLength : ℕ) :
      afterHeads inputLength =
        Function.update
          (Function.update
            (Function.update
              (Function.update (afterLimit₁ inputLength) Work.gateCount
                (afterLimit₁ inputLength Work.gateCount +
                  stepHeadFormulasEffectSizeInternal tm
                    (afterLimit₁ inputLength Work.horizon)))
              Work.available
                (afterLimit₁ inputLength Work.available + (k + 2) *
                  (afterLimit₁ inputLength Work.horizon + 1)))
            Work.reference₀ 0) Work.temporary₃ 0 := by
    dsimp only [afterHeads]
    simpa only [tapes] using
      emitStepHeadTapeCopiesList_effect_packed tm
        (afterLimit₁ inputLength) (hheadPosition inputLength)
        (hheadLimitLocal inputLength) (hheadReference inputLength)
        (hheadTemporary inputLength)
  have hheadsHorizon (inputLength : ℕ) :
      afterHeads inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [hheadsEffect]
    simpa [Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃] using hheadHorizon inputLength
  have hheadsPosition (inputLength : ℕ) :
      afterHeads inputLength Work.position = 0 := by
    rw [hheadsEffect]
    simpa [Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃] using hheadPosition inputLength
  have hheadsReference (inputLength : ℕ) :
      afterHeads inputLength Work.reference₀ = 0 := by
    rw [hheadsEffect]
    simp [Work.reference₀, Work.temporary₃]
  have hheadsTemporary (inputLength : ℕ) :
      afterHeads inputLength Work.temporary₃ = 0 := by
    rw [hheadsEffect]
    simp [Work.temporary₃]
  have hafterHeadsValues : ∀ inputLength index,
      afterHeads inputLength index ≤ width inputLength := by
    intro inputLength index
    rw [hheadsEffect]
    by_cases hgate : index = Work.gateCount
    · subst index
      simp [Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃]
      change afterLimit₁ inputLength Work.gateCount +
          stepHeadFormulasEffectSizeInternal tm
            (afterLimit₁ inputLength Work.horizon) ≤ width inputLength
      rw [hheadHorizon inputLength]
      have hfinal :=
        (henvelope inputLength).finalFrontier_le_internal
      exact le_trans (hheadGateEnd inputLength) (by omega)
    · by_cases havail : index = Work.available
      · subst index
        simp [Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
        rw [hheadHorizon inputLength]
        exact le_trans (hheadAvailableEnd inputLength)
          ((henvelope inputLength).finalFrontier_le_internal)
      · by_cases href : index = Work.reference₀
        · subst index
          simp [Work.reference₀, Work.temporary₃]
        · by_cases htemp : index = Work.temporary₃
          · subst index
            simp [Work.temporary₃]
          · have hgateNum : index ≠ (4 : Fin WorkCount) := by
              simpa [Work.gateCount] using hgate
            have havailNum : index ≠ (5 : Fin WorkCount) := by
              simpa [Work.available] using havail
            have hrefNum : index ≠ (7 : Fin WorkCount) := by
              simpa [Work.reference₀] using href
            have htempNum : index ≠ (25 : Fin WorkCount) := by
              simpa [Work.temporary₃] using htemp
            simpa [hgateNum, havailNum, hrefNum, htempNum,
              Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃] using hafterLimit₁Values inputLength index
  have hlimit₂Result (inputLength : ℕ) :
      afterHeads inputLength Work.horizon + 2 ≤ width inputLength := by
    rw [hheadsHorizon]
    exact (henvelope inputLength).horizon_add_two_le_internal
  have hlimit₂Space : BinaryRoutine.SpaceBoundByWidthAt
      (setStepPositionLimit 2) initialSpace afterHeads width :=
    setStepPositionLimit_spaceBoundByWidthAt_internal 2 hafterHeadsValues
      hlimit₂Result
  have hlimit₂Effect (inputLength : ℕ) :
      afterLimit₂ inputLength =
        Function.update (afterHeads inputLength) Work.limit₁
          (afterHeads inputLength Work.horizon + 2) := by
    dsimp only [afterLimit₂]
    exact setStepPositionLimit_effect_local_internal 2
      (afterHeads inputLength)
  have hcellHorizon (inputLength : ℕ) :
      afterLimit₂ inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    rw [hlimit₂Effect]
    simpa [Work.limit₁, Work.horizon] using hheadsHorizon inputLength
  have hcellPosition (inputLength : ℕ) :
      afterLimit₂ inputLength Work.position = 0 := by
    rw [hlimit₂Effect]
    simpa [Work.limit₁, Work.position] using hheadsPosition inputLength
  have hcellLimit (inputLength : ℕ) :
      afterLimit₂ inputLength Work.limit₁ =
        baseValues inputLength Work.horizon + 2 := by
    rw [hlimit₂Effect]
    simp [Work.limit₁]
    rw [hheadsHorizon]
  have hcellLimitNum (inputLength : ℕ) :
      afterLimit₂ inputLength (17 : Fin WorkCount) =
        baseValues inputLength (1 : Fin WorkCount) + 2 := by
    simpa [Work.limit₁, Work.horizon] using hcellLimit inputLength
  have hcellLimitLocal (inputLength : ℕ) :
      afterLimit₂ inputLength Work.limit₁ =
        afterLimit₂ inputLength Work.horizon + 2 := by
    rw [hcellLimit, hcellHorizon]
  have hcellGateEnd (inputLength : ℕ) :
      afterLimit₂ inputLength Work.gateCount +
          stepCellFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) := by
    rw [hlimit₂Effect]
    simp [Work.limit₁, Work.gateCount]
    rw [hheadsEffect]
    simp [Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    rw [hheadGateStartNum, hheadHorizon]
    change baseValues inputLength Work.available +
          stepStateFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) +
        stepHeadFormulasEffectSizeInternal tm
          (baseValues inputLength Work.horizon) +
        stepCellFormulasEffectSizeInternal tm
          (baseValues inputLength Work.horizon) ≤
      baseValues inputLength Work.available +
        stepFormulasEffectSizeInternal tm
          (baseValues inputLength Work.horizon)
    unfold stepFormulasEffectSizeInternal
    omega
  have hcellAvailableEnd (inputLength : ℕ) :
      afterLimit₂ inputLength Work.available +
          (k + 2) * (4 * (baseValues inputLength Work.horizon + 2)) ≤
        baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon) := by
    rw [hlimit₂Effect]
    simp [Work.limit₁, Work.available]
    rw [hheadsEffect]
    simp [Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    rw [hheadAvailableStartNum, hheadHorizon]
    change baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) +
          Fintype.card tm.Q +
          (k + 2) * (baseValues inputLength Work.horizon + 1) +
        (k + 2) * (4 * (baseValues inputLength Work.horizon + 2)) ≤
      baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon) +
        stepAtomCount (Fintype.card tm.Q) k
          (baseValues inputLength Work.horizon)
    unfold stepAtomCount
    ring_nf
    exact le_rfl
  have hcellReference (inputLength : ℕ) :
      afterLimit₂ inputLength Work.reference₀ = 0 := by
    rw [hlimit₂Effect]
    simpa [Work.limit₁, Work.reference₀] using hheadsReference inputLength
  have hcellTemporary (inputLength : ℕ) :
      afterLimit₂ inputLength Work.temporary₃ = 0 := by
    rw [hlimit₂Effect]
    simpa [Work.limit₁, Work.temporary₃] using hheadsTemporary inputLength
  have hcellSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (tapes.map (emitStepCellTapeCopies tm)) initialSpace afterLimit₂
        width := by
    simpa only [tapes] using
      emitStepCellTapeCopiesList_seqListSpaceBoundByWidthAt_packed tm
        henvelope hcellHorizon hcellPosition hcellLimit hcellGateEnd
        hcellAvailableEnd hcellReference hcellTemporary
  have hcellsEffect (inputLength : ℕ) :
      afterCells inputLength =
        Function.update
          (Function.update
            (Function.update
              (Function.update (afterLimit₂ inputLength) Work.gateCount
                (afterLimit₂ inputLength Work.gateCount +
                  stepCellFormulasEffectSizeInternal tm
                    (afterLimit₂ inputLength Work.horizon)))
              Work.available
                (afterLimit₂ inputLength Work.available + (k + 2) *
                  (4 * (afterLimit₂ inputLength Work.horizon + 2))))
            Work.reference₀ 0) Work.temporary₃ 0 := by
    dsimp only [afterCells]
    simpa only [tapes] using
      emitStepCellTapeCopiesList_effect_packed tm
        (afterLimit₂ inputLength) (hcellPosition inputLength)
        (hcellLimitLocal inputLength) (hcellReference inputLength)
        (hcellTemporary inputLength)
  have hafterCellsLimit (inputLength : ℕ) :
      afterCells inputLength Work.limit₁ ≤ width inputLength := by
    rw [hcellsEffect]
    simp [Work.limit₁, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
    rw [hcellLimitNum]
    exact (henvelope inputLength).horizon_add_two_le_internal
  have hclearSpace : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.limit₁) initialSpace afterCells width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₁ hafterCellsLimit
  have hfirstTwo : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [emitStepStateCopies tm, setStepPositionLimit 1]
        initialSpace values width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    refine ⟨hstateSpace, ?_⟩
    change BinaryRoutine.SpaceBoundByWidthAt (setStepPositionLimit 1)
        initialSpace afterState width ∧ True
    exact ⟨hlimit₁Space, trivial⟩
  have hfirstTwoEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          [emitStepStateCopies tm, setStepPositionLimit 1]).effect
            (values inputLength)) = afterLimit₁ := by
    funext inputLength
    simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
      BinaryRoutine.emitBits, afterLimit₁, afterState]
  have hthroughHeads : BinaryRoutine.SeqListSpaceBoundByWidthAt
      ([emitStepStateCopies tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeCopies tm)) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      [emitStepStateCopies tm, setStepPositionLimit 1]
      (tapes.map (emitStepHeadTapeCopies tm)) hfirstTwo (by
        simpa only [hfirstTwoEffect] using hheadSeq)
  have hthroughHeadsEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          ([emitStepStateCopies tm, setStepPositionLimit 1] ++
            tapes.map (emitStepHeadTapeCopies tm))).effect
              (values inputLength)) = afterHeads := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      [emitStepStateCopies tm, setStepPositionLimit 1]).effect
        (values inputLength) = afterLimit₁ inputLength by
          exact congrFun hfirstTwoEffect inputLength]
  have hlimit₂Seq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [setStepPositionLimit 2] initialSpace afterHeads width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    exact ⟨hlimit₂Space, trivial⟩
  have hthroughLimit₂ : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2]) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      ([emitStepStateCopies tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeCopies tm))
      [setStepPositionLimit 2] hthroughHeads (by
        simpa only [hthroughHeadsEffect] using hlimit₂Seq)
  have hthroughLimit₂Effect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          (([emitStepStateCopies tm, setStepPositionLimit 1] ++
              tapes.map (emitStepHeadTapeCopies tm)) ++
            [setStepPositionLimit 2])).effect (values inputLength)) =
        afterLimit₂ := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      ([emitStepStateCopies tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeCopies tm))).effect
          (values inputLength) = afterHeads inputLength by
            exact congrFun hthroughHeadsEffect inputLength]
    simp [BinaryRoutine.seqList, BinaryRoutine.seq, BinaryRoutine.identity,
      BinaryRoutine.emitBits, afterLimit₂]
  have hthroughCells : BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeCopies tm)) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      (([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2])
      (tapes.map (emitStepCellTapeCopies tm)) hthroughLimit₂ (by
        simpa only [hthroughLimit₂Effect] using hcellSeq)
  have hthroughCellsEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          ((([emitStepStateCopies tm, setStepPositionLimit 1] ++
              tapes.map (emitStepHeadTapeCopies tm)) ++
            [setStepPositionLimit 2]) ++
            tapes.map (emitStepCellTapeCopies tm))).effect
              (values inputLength)) = afterCells := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      (([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2])).effect (values inputLength) =
          afterLimit₂ inputLength by
            exact congrFun hthroughLimit₂Effect inputLength]
  have hclearSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [BinaryRoutine.clear Work.limit₁] initialSpace afterCells width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    exact ⟨hclearSpace, trivial⟩
  have htotal : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (((([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeCopies tm)) ++
        [BinaryRoutine.clear Work.limit₁]) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      ((([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeCopies tm))
      [BinaryRoutine.clear Work.limit₁] hthroughCells (by
        simpa only [hthroughCellsEffect] using hclearSeq)
  unfold emitStepPackedCopies
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simpa only [tapes, List.append_assoc] using htotal

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
