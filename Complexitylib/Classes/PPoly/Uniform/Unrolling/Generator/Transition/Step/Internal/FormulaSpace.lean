/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Space.Common

/-!
# Formula-phase space bound for one direct transition step

This module follows the exact state, head, and cell formula trajectories and
certifies every nested routine against the shared packed-step width envelope.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem emitStepStateFormulas_spaceBoundByWidthAt_formula
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (values inputLength) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepStateFormulas tm)
      initialSpace values width := by
  let sizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    stepFormulaSizeAtSpecializedInternal tm
      (values inputLength Work.horizon)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount :=
    fun count inputLength =>
      Function.update (values inputLength) Work.available
        (values inputLength Work.available +
          prefixSize (sizeAt inputLength) count)
  unfold emitStepStateFormulas
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  apply seqList_ofFn_spaceBoundByWidthAt_internal
      (Fintype.card tm.Q)
      (fun index => emitNextStateFormula tm
        ((Fintype.equivFin tm.Q).symm index)) trajectory
  · funext inputLength index
    simp [trajectory]
  · intro index
    apply emitNextStateFormula_spaceBoundByWidth
    · intro inputLength
      have hphase := update_available_preserves_phaseClean_forSpace_internal
        (hclean inputLength).phaseClean_forSpace_internal
        (values inputLength Work.available +
          prefixSize (sizeAt inputLength) index.val)
      simpa [trajectory] using hphase.caseFormulaClean_forSpace_internal
    · intro inputLength current
      have hfrontier :=
        (henvelope inputLength).formulaFrontier_le_internal
      rw [stepFormulasEffectSize_eq_prefixSize_internal] at hfrontier
      have hprefix := prefixSize_mono (sizeAt inputLength)
        (show index.val ≤ stepAtomCount (Fintype.card tm.Q) k
          (values inputLength Work.horizon) by
            unfold stepAtomCount
            omega)
      simp only [sizeAt] at hprefix
      by_cases hcurrent : current = Work.available
      · subst current
        simp [trajectory, sizeAt]
        omega
      · simpa [trajectory, hcurrent] using
          (henvelope inputLength).values_le current
    · intro inputLength stateIndex tapeIndex symbolIndex position
        hstate htape hsymbol hposition
      have hposition' : position ≤ values inputLength Work.horizon := by
        simpa [trajectory, Work.available, Work.horizon] using hposition
      have hcap := (henvelope inputLength).cap
        ((Fintype.equivFin tm.Q).symm index) .input .output .zero
        stateIndex tapeIndex symbolIndex position hstate htape hsymbol
        (by omega)
      rw [stepScheduleSize_eq_formulas_add_atoms_internal,
        stepFormulasEffectSize_eq_prefixSize_internal] at hcap
      have hsize := stepFormulaSizeAtSpecialized_state_forSpace_internal tm
        (values inputLength Work.horizon) index
      have hprefix := prefixSize_mono (sizeAt inputLength)
        (show index.val + 1 ≤ stepAtomCount (Fintype.card tm.Q) k
          (values inputLength Work.horizon) by
            unfold stepAtomCount
            omega)
      rw [prefixSize_succ] at hprefix
      change prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon)) index.val +
          stepFormulaSizeAtSpecializedInternal tm
            (values inputLength Work.horizon) index.val ≤
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon))
          (stepAtomCount (Fintype.card tm.Q) k
            (values inputLength Work.horizon)) at hprefix
      rw [hsize] at hprefix
      have havailable : trajectory index.val inputLength Work.available =
          values inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (values inputLength Work.horizon)) index.val := by
        simp [trajectory, sizeAt, Work.available]
      have hhorizon : trajectory index.val inputLength Work.horizon =
          values inputLength Work.horizon := by
        simp [trajectory, Work.available, Work.horizon]
      have hconfigBase : trajectory index.val inputLength Work.configBase =
          values inputLength Work.configBase := by
        simp [trajectory, Work.available, Work.configBase]
      rw [havailable, hhorizon, hconfigBase]
      omega
  · intro index inputLength
    have hphase := update_available_preserves_phaseClean_forSpace_internal
      (hclean inputLength).phaseClean_forSpace_internal
      (values inputLength Work.available +
        prefixSize (sizeAt inputLength) index.val)
    rw [emitNextStateFormula_effect tm
      ((Fintype.equivFin tm.Q).symm index) (trajectory index.val inputLength)
      (by simpa [trajectory] using
        hphase.caseFormulaClean_forSpace_internal)]
    have hsize := stepFormulaSizeAtSpecialized_state_forSpace_internal tm
      (values inputLength Work.horizon) index
    have hhorizon : trajectory index.val inputLength Work.horizon =
        values inputLength Work.horizon := by
      simp [trajectory, Work.available, Work.horizon]
    rw [hhorizon]
    funext current
    by_cases hcurrent : current = Work.available
    · subst current
      simp [trajectory, sizeAt, prefixSize_succ, hsize]
      omega
    · simp [trajectory, hcurrent]

private theorem emitStepHeadTapeFormulas_spaceBoundByWidthAt_formula
    (tm : NTM k) (tape : TapeSlot k) (start : ℕ → ℕ)
    {initialSpace : ℕ → ℕ}
    {baseValues : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (baseValues inputLength))
    (hhorizon : ∀ inputLength,
      0 < baseValues inputLength Work.horizon)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hblock : ∀ inputLength,
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength) +
          (baseValues inputLength Work.horizon + 1) *
            nextHeadFormulaScheduleSize (transitionCases tm).length k
              (baseValues inputLength Work.horizon)
              (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) =
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon))
          (start inputLength + baseValues inputLength Work.horizon + 1))
    (hend : ∀ inputLength,
      start inputLength + baseValues inputLength Work.horizon + 1 ≤
        stepAtomCount (Fintype.card tm.Q) k
          (baseValues inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepHeadTapeFormulas tm tape)
      initialSpace
      (fun inputLength =>
        Function.update
          (Function.update (baseValues inputLength) Work.limit₁
            (baseValues inputLength Work.horizon + 1))
          Work.available
          (baseValues inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (baseValues inputLength Work.horizon)) (start inputLength)))
      width := by
  let entry : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (baseValues inputLength) Work.limit₁
        (baseValues inputLength Work.horizon + 1))
      Work.available
      (baseValues inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength))
  let body := emitNextHeadFormula tm tape
  have hentryPhase : ∀ inputLength,
      StepPhaseCleanInternal (entry inputLength) := by
    intro inputLength
    have hlimit := update_limit₁_preserves_phaseClean_internal
      (hclean inputLength).phaseClean_forSpace_internal
      (baseValues inputLength Work.horizon + 1)
    simpa [entry] using update_available_preserves_phaseClean_forSpace_internal
      hlimit
      (baseValues inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength))
  have hentryHorizon : ∀ inputLength,
      entry inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    intro inputLength
    simp [entry, Work.available, Work.limit₁, Work.horizon]
  have hentryLimit : ∀ inputLength,
      entry inputLength Work.limit₁ =
        entry inputLength Work.horizon + 1 := by
    intro inputLength
    simp [entry, Work.available, Work.limit₁, Work.horizon]
  have hentryValues : ∀ inputLength index,
      entry inputLength index ≤ width inputLength := by
    intro inputLength index
    have hfrontier :=
      (henvelope inputLength).formulaFrontier_le_internal
    rw [stepFormulasEffectSize_eq_prefixSize_internal] at hfrontier
    have hprefix := prefixSize_mono
      (stepFormulaSizeAtSpecializedInternal tm
        (baseValues inputLength Work.horizon))
      (show start inputLength ≤
          stepAtomCount (Fintype.card tm.Q) k
            (baseValues inputLength Work.horizon) by
        have := hend inputLength
        omega)
    by_cases hindex : index = Work.available
    · subst index
      change entry inputLength Work.available ≤ width inputLength
      rw [show entry inputLength Work.available =
          baseValues inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (baseValues inputLength Work.horizon)) (start inputLength) by
        simp [entry, Work.available, Work.limit₁]]
      omega
    · by_cases hlimit : index = Work.limit₁
      · subst index
        change entry inputLength Work.limit₁ ≤ width inputLength
        rw [hentryLimit inputLength, hentryHorizon inputLength]
        have hwidth :=
          (henvelope inputLength).horizon_add_two_le_internal
        omega
      · simpa [entry, hindex, hlimit] using
          (henvelope inputLength).values_le index
  have hloop : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor body Work.position Work.limit₁)
      initialSpace entry width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    · intro inputLength
      exact hentryValues inputLength Work.limit₁
    · intro inputLength count hcount
      have hcount' : count ≤ baseValues inputLength Work.horizon := by
        rw [BinaryRoutine.binaryForCount, hentryLimit inputLength] at hcount
        have hposition := (hentryPhase inputLength).position
        rw [hposition, Nat.sub_zero, hentryHorizon inputLength] at hcount
        omega
      have htrajectory := headFormula_binaryForValues_effect_forSpace_internal
        tm tape (entry inputLength) (hentryPhase inputLength)
        (by simpa [hentryHorizon inputLength] using hhorizon inputLength)
        count (by rw [hentryHorizon inputLength]; omega)
      rw [htrajectory]
      simp [Work.position, Work.available]
      have hwidth := (henvelope inputLength).horizon_add_two_le_internal
      omega
    · let bodyValues := BinaryRoutine.binaryForClampedValues body
        Work.position Work.limit₁ entry
      let inputAt : ℕ → ℕ := fun code => (Nat.unpair code).1
      let countAt : ℕ → ℕ := fun code =>
        min (Nat.unpair code).2
          (BinaryRoutine.binaryForCount Work.position Work.limit₁
            (entry (inputAt code)) - 1)
      have hcountAt : ∀ code,
          countAt code ≤ baseValues (inputAt code) Work.horizon := by
        intro code
        have hposition := (hentryPhase (inputAt code)).position
        have hlimit := hentryLimit (inputAt code)
        dsimp only [countAt]
        rw [BinaryRoutine.binaryForCount, hlimit, hposition, Nat.sub_zero,
          hentryHorizon (inputAt code)]
        simp
      have htrajectory : ∀ code,
          bodyValues code =
            Function.update
              (Function.update (entry (inputAt code)) Work.position
                (countAt code))
              Work.available
              (entry (inputAt code) Work.available +
                countAt code *
                  nextHeadFormulaScheduleSize
                    (transitionCases tm).length k
                    (entry (inputAt code) Work.horizon)
                    (movedHeadCaseSelectedAt tm tape)
                    (effectCaseChoiceAt tm)) := by
        intro code
        unfold bodyValues BinaryRoutine.binaryForClampedValues
        change BinaryRoutine.binaryForValues body Work.position
            (entry (inputAt code)) (countAt code) = _
        exact headFormula_binaryForValues_effect_forSpace_internal tm tape
          (entry (inputAt code)) (hentryPhase (inputAt code))
          (by simpa [hentryHorizon (inputAt code)] using
            hhorizon (inputAt code)) (countAt code) (by
              rw [hentryHorizon (inputAt code)]
              exact Nat.le_add_right_of_le (hcountAt code))
      apply emitNextHeadFormula_spaceBoundByWidth
      · intro code
        change MovedHeadFormulaClean (bodyValues code)
        rw [htrajectory code]
        have hmoved := (hentryPhase (inputAt code))
          |>.movedHeadClean_atPosition_forSpace_internal (countAt code)
          |>.updateAvailable_emitted_internal
            (entry (inputAt code) Work.available + countAt code *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (entry (inputAt code) Work.horizon)
                (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm))
        exact hmoved
      · intro code
        change 0 < bodyValues code Work.horizon
        rw [htrajectory code]
        simpa [Work.position, Work.available, Work.horizon,
          hentryHorizon (inputAt code)] using! hhorizon (inputAt code)
      · intro code
        change bodyValues code Work.position ≤ bodyValues code Work.horizon
        rw [htrajectory code]
        simp [Work.position, Work.available, Work.horizon]
        simpa [Work.horizon, hentryHorizon (inputAt code)] using! hcountAt code
      · intro code index
        change bodyValues code index ≤ width (inputAt code)
        rw [htrajectory code]
        let inputLength := inputAt code
        let count := countAt code
        let scheduleSize := nextHeadFormulaScheduleSize
          (transitionCases tm).length k
          (baseValues inputLength Work.horizon)
          (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        have hfrontier :=
          (henvelope inputLength).formulaFrontier_le_internal
        rw [stepFormulasEffectSize_eq_prefixSize_internal] at hfrontier
        have hprefix := prefixSize_mono
          (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon)) (hend inputLength)
        have havailable :
            entry inputLength Work.available + count * scheduleSize ≤
              baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (start inputLength +
                    baseValues inputLength Work.horizon + 1) := by
          have := hcountAt code
          have hmul : countAt code * scheduleSize ≤
              (baseValues (inputAt code) Work.horizon + 1) * scheduleSize :=
            Nat.mul_le_mul_right scheduleSize (by omega)
          dsimp only [count, inputLength] at *
          calc
            entry (inputAt code) Work.available +
                countAt code * scheduleSize =
              baseValues (inputAt code) Work.available +
                  prefixSize (stepFormulaSizeAtSpecializedInternal tm
                    (baseValues (inputAt code) Work.horizon))
                    (start (inputAt code)) +
                countAt code * scheduleSize := by
                  simp [entry, Work.available, Work.limit₁]
            _ ≤ baseValues (inputAt code) Work.available +
                (prefixSize (stepFormulaSizeAtSpecializedInternal tm
                    (baseValues (inputAt code) Work.horizon))
                    (start (inputAt code)) +
                  (baseValues (inputAt code) Work.horizon + 1) *
                    scheduleSize) := by omega
            _ = baseValues (inputAt code) Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues (inputAt code) Work.horizon))
                  (start (inputAt code) +
                    baseValues (inputAt code) Work.horizon + 1) := by
              rw [hblock (inputAt code)]
        by_cases hindex : index = Work.available
        · subst index
          simp [Work.available, Work.position]
          exact le_trans havailable (le_trans (Nat.add_le_add_left hprefix _)
            hfrontier)
        · by_cases hposition : index = Work.position
          · subst index
            simp [Work.available, Work.position]
            exact le_trans (hcountAt code)
              (le_trans (Nat.le_add_right _ 2)
                (henvelope (inputAt code)).horizon_add_two_le_internal)
          · simp [hindex, hposition]
            exact hentryValues (inputAt code) index
      · intro code stateIndex tapeIndex symbolIndex position hstate htape
          hsymbol hposition
        change bodyValues code Work.available +
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (bodyValues code Work.horizon)
                (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) +
            transitionStateRef (bodyValues code Work.configBase) stateIndex +
          (transitionHeadRef (Fintype.card tm.Q)
                (bodyValues code Work.horizon)
                (bodyValues code Work.configBase) tapeIndex position +
              tapeIndex + bodyValues code Work.horizon + 1) +
          (transitionCellRef (Fintype.card tm.Q) (k + 2)
                (bodyValues code Work.horizon)
                (bodyValues code Work.configBase) tapeIndex position
                symbolIndex +
              (tapeIndex * (bodyValues code Work.horizon + 2) + position) +
              (bodyValues code Work.horizon + 2) + (k + 2) + tapeIndex + 4) +
          caseReadSize (bodyValues code Work.horizon) +
          2 * TM.binaryPolynomialValueCap predecessorHeadSchedulePolynomial
            (bodyValues code Work.horizon) +
          2 * (bodyValues code Work.horizon + 2) +
          bodyValues code Work.horizon +
          2 * TM.binaryPolynomialValueCap
            (headNextChildPolynomial tm tape)
            (bodyValues code Work.horizon) ≤ width (inputAt code)
        rw [htrajectory code]
        let inputLength := inputAt code
        let count := countAt code
        let scheduleSize := nextHeadFormulaScheduleSize
          (transitionCases tm).length k
          (baseValues inputLength Work.horizon)
          (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        change position ≤ bodyValues code Work.horizon + 1 at hposition
        have hposition' : position ≤
            baseValues inputLength Work.horizon + 1 := by
          rw [htrajectory code] at hposition
          simp [Work.position, Work.available, Work.horizon] at hposition
          simpa [inputLength, Work.horizon,
            hentryHorizon (inputAt code)] using! hposition
        have hcap := (henvelope inputLength).cap tm.qstart tape .output .zero
          stateIndex tapeIndex symbolIndex position hstate htape hsymbol
          hposition'
        rw [stepScheduleSize_eq_formulas_add_atoms_internal,
          stepFormulasEffectSize_eq_prefixSize_internal] at hcap
        have hprefix := prefixSize_mono
          (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon)) (hend inputLength)
        have havailable :
            entry inputLength Work.available + count * scheduleSize +
                scheduleSize ≤
              baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (start inputLength +
                    baseValues inputLength Work.horizon + 1) := by
          have := hcountAt code
          have hmul : countAt code * scheduleSize + scheduleSize ≤
              (baseValues (inputAt code) Work.horizon + 1) * scheduleSize := by
            have hcountSucc : countAt code + 1 ≤
                baseValues (inputAt code) Work.horizon + 1 := by omega
            simpa [Nat.add_mul] using
              Nat.mul_le_mul_right scheduleSize hcountSucc
          dsimp only [count, inputLength] at *
          calc
            entry (inputAt code) Work.available +
                  countAt code * scheduleSize + scheduleSize =
              baseValues (inputAt code) Work.available +
                    prefixSize (stepFormulaSizeAtSpecializedInternal tm
                      (baseValues (inputAt code) Work.horizon))
                      (start (inputAt code)) +
                  countAt code * scheduleSize + scheduleSize := by
                    simp [entry, Work.available, Work.limit₁]
            _ ≤ baseValues (inputAt code) Work.available +
                (prefixSize (stepFormulaSizeAtSpecializedInternal tm
                    (baseValues (inputAt code) Work.horizon))
                    (start (inputAt code)) +
                  (baseValues (inputAt code) Work.horizon + 1) *
                    scheduleSize) := by omega
            _ = baseValues (inputAt code) Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues (inputAt code) Work.horizon))
                  (start (inputAt code) +
                    baseValues (inputAt code) Work.horizon + 1) := by
              rw [hblock (inputAt code)]
        have hlocalFrontier := le_trans havailable
          (Nat.add_le_add_left hprefix (baseValues inputLength Work.available))
        simp only [Function.update_apply]
        simp [entry, Work.available, Work.position, Work.horizon,
          Work.limit₁, Work.configBase]
        dsimp only [inputLength, count, scheduleSize] at hcap hlocalFrontier ⊢
        simp only [Work.available, Work.horizon, Work.configBase] at hcap
        simp [entry, Work.available, Work.limit₁, Work.horizon] at hlocalFrontier
        omega
  unfold emitStepHeadTapeFormulas
  change BinaryRoutine.SpaceBoundByWidthAt
    (BinaryRoutine.seq
      (BinaryRoutine.binaryFor body Work.position Work.limit₁)
      (BinaryRoutine.clear Work.position)) initialSpace entry width
  apply BinaryRoutine.SpaceBoundByWidthAt.seq hloop
  apply BinaryRoutine.SpaceBoundByWidthAt.clear
  intro inputLength
  change BinaryRoutine.binaryForValues body Work.position (entry inputLength)
      (BinaryRoutine.binaryForCount Work.position Work.limit₁
        (entry inputLength)) Work.position ≤ width inputLength
  have htotal :
      BinaryRoutine.binaryForCount Work.position Work.limit₁
          (entry inputLength) = entry inputLength Work.horizon + 1 := by
    rw [BinaryRoutine.binaryForCount, hentryLimit inputLength,
      (hentryPhase inputLength).position, Nat.sub_zero]
  have htrajectory := headFormula_binaryForValues_effect_forSpace_internal
    tm tape (entry inputLength) (hentryPhase inputLength)
    (by simpa [hentryHorizon inputLength] using hhorizon inputLength)
    (BinaryRoutine.binaryForCount Work.position Work.limit₁
      (entry inputLength)) (by rw [htotal])
  rw [htrajectory]
  simp [Work.position, Work.available]
  have htotal' : BinaryRoutine.binaryForCount 30 Work.limit₁
      (entry inputLength) = entry inputLength Work.horizon + 1 := by
    simpa [Work.position] using htotal
  rw [htotal']
  rw [← hentryLimit inputLength]
  exact hentryValues inputLength Work.limit₁

private noncomputable def stepCellSymbolSizeFormula (tm : NTM k)
    (tape : TapeSlot k) (T position index : ℕ) : ℕ :=
  if hindex : index < 4 then
    match tape with
    | .input => 1
    | .work workIndex =>
        if position = 0 then 1 else
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
            (writtenCellEffectSelectedAt tm (.work workIndex)
              (symbolEquiv.symm ⟨index, hindex⟩))
            (effectCaseChoiceAt tm)
    | .output =>
        if position = 0 then 1 else
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
            (writtenCellEffectSelectedAt tm .output
              (symbolEquiv.symm ⟨index, hindex⟩))
            (effectCaseChoiceAt tm)
  else 0

private theorem stepCellSymbolSizeFormula_prefix_four (tm : NTM k)
    (tape : TapeSlot k) (T position : ℕ) :
    prefixSize (stepCellSymbolSizeFormula tm tape T position) 4 =
      stepCellPositionEffectSizeInternal tm tape T position := by
  rw [prefixSize_eq_sum_ofFn]
  cases tape <;> simp [stepCellSymbolSizeFormula,
    stepCellPositionEffectSizeInternal]

private theorem MovedHeadFormulaClean.copyScratch_formula
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.tapeIndex = 0 ∧ values Work.symbolIndex = 0 ∧
      values Work.temporary₀ = 0 ∧ values Work.temporary₁ = 0 ∧
      values Work.temporary₂ = 0 ∧ values Work.reference₀ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.position, Work.tapeIndex] using hclean.caseClean.tapeIndex
  · simpa [Work.position, Work.symbolIndex] using hclean.caseClean.symbolIndex
  · simpa [Work.position, Work.temporary₀] using hclean.caseClean.temporary₀
  · simpa [Work.position, Work.temporary₁] using hclean.caseClean.temporary₁
  · simpa [Work.position, Work.temporary₂] using hclean.caseClean.temporary₂
  · simpa [Work.position, Work.reference₀] using hclean.caseClean.reference₀

private theorem MovedHeadFormulaClean.writtenCellClean_formula
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    WrittenCellFormulaClean values :=
  { caseClean := hclean.caseClean
    limit₂ := hclean.limit₂
    savedOutput := hclean.savedOutput }

private theorem emitStepCellPosition_spaceBoundByWidthAt_formula
    (tm : NTM k) (tape : TapeSlot k) {initialSpace : ℕ → ℕ}
    {baseValues current : ℕ → BinaryValues WorkCount}
    {width : ℕ → ℕ}
    (hclean : ∀ inputLength, MovedHeadFormulaClean (current inputLength))
    (hhorizon : ∀ inputLength,
      current inputLength Work.horizon =
        baseValues inputLength Work.horizon)
    (hconfigBase : ∀ inputLength,
      current inputLength Work.configBase =
        baseValues inputLength Work.configBase)
    (hposition : ∀ inputLength,
      current inputLength Work.position ≤
        baseValues inputLength Work.horizon + 1)
    (hvalues : ∀ inputLength index,
      current inputLength index ≤ width inputLength)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hend : ∀ inputLength,
      current inputLength Work.available +
          stepCellPositionEffectSizeInternal tm tape
            (baseValues inputLength Work.horizon)
            (current inputLength Work.position) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon))
    (hwritten : ∀ inputLength (index : Fin 4)
        (writable : WritableSlot k), tape = writable.toTapeSlot →
      current inputLength Work.available +
          prefixSize (stepCellSymbolSizeFormula tm tape
            (baseValues inputLength Work.horizon)
            (current inputLength Work.position)) index.val +
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k
            (baseValues inputLength Work.horizon)
            (writtenCellEffectSelectedAt tm writable
              (symbolEquiv.symm index)) (effectCaseChoiceAt tm) ≤
        baseValues inputLength Work.available +
          stepFormulasEffectSizeInternal tm
            (baseValues inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt
      (match tape with
        | .input => emitStepImmutableCellPosition tm .input
        | .work index => emitStepWritableCellPosition tm (.work index)
        | .output => emitStepWritableCellPosition tm .output)
      initialSpace current width := by
  let routineAt : Fin 4 → BinaryRoutine WorkCount := fun index =>
    let symbol := symbolEquiv.symm index
    match tape with
    | .input =>
        emitNextCellCopy (Fintype.card tm.Q) (k + 2)
          (TapeSlot.input : TapeSlot k).index
          (CircuitUnrolling.symbolIndex symbol)
    | .work workIndex =>
        BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            (TapeSlot.work workIndex).index
            (CircuitUnrolling.symbolIndex symbol))
          (emitNextWrittenCellFormula tm (.work workIndex) symbol)
    | .output =>
        BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            (TapeSlot.output : TapeSlot k).index
            (CircuitUnrolling.symbolIndex symbol))
          (emitNextWrittenCellFormula tm .output symbol)
  let sizeAt : ℕ → ℕ → ℕ := fun inputLength =>
    stepCellSymbolSizeFormula tm tape
      (baseValues inputLength Work.horizon)
      (current inputLength Work.position)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount :=
    fun count inputLength =>
      Function.update (current inputLength) Work.available
        (current inputLength Work.available +
          prefixSize (sizeAt inputLength) count)
  have htrajectoryClean : ∀ count inputLength,
      MovedHeadFormulaClean (trajectory count inputLength) := by
    intro count inputLength
    simpa [trajectory] using (hclean inputLength).updateAvailable_emitted_internal
      (current inputLength Work.available +
        prefixSize (sizeAt inputLength) count)
  have htrajectoryValues : ∀ (index : Fin 4) inputLength currentIndex,
      trajectory index.val inputLength currentIndex ≤ width inputLength := by
    intro index inputLength currentIndex
    have hprefix := prefixSize_mono (sizeAt inputLength)
      (show index.val ≤ 4 by omega)
    rw [stepCellSymbolSizeFormula_prefix_four tm tape
      (baseValues inputLength Work.horizon)
      (current inputLength Work.position)] at hprefix
    have hfrontier :=
      (henvelope inputLength).formulaFrontier_le_internal
    have havailable := le_trans (Nat.add_le_add_left hprefix _)
      (le_trans (hend inputLength) hfrontier)
    by_cases hindex : currentIndex = Work.available
    · subst currentIndex
      simpa [trajectory, sizeAt, Work.available] using havailable
    · simpa [trajectory, hindex] using hvalues inputLength currentIndex
  have hcopyCap : ∀ (index : Fin 4) inputLength,
      transitionCellRef (Fintype.card tm.Q) (k + 2)
            (trajectory index.val inputLength Work.horizon)
            (trajectory index.val inputLength Work.configBase) tape.index
            (trajectory index.val inputLength Work.position)
            (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)) +
          (tape.index * (trajectory index.val inputLength Work.horizon + 2) +
            trajectory index.val inputLength Work.position) +
          (trajectory index.val inputLength Work.horizon + 2) + (k + 2) +
          tape.index + 4 ≤ width inputLength := by
    intro index inputLength
    have htape : tape.index.val ≤ k + 1 := by
      have := tape.index.isLt
      omega
    have hsymbol :=
      (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)).isLt
    have hcap := (henvelope inputLength).cap tm.qstart .input .output .zero
      0 tape.index (CircuitUnrolling.symbolIndex (symbolEquiv.symm index))
      (current inputLength Work.position)
      (Fintype.card_pos_iff.mpr ⟨tm.qstart⟩) htape hsymbol
      (hposition inputLength)
    have htrajectoryHorizon :
        trajectory index.val inputLength Work.horizon =
          baseValues inputLength Work.horizon := by
      rw [show trajectory index.val inputLength Work.horizon =
          current inputLength Work.horizon by
        simp [trajectory, Work.available, Work.horizon]]
      exact hhorizon inputLength
    have htrajectoryConfigBase :
        trajectory index.val inputLength Work.configBase =
          baseValues inputLength Work.configBase := by
      rw [show trajectory index.val inputLength Work.configBase =
          current inputLength Work.configBase by
        simp [trajectory, Work.available, Work.configBase]]
      exact hconfigBase inputLength
    have htrajectoryPosition :
        trajectory index.val inputLength Work.position =
          current inputLength Work.position := by
      simp [trajectory, Work.available, Work.position]
    rw [htrajectoryHorizon, htrajectoryConfigBase, htrajectoryPosition]
    omega
  have hseq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (List.ofFn routineAt) initialSpace current width := by
    apply seqList_ofFn_spaceBoundByWidthAt_internal 4 routineAt trajectory
    · funext inputLength index
      simp [trajectory]
    · intro index
      cases tape with
      | input =>
          apply emitNextCellCopy_spaceBoundByWidth
          · exact htrajectoryValues index
          · exact hcopyCap index
      | work workIndex =>
          apply BinaryRoutine.SpaceBoundByWidthAt.branchZero
          · apply emitNextCellCopy_spaceBoundByWidth
            · exact htrajectoryValues index
            · exact hcopyCap index
          · apply emitNextWrittenCellFormula_spaceBoundByWidth
            · intro inputLength
              exact (htrajectoryClean index.val inputLength)
                |>.writtenCellClean_formula
            · intro inputLength
              have htrajectoryHorizon :
                  trajectory index.val inputLength Work.horizon =
                    baseValues inputLength Work.horizon := by
                rw [show trajectory index.val inputLength Work.horizon =
                    current inputLength Work.horizon by
                  simp [trajectory, Work.available, Work.horizon]]
                exact hhorizon inputLength
              have htrajectoryPosition :
                  trajectory index.val inputLength Work.position =
                    current inputLength Work.position := by
                simp [trajectory, Work.available, Work.position]
              rw [htrajectoryHorizon, htrajectoryPosition]
              exact hposition inputLength
            · exact htrajectoryValues index
            · intro inputLength stateIndex tapeIndex symbolIndex position
                hstate htape hsymbol hposition'
              have hcap := (henvelope inputLength).cap tm.qstart .input
                (.work workIndex) (symbolEquiv.symm index) stateIndex tapeIndex
                symbolIndex position hstate htape hsymbol (by
                  have htrajectoryHorizon :
                      trajectory index.val inputLength Work.horizon =
                        baseValues inputLength Work.horizon := by
                    rw [show trajectory index.val inputLength Work.horizon =
                        current inputLength Work.horizon by
                      simp [trajectory, Work.available, Work.horizon]]
                    exact hhorizon inputLength
                  rwa [htrajectoryHorizon] at hposition')
              have hfrontier := hwritten inputLength index (.work workIndex) rfl
              rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
              have htrajectoryAvailable :
                  trajectory index.val inputLength Work.available =
                    current inputLength Work.available +
                      prefixSize (stepCellSymbolSizeFormula tm
                        (.work workIndex)
                        (baseValues inputLength Work.horizon)
                        (current inputLength Work.position)) index.val := by
                simp [trajectory, sizeAt, Work.available]
              have htrajectoryHorizon :
                  trajectory index.val inputLength Work.horizon =
                    baseValues inputLength Work.horizon := by
                rw [show trajectory index.val inputLength Work.horizon =
                    current inputLength Work.horizon by
                  simp [trajectory, Work.available, Work.horizon]]
                exact hhorizon inputLength
              have htrajectoryConfigBase :
                  trajectory index.val inputLength Work.configBase =
                    baseValues inputLength Work.configBase := by
                rw [show trajectory index.val inputLength Work.configBase =
                    current inputLength Work.configBase by
                  simp [trajectory, Work.available, Work.configBase]]
                exact hconfigBase inputLength
              rw [htrajectoryAvailable, htrajectoryHorizon,
                htrajectoryConfigBase]
              omega
      | output =>
          apply BinaryRoutine.SpaceBoundByWidthAt.branchZero
          · apply emitNextCellCopy_spaceBoundByWidth
            · exact htrajectoryValues index
            · exact hcopyCap index
          · apply emitNextWrittenCellFormula_spaceBoundByWidth
            · intro inputLength
              exact (htrajectoryClean index.val inputLength)
                |>.writtenCellClean_formula
            · intro inputLength
              have htrajectoryHorizon :
                  trajectory index.val inputLength Work.horizon =
                    baseValues inputLength Work.horizon := by
                rw [show trajectory index.val inputLength Work.horizon =
                    current inputLength Work.horizon by
                  simp [trajectory, Work.available, Work.horizon]]
                exact hhorizon inputLength
              have htrajectoryPosition :
                  trajectory index.val inputLength Work.position =
                    current inputLength Work.position := by
                simp [trajectory, Work.available, Work.position]
              rw [htrajectoryHorizon, htrajectoryPosition]
              exact hposition inputLength
            · exact htrajectoryValues index
            · intro inputLength stateIndex tapeIndex symbolIndex position
                hstate htape hsymbol hposition'
              have hcap := (henvelope inputLength).cap tm.qstart .input
                .output (symbolEquiv.symm index) stateIndex tapeIndex
                symbolIndex position hstate htape hsymbol (by
                  have htrajectoryHorizon :
                      trajectory index.val inputLength Work.horizon =
                        baseValues inputLength Work.horizon := by
                    rw [show trajectory index.val inputLength Work.horizon =
                        current inputLength Work.horizon by
                      simp [trajectory, Work.available, Work.horizon]]
                    exact hhorizon inputLength
                  rwa [htrajectoryHorizon] at hposition')
              have hfrontier := hwritten inputLength index .output rfl
              rw [stepScheduleSize_eq_formulas_add_atoms_internal] at hcap
              have htrajectoryAvailable :
                  trajectory index.val inputLength Work.available =
                    current inputLength Work.available +
                      prefixSize (stepCellSymbolSizeFormula tm .output
                        (baseValues inputLength Work.horizon)
                        (current inputLength Work.position)) index.val := by
                simp [trajectory, sizeAt, Work.available]
              have htrajectoryHorizon :
                  trajectory index.val inputLength Work.horizon =
                    baseValues inputLength Work.horizon := by
                rw [show trajectory index.val inputLength Work.horizon =
                    current inputLength Work.horizon by
                  simp [trajectory, Work.available, Work.horizon]]
                exact hhorizon inputLength
              have htrajectoryConfigBase :
                  trajectory index.val inputLength Work.configBase =
                    baseValues inputLength Work.configBase := by
                rw [show trajectory index.val inputLength Work.configBase =
                    current inputLength Work.configBase by
                  simp [trajectory, Work.available, Work.configBase]]
                exact hconfigBase inputLength
              rw [htrajectoryAvailable, htrajectoryHorizon,
                htrajectoryConfigBase]
              omega
    · intro index inputLength
      have hmoved := htrajectoryClean index.val inputLength
      cases tape with
      | input =>
          have hscratch := hmoved.copyScratch_formula
          rw [emitNextCellCopy_effect _ _ _ _ _ hscratch.1 hscratch.2.1
            hscratch.2.2.1 hscratch.2.2.2.1 hscratch.2.2.2.2.1
            hscratch.2.2.2.2.2]
          funext currentIndex
          by_cases hindex : currentIndex = Work.available
          · subst currentIndex
            simp [trajectory, sizeAt, prefixSize_succ,
              stepCellSymbolSizeFormula, index.isLt, Work.available]
            omega
          · simp [trajectory, hindex]
      | work workIndex =>
          have htrajectoryPosition :
              trajectory index.val inputLength Work.position =
                current inputLength Work.position := by
            simp [trajectory, Work.available, Work.position]
          have htrajectoryHorizon :
              trajectory index.val inputLength Work.horizon =
                baseValues inputLength Work.horizon := by
            rw [show trajectory index.val inputLength Work.horizon =
                current inputLength Work.horizon by
              simp [trajectory, Work.available, Work.horizon]]
            exact hhorizon inputLength
          by_cases hpositionZero : current inputLength Work.position = 0
          · rw [show (routineAt index).effect
                  (trajectory index.val inputLength) =
                (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
                  (TapeSlot.work workIndex).index
                  (CircuitUnrolling.symbolIndex
                    (symbolEquiv.symm index))).effect
                  (trajectory index.val inputLength) by
                have hz : trajectory index.val inputLength Work.position = 0 :=
                  htrajectoryPosition.trans hpositionZero
                simp [routineAt, BinaryRoutine.branchZero, hz]]
            have hscratch := hmoved.copyScratch_formula
            rw [emitNextCellCopy_effect _ _ _ _ _ hscratch.1 hscratch.2.1
              hscratch.2.2.1 hscratch.2.2.2.1 hscratch.2.2.2.2.1
              hscratch.2.2.2.2.2]
            funext currentIndex
            by_cases hindex : currentIndex = Work.available
            · subst currentIndex
              simp [trajectory, sizeAt, prefixSize_succ,
                stepCellSymbolSizeFormula, index.isLt, Work.available,
                hpositionZero]
              omega
            · simp [trajectory, hindex]
          · rw [show (routineAt index).effect
                  (trajectory index.val inputLength) =
                (emitNextWrittenCellFormula tm (.work workIndex)
                  (symbolEquiv.symm index)).effect
                  (trajectory index.val inputLength) by
                have hn :
                    trajectory index.val inputLength Work.position ≠ 0 := by
                  rwa [htrajectoryPosition]
                simp [routineAt, BinaryRoutine.branchZero, hn]]
            rw [emitNextWrittenCellFormula_effect tm (.work workIndex)
              (symbolEquiv.symm index) _ hmoved.writtenCellClean_formula]
            rw [htrajectoryHorizon]
            funext currentIndex
            by_cases hindex : currentIndex = Work.available
            · subst currentIndex
              simp [trajectory, sizeAt, prefixSize_succ,
                stepCellSymbolSizeFormula, index.isLt, Work.available,
                hpositionZero]
              omega
            · simp [trajectory, hindex]
      | output =>
          have htrajectoryPosition :
              trajectory index.val inputLength Work.position =
                current inputLength Work.position := by
            simp [trajectory, Work.available, Work.position]
          have htrajectoryHorizon :
              trajectory index.val inputLength Work.horizon =
                baseValues inputLength Work.horizon := by
            rw [show trajectory index.val inputLength Work.horizon =
                current inputLength Work.horizon by
              simp [trajectory, Work.available, Work.horizon]]
            exact hhorizon inputLength
          by_cases hpositionZero : current inputLength Work.position = 0
          · rw [show (routineAt index).effect
                  (trajectory index.val inputLength) =
                (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
                  (TapeSlot.output : TapeSlot k).index
                  (CircuitUnrolling.symbolIndex
                    (symbolEquiv.symm index))).effect
                  (trajectory index.val inputLength) by
                have hz : trajectory index.val inputLength Work.position = 0 :=
                  htrajectoryPosition.trans hpositionZero
                simp [routineAt, BinaryRoutine.branchZero, hz]]
            have hscratch := hmoved.copyScratch_formula
            rw [emitNextCellCopy_effect _ _ _ _ _ hscratch.1 hscratch.2.1
              hscratch.2.2.1 hscratch.2.2.2.1 hscratch.2.2.2.2.1
              hscratch.2.2.2.2.2]
            funext currentIndex
            by_cases hindex : currentIndex = Work.available
            · subst currentIndex
              simp [trajectory, sizeAt, prefixSize_succ,
                stepCellSymbolSizeFormula, index.isLt, Work.available,
                hpositionZero]
              omega
            · simp [trajectory, hindex]
          · rw [show (routineAt index).effect
                  (trajectory index.val inputLength) =
                (emitNextWrittenCellFormula tm .output
                  (symbolEquiv.symm index)).effect
                  (trajectory index.val inputLength) by
                have hn :
                    trajectory index.val inputLength Work.position ≠ 0 := by
                  rwa [htrajectoryPosition]
                simp [routineAt, BinaryRoutine.branchZero, hn]]
            rw [emitNextWrittenCellFormula_effect tm .output
              (symbolEquiv.symm index) _ hmoved.writtenCellClean_formula]
            rw [htrajectoryHorizon]
            funext currentIndex
            by_cases hindex : currentIndex = Work.available
            · subst currentIndex
              simp [trajectory, sizeAt, prefixSize_succ,
                stepCellSymbolSizeFormula, index.isLt, Work.available,
                hpositionZero]
              omega
            · simp [trajectory, hindex]
  have hresult := BinaryRoutine.SpaceBoundByWidthAt.seqList _ hseq
  cases tape <;> simpa [routineAt, emitStepImmutableCellPosition,
    emitStepWritableCellPosition] using! hresult

private noncomputable def stepCellFormulaBodyFormula (tm : NTM k) :
    TapeSlot k → BinaryRoutine WorkCount
  | .input => emitStepImmutableCellPosition tm .input
  | .work index => emitStepWritableCellPosition tm (.work index)
  | .output => emitStepWritableCellPosition tm .output

private theorem emitStepCellTapeFormulas_spaceBoundByWidthAt_formula
    (tm : NTM k) (tape : TapeSlot k) (start : ℕ → ℕ)
    {initialSpace : ℕ → ℕ}
    {baseValues : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (baseValues inputLength))
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength))
    (hblock : ∀ inputLength,
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength) +
          prefixSize (stepCellPositionEffectSizeInternal tm tape
            (baseValues inputLength Work.horizon))
            (baseValues inputLength Work.horizon + 2) =
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon))
          (start inputLength +
            4 * (baseValues inputLength Work.horizon + 2)))
    (hend : ∀ inputLength,
      start inputLength + 4 * (baseValues inputLength Work.horizon + 2) ≤
        stepAtomCount (Fintype.card tm.Q) k
          (baseValues inputLength Work.horizon)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepCellTapeFormulas tm tape)
      initialSpace
      (fun inputLength =>
        Function.update
          (Function.update (baseValues inputLength) Work.limit₁
            (baseValues inputLength Work.horizon + 2))
          Work.available
          (baseValues inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (baseValues inputLength Work.horizon)) (start inputLength)))
      width := by
  let entry : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (baseValues inputLength) Work.limit₁
        (baseValues inputLength Work.horizon + 2))
      Work.available
      (baseValues inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength))
  let body : BinaryRoutine WorkCount := stepCellFormulaBodyFormula tm tape
  let localSize : ℕ → ℕ → ℕ := fun inputLength =>
    stepCellPositionEffectSizeInternal tm tape
      (baseValues inputLength Work.horizon)
  have hentryPhase : ∀ inputLength,
      StepPhaseCleanInternal (entry inputLength) := by
    intro inputLength
    have hlimit := update_limit₁_preserves_phaseClean_internal
      (hclean inputLength).phaseClean_forSpace_internal
      (baseValues inputLength Work.horizon + 2)
    simpa [entry] using update_available_preserves_phaseClean_forSpace_internal
      hlimit
      (baseValues inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (baseValues inputLength Work.horizon)) (start inputLength))
  have hentryHorizon : ∀ inputLength,
      entry inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    intro inputLength
    simp [entry, Work.available, Work.limit₁, Work.horizon]
  have hentryConfigBase : ∀ inputLength,
      entry inputLength Work.configBase =
        baseValues inputLength Work.configBase := by
    intro inputLength
    simp [entry, Work.available, Work.limit₁, Work.configBase]
  have hentryLimit : ∀ inputLength,
      entry inputLength Work.limit₁ =
        entry inputLength Work.horizon + 2 := by
    intro inputLength
    simp [entry, Work.available, Work.limit₁, Work.horizon]
  have hprefixFrontier : ∀ inputLength count,
      count ≤ baseValues inputLength Work.horizon + 2 →
        entry inputLength Work.available +
            prefixSize (localSize inputLength) count ≤
          baseValues inputLength Work.available +
            stepFormulasEffectSizeInternal tm
              (baseValues inputLength Work.horizon) := by
    intro inputLength count hcount
    have hlocal := prefixSize_mono (localSize inputLength) hcount
    have hglobal := prefixSize_mono
      (stepFormulaSizeAtSpecializedInternal tm
        (baseValues inputLength Work.horizon)) (hend inputLength)
    rw [show entry inputLength Work.available =
        baseValues inputLength Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon)) (start inputLength) by
      simp [entry, Work.available, Work.limit₁]]
    dsimp only [localSize] at hlocal
    have hlocal' := Nat.add_le_add_left hlocal
      (prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (baseValues inputLength Work.horizon)) (start inputLength))
    rw [hblock inputLength] at hlocal'
    rw [stepFormulasEffectSize_eq_prefixSize_internal]
    dsimp only [localSize]
    omega
  have hentryValues : ∀ inputLength index,
      entry inputLength index ≤ width inputLength := by
    intro inputLength index
    by_cases hindex : index = Work.available
    · subst index
      exact le_trans (hprefixFrontier inputLength 0 (by omega))
        (henvelope inputLength).formulaFrontier_le_internal
    · by_cases hlimit : index = Work.limit₁
      · subst index
        rw [hentryLimit inputLength, hentryHorizon inputLength]
        exact (henvelope inputLength).horizon_add_two_le_internal
      · simpa [entry, hindex, hlimit] using
          (henvelope inputLength).values_le index
  have hloop : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.binaryFor body Work.position Work.limit₁)
      initialSpace entry width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.binaryFor_of_clamped_body
    · exact fun inputLength => hentryValues inputLength Work.limit₁
    · intro inputLength count hcount
      have hcount' : count <
          baseValues inputLength Work.horizon + 2 := by
        rw [BinaryRoutine.binaryForCount, hentryLimit inputLength] at hcount
        rw [(hentryPhase inputLength).position, Nat.sub_zero,
          hentryHorizon inputLength] at hcount
        exact hcount
      have htrajectory :=
        cellFormula_binaryForValues_effect_forSpace_internal tm tape
          (entry inputLength) (hentryPhase inputLength) count
      change (BinaryRoutine.binaryForValues body Work.position
        (entry inputLength) count) Work.position ≤ width inputLength
      rw [show BinaryRoutine.binaryForValues body Work.position
          (entry inputLength) count =
        Function.update
          (Function.update (entry inputLength) Work.position count)
          Work.available
          (entry inputLength Work.available +
            prefixSize (stepCellPositionEffectSizeInternal tm tape
              (entry inputLength Work.horizon)) count) by
        simpa [body, stepCellFormulaBodyFormula] using! htrajectory]
      simp [Work.position, Work.available]
      exact le_trans (Nat.le_of_lt hcount')
        (henvelope inputLength).horizon_add_two_le_internal
    · let bodyValues := BinaryRoutine.binaryForClampedValues body
        Work.position Work.limit₁ entry
      let inputAt : ℕ → ℕ := fun code => (Nat.unpair code).1
      let countAt : ℕ → ℕ := fun code =>
        min (Nat.unpair code).2
          (BinaryRoutine.binaryForCount Work.position Work.limit₁
            (entry (inputAt code)) - 1)
      have hcountAt : ∀ code,
          countAt code < baseValues (inputAt code) Work.horizon + 2 := by
        intro code
        have hmin := Nat.min_le_right (Nat.unpair code).2
          (baseValues (inputAt code) Work.horizon + 1)
        have htotal : BinaryRoutine.binaryForCount Work.position Work.limit₁
              (entry (inputAt code)) =
            baseValues (inputAt code) Work.horizon + 2 := by
          rw [BinaryRoutine.binaryForCount, hentryLimit (inputAt code),
            (hentryPhase (inputAt code)).position, Nat.sub_zero,
            hentryHorizon (inputAt code)]
        dsimp only [countAt]
        rw [htotal, show baseValues (inputAt code) Work.horizon + 2 - 1 =
          baseValues (inputAt code) Work.horizon + 1 by omega]
        exact Nat.lt_of_le_of_lt hmin (by omega)
      have htrajectory : ∀ code,
          bodyValues code =
            Function.update
              (Function.update (entry (inputAt code)) Work.position
                (countAt code))
              Work.available
              (entry (inputAt code) Work.available +
                prefixSize (localSize (inputAt code)) (countAt code)) := by
        intro code
        unfold bodyValues BinaryRoutine.binaryForClampedValues
        change BinaryRoutine.binaryForValues body Work.position
            (entry (inputAt code)) (countAt code) = _
        have heffect := cellFormula_binaryForValues_effect_forSpace_internal
          tm tape (entry (inputAt code)) (hentryPhase (inputAt code))
          (countAt code)
        simpa [body, stepCellFormulaBodyFormula, localSize,
          hentryHorizon (inputAt code)] using! heffect
      suffices hbodySpace : BinaryRoutine.SpaceBoundByWidthAt
          (match tape with
            | .input => emitStepImmutableCellPosition tm .input
            | .work index => emitStepWritableCellPosition tm (.work index)
            | .output => emitStepWritableCellPosition tm .output)
          (fun code => initialSpace (Nat.unpair code).1) bodyValues
          (fun code => width (Nat.unpair code).1) by
        simpa [body, stepCellFormulaBodyFormula] using! hbodySpace
      apply emitStepCellPosition_spaceBoundByWidthAt_formula tm tape
          (baseValues := fun code => baseValues (inputAt code))
      · intro code
        rw [htrajectory code]
        exact (hentryPhase (inputAt code))
          |>.movedHeadClean_atPosition_forSpace_internal (countAt code)
          |>.updateAvailable_emitted_internal _
      · intro code
        rw [htrajectory code]
        simp [Work.position, Work.available, Work.horizon]
        simpa only [Work.horizon] using hentryHorizon (inputAt code)
      · intro code
        rw [htrajectory code]
        simp [Work.position, Work.available, Work.configBase]
        simpa only [Work.configBase] using hentryConfigBase (inputAt code)
      · intro code
        rw [htrajectory code]
        simp [Work.position, Work.available, Work.horizon]
        have hcount := hcountAt code
        simp only [Work.horizon] at hcount ⊢
        omega
      · intro code index
        rw [htrajectory code]
        by_cases hindex : index = Work.available
        · subst index
          simp [Work.position, Work.available]
          exact le_trans
            (hprefixFrontier (inputAt code) (countAt code)
              (Nat.le_of_lt (hcountAt code)))
            (henvelope (inputAt code)).formulaFrontier_le_internal
        · by_cases hposition : index = Work.position
          · subst index
            simp [Work.position, Work.available]
            exact le_trans (Nat.le_of_lt (hcountAt code))
              (henvelope (inputAt code)).horizon_add_two_le_internal
          · simp [hindex, hposition]
            exact hentryValues (inputAt code) index
      · exact fun code => henvelope (inputAt code)
      · intro code
        rw [htrajectory code]
        simp [Work.position, Work.available, Work.horizon]
        have hnext := prefixSize_mono (localSize (inputAt code))
          (show countAt code + 1 ≤
              baseValues (inputAt code) Work.horizon + 2 by
            exact hcountAt code)
        rw [prefixSize_succ] at hnext
        have hfrontier := hprefixFrontier (inputAt code)
          (baseValues (inputAt code) Work.horizon + 2) (by omega)
        dsimp only [localSize] at hnext hfrontier ⊢
        simp only [Work.available, Work.horizon] at hnext hfrontier ⊢
        omega
      · intro code index writable htape
        subst tape
        rw [htrajectory code]
        simp only [Function.update_apply]
        simp [Work.position, Work.available, Work.horizon]
        let T := baseValues (inputAt code) Work.horizon
        let position := countAt code
        let symbolSize := stepCellSymbolSizeFormula tm writable.toTapeSlot T
          position
        have htotal := hprefixFrontier (inputAt code) (T + 2) (by omega)
        have hpositionBound : position < T + 2 := hcountAt code
        by_cases hzero : position = 0
        · have hzeroPrefix : prefixSize symbolSize index.val ≤ 4 := by
            have hmono := prefixSize_mono symbolSize
              (show index.val ≤ 4 by omega)
            rw [stepCellSymbolSizeFormula_prefix_four tm
              writable.toTapeSlot T position] at hmono
            simp [stepCellPositionEffectSizeInternal, hzero] at hmono
            cases writable <;>
              simpa [WritableSlot.toTapeSlot] using hmono
          have hwrittenAtOne :
              nextWrittenCellFormulaScheduleSize
                  (transitionCases tm).length k T
                  (writtenCellEffectSelectedAt tm writable
                    (symbolEquiv.symm index)) (effectCaseChoiceAt tm) ≤
                stepCellPositionEffectSizeInternal tm writable.toTapeSlot T 1 := by
            let oneSize := stepCellSymbolSizeFormula tm writable.toTapeSlot T 1
            have hmono := prefixSize_mono oneSize
              (show index.val + 1 ≤ 4 by omega)
            rw [prefixSize_succ,
              stepCellSymbolSizeFormula_prefix_four tm
                writable.toTapeSlot T 1] at hmono
            have hsize : oneSize index.val =
                nextWrittenCellFormulaScheduleSize
                  (transitionCases tm).length k T
                  (writtenCellEffectSelectedAt tm writable
                    (symbolEquiv.symm index)) (effectCaseChoiceAt tm) := by
              cases writable <;>
                simp [oneSize, stepCellSymbolSizeFormula, index.isLt,
                  WritableSlot.toTapeSlot]
            rw [hsize] at hmono
            omega
          have htwo := prefixSize_mono
            (stepCellPositionEffectSizeInternal tm writable.toTapeSlot T)
            (show 2 ≤ T + 2 by omega)
          rw [show prefixSize
              (stepCellPositionEffectSizeInternal tm writable.toTapeSlot T) 2 =
                stepCellPositionEffectSizeInternal tm writable.toTapeSlot T 0 +
                  stepCellPositionEffectSizeInternal tm writable.toTapeSlot T 1 by
            rw [show 2 = 1 + 1 by omega, prefixSize_succ,
              show prefixSize
                  (stepCellPositionEffectSizeInternal tm writable.toTapeSlot T)
                  1 =
                stepCellPositionEffectSizeInternal tm writable.toTapeSlot T 0 by
              rw [show 1 = 0 + 1 by omega, prefixSize_succ]
              simp [prefixSize]]] at htwo
          have hzeroEffect :
              stepCellPositionEffectSizeInternal tm writable.toTapeSlot T 0 = 4 := by
            cases writable <;>
              simp [stepCellPositionEffectSizeInternal,
                WritableSlot.toTapeSlot]
          rw [hzeroEffect] at htwo
          dsimp only [T, position, symbolSize] at *
          dsimp only [localSize] at htotal ⊢
          simp [hzero] at hzeroPrefix ⊢
          simp only [Work.horizon] at hzeroPrefix hwrittenAtOne htwo
          simp only [Work.available, Work.horizon] at htotal ⊢
          omega
        · have hsymbol := prefixSize_mono symbolSize
              (show index.val + 1 ≤ 4 by omega)
          rw [prefixSize_succ,
            stepCellSymbolSizeFormula_prefix_four tm
              writable.toTapeSlot T position] at hsymbol
          have hsize : symbolSize index.val =
              nextWrittenCellFormulaScheduleSize
                (transitionCases tm).length k T
                (writtenCellEffectSelectedAt tm writable
                  (symbolEquiv.symm index)) (effectCaseChoiceAt tm) := by
            cases writable <;>
              simp [symbolSize, stepCellSymbolSizeFormula, index.isLt, hzero,
                WritableSlot.toTapeSlot]
          rw [hsize] at hsymbol
          have hnext := prefixSize_mono
            (stepCellPositionEffectSizeInternal tm writable.toTapeSlot T)
            (show position + 1 ≤ T + 2 by exact hpositionBound)
          rw [prefixSize_succ] at hnext
          dsimp only [T, position, symbolSize] at *
          dsimp only [localSize] at htotal ⊢
          simp only [Work.available, Work.horizon] at hsymbol hnext htotal ⊢
          omega
  have hclear : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.position) initialSpace
      (fun inputLength =>
        (BinaryRoutine.binaryFor body Work.position Work.limit₁).effect
          (entry inputLength)) width := by
    apply BinaryRoutine.SpaceBoundByWidthAt.clear
    intro inputLength
    change BinaryRoutine.binaryForValues body Work.position
        (entry inputLength)
        (BinaryRoutine.binaryForCount Work.position Work.limit₁
          (entry inputLength)) Work.position ≤ width inputLength
    have htotal : BinaryRoutine.binaryForCount Work.position Work.limit₁
          (entry inputLength) = entry inputLength Work.horizon + 2 := by
      rw [BinaryRoutine.binaryForCount, hentryLimit inputLength,
        (hentryPhase inputLength).position, Nat.sub_zero]
    have htrajectory :=
      cellFormula_binaryForValues_effect_forSpace_internal tm tape
        (entry inputLength) (hentryPhase inputLength)
        (BinaryRoutine.binaryForCount Work.position Work.limit₁
          (entry inputLength))
    rw [show BinaryRoutine.binaryForValues body Work.position
          (entry inputLength)
          (BinaryRoutine.binaryForCount Work.position Work.limit₁
            (entry inputLength)) =
        Function.update
          (Function.update (entry inputLength) Work.position
            (BinaryRoutine.binaryForCount Work.position Work.limit₁
              (entry inputLength)))
          Work.available
          (entry inputLength Work.available +
            prefixSize (stepCellPositionEffectSizeInternal tm tape
              (entry inputLength Work.horizon))
              (BinaryRoutine.binaryForCount Work.position Work.limit₁
                (entry inputLength))) by
      simpa [body, stepCellFormulaBodyFormula] using! htrajectory]
    simp [Work.position, Work.available]
    have htotal' : BinaryRoutine.binaryForCount 30 Work.limit₁
        (entry inputLength) = entry inputLength Work.horizon + 2 := by
      simpa [Work.position] using htotal
    rw [htotal']
    rw [hentryHorizon inputLength]
    exact (henvelope inputLength).horizon_add_two_le_internal
  have hresult := BinaryRoutine.SpaceBoundByWidthAt.seq hloop hclear
  cases tape <;> simpa [body, stepCellFormulaBodyFormula,
    emitStepCellTapeFormulas] using hresult

private theorem emitStepHeadTapeList_spaceBoundByWidthAt_formula
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (baseValues inputLength))
    (hhorizon : ∀ inputLength,
      0 < baseValues inputLength Work.horizon)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength)) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepHeadTapeFormulas tm))
      initialSpace
      (fun inputLength =>
        Function.update
          (Function.update (baseValues inputLength) Work.limit₁
            (baseValues inputLength Work.horizon + 1))
          Work.available
          (baseValues inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (baseValues inputLength Work.horizon))
              (Fintype.card tm.Q)))
      width := by
  let tapeCount := k + 2
  let tapeAt : Fin tapeCount → TapeSlot k := (tapeSlotEquiv k).symm
  let startAt : ℕ → ℕ → ℕ := fun count inputLength =>
    Fintype.card tm.Q +
      count * (baseValues inputLength Work.horizon + 1)
  let trajectory : ℕ → ℕ → BinaryValues WorkCount :=
    fun count inputLength =>
      Function.update
        (Function.update (baseValues inputLength) Work.limit₁
          (baseValues inputLength Work.horizon + 1))
        Work.available
        (baseValues inputLength Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon))
            (startAt count inputLength))
  have htrajectoryPhase : ∀ count inputLength,
      StepPhaseCleanInternal (trajectory count inputLength) := by
    intro count inputLength
    have hlimit := update_limit₁_preserves_phaseClean_internal
      (hclean inputLength).phaseClean_forSpace_internal
      (baseValues inputLength Work.horizon + 1)
    simpa [trajectory] using update_available_preserves_phaseClean_forSpace_internal
      hlimit _
  have htrajectoryHorizon : ∀ count inputLength,
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    intro count inputLength
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have htrajectoryLimit : ∀ count inputLength,
      trajectory count inputLength Work.limit₁ =
        trajectory count inputLength Work.horizon + 1 := by
    intro count inputLength
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hseq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (List.ofFn fun index : Fin tapeCount =>
        emitStepHeadTapeFormulas tm (tapeAt index))
      initialSpace (trajectory 0) width := by
    apply seqList_ofFn_spaceBoundByWidthAt_internal tapeCount
      (fun index => emitStepHeadTapeFormulas tm (tapeAt index)) trajectory
    · funext inputLength index
      simp [trajectory, startAt]
    · intro index
      apply emitStepHeadTapeFormulas_spaceBoundByWidthAt_formula tm
        (tapeAt index) (startAt index.val)
      · exact hclean
      · exact hhorizon
      · exact henvelope
      · intro inputLength
        have hprefix := headPrefixBlock_internal tm
          (baseValues inputLength Work.horizon) (tapeAt index)
        have hidx := tapeSlotEquiv_symm_index_internal index
        change (tapeAt index).index.val = index.val at hidx
        rw [hidx] at hprefix
        simpa [startAt, Nat.add_assoc] using hprefix.symm
      · intro inputLength
        have hindex := index.isLt
        have hmul : (index.val + 1) *
              (baseValues inputLength Work.horizon + 1) ≤
            (k + 2) * (baseValues inputLength Work.horizon + 1) :=
          Nat.mul_le_mul_right _ (by
            dsimp only [tapeCount] at hindex
            exact hindex)
        have hrewrite : Fintype.card tm.Q + index.val *
                (baseValues inputLength Work.horizon + 1) +
                baseValues inputLength Work.horizon + 1 =
            Fintype.card tm.Q + (index.val + 1) *
              (baseValues inputLength Work.horizon + 1) := by
          ring
        unfold stepAtomCount
        dsimp only [startAt, tapeCount]
        rw [hrewrite]
        omega
    · intro index inputLength
      have heffect := emitStepHeadTapeFormulas_effect_internal tm
        (tapeAt index) (trajectory index.val inputLength)
        (htrajectoryPhase index.val inputLength)
        (by simpa [htrajectoryHorizon index.val inputLength] using
          hhorizon inputLength)
        (htrajectoryLimit index.val inputLength)
      rw [htrajectoryHorizon index.val inputLength] at heffect
      rw [heffect]
      have hprefix := headPrefixBlock_internal tm
        (baseValues inputLength Work.horizon) (tapeAt index)
      have hidx := tapeSlotEquiv_symm_index_internal index
      change (tapeAt index).index.val = index.val at hidx
      rw [hidx] at hprefix
      have havailable :
          trajectory index.val inputLength Work.available +
              (baseValues inputLength Work.horizon + 1) *
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (baseValues inputLength Work.horizon)
                  (movedHeadCaseSelectedAt tm (tapeAt index))
                  (effectCaseChoiceAt tm) =
            baseValues inputLength Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (baseValues inputLength Work.horizon))
                (startAt (index.val + 1) inputLength) := by
        rw [show trajectory index.val inputLength Work.available =
            baseValues inputLength Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (baseValues inputLength Work.horizon))
                (startAt index.val inputLength) by
          simp [trajectory, Work.available, Work.limit₁]]
        calc
          baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (startAt index.val inputLength) +
              (baseValues inputLength Work.horizon + 1) *
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (baseValues inputLength Work.horizon)
                  (movedHeadCaseSelectedAt tm (tapeAt index))
                  (effectCaseChoiceAt tm) =
              baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (Fintype.card tm.Q + index.val *
                    (baseValues inputLength Work.horizon + 1) +
                    (baseValues inputLength Work.horizon + 1)) := by
                rw [hprefix]
                dsimp only [startAt]
                omega
          _ = baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (startAt (index.val + 1) inputLength) := by
            congr 2
            simp [startAt]
            ring
      funext current
      by_cases hcurrent : current = Work.available
      · subst current
        simpa [trajectory, Work.available, Work.limit₁] using havailable
      · simp [trajectory, hcurrent]
  have hzero : trajectory 0 = fun inputLength =>
      Function.update
        (Function.update (baseValues inputLength) Work.limit₁
          (baseValues inputLength Work.horizon + 1))
        Work.available
        (baseValues inputLength Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon))
            (Fintype.card tm.Q)) := by
    funext inputLength index
    simp [trajectory, startAt]
  rw [hzero] at hseq
  rw [List.map_ofFn]
  simpa only [tapeAt, tapeCount] using! hseq

private theorem emitStepCellTapeList_spaceBoundByWidthAt_formula
    (tm : NTM k) {initialSpace : ℕ → ℕ}
    {baseValues : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (baseValues inputLength))
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (baseValues inputLength) (width inputLength)) :
    BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepCellTapeFormulas tm))
      initialSpace
      (fun inputLength =>
        Function.update
          (Function.update (baseValues inputLength) Work.limit₁
            (baseValues inputLength Work.horizon + 2))
          Work.available
          (baseValues inputLength Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (baseValues inputLength Work.horizon))
              (Fintype.card tm.Q +
                (k + 2) * (baseValues inputLength Work.horizon + 1))))
      width := by
  let tapeCount := k + 2
  let tapeAt : Fin tapeCount → TapeSlot k := (tapeSlotEquiv k).symm
  let startAt : ℕ → ℕ → ℕ := fun count inputLength =>
    Fintype.card tm.Q + tapeCount *
        (baseValues inputLength Work.horizon + 1) +
      count * (baseValues inputLength Work.horizon + 2) * 4
  let trajectory : ℕ → ℕ → BinaryValues WorkCount :=
    fun count inputLength =>
      Function.update
        (Function.update (baseValues inputLength) Work.limit₁
          (baseValues inputLength Work.horizon + 2))
        Work.available
        (baseValues inputLength Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon))
            (startAt count inputLength))
  have htrajectoryPhase : ∀ count inputLength,
      StepPhaseCleanInternal (trajectory count inputLength) := by
    intro count inputLength
    have hlimit := update_limit₁_preserves_phaseClean_internal
      (hclean inputLength).phaseClean_forSpace_internal
      (baseValues inputLength Work.horizon + 2)
    simpa [trajectory] using update_available_preserves_phaseClean_forSpace_internal
      hlimit _
  have htrajectoryHorizon : ∀ count inputLength,
      trajectory count inputLength Work.horizon =
        baseValues inputLength Work.horizon := by
    intro count inputLength
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have htrajectoryLimit : ∀ count inputLength,
      trajectory count inputLength Work.limit₁ =
        trajectory count inputLength Work.horizon + 2 := by
    intro count inputLength
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hseq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (List.ofFn fun index : Fin tapeCount =>
        emitStepCellTapeFormulas tm (tapeAt index))
      initialSpace (trajectory 0) width := by
    apply seqList_ofFn_spaceBoundByWidthAt_internal tapeCount
      (fun index => emitStepCellTapeFormulas tm (tapeAt index)) trajectory
    · funext inputLength index
      simp [trajectory, startAt, tapeCount]
    · intro index
      apply emitStepCellTapeFormulas_spaceBoundByWidthAt_formula tm
        (tapeAt index) (startAt index.val)
      · exact hclean
      · exact henvelope
      · intro inputLength
        have hprefix := cellPrefixBlock_internal tm
          (baseValues inputLength Work.horizon) (tapeAt index)
        have hidx := tapeSlotEquiv_symm_index_internal index
        change (tapeAt index).index.val = index.val at hidx
        rw [hidx] at hprefix
        simpa [startAt, tapeCount, Nat.add_assoc] using hprefix.symm
      · intro inputLength
        have hindex := index.isLt
        have hmul : (index.val + 1) *
                (baseValues inputLength Work.horizon + 2) * 4 ≤
            (k + 2) * (baseValues inputLength Work.horizon + 2) * 4 :=
          Nat.mul_le_mul_right 4 (Nat.mul_le_mul_right _ (by
            dsimp only [tapeCount] at hindex
            exact hindex))
        have hrewrite :
            Fintype.card tm.Q + (k + 2) *
                  (baseValues inputLength Work.horizon + 1) +
                index.val * (baseValues inputLength Work.horizon + 2) * 4 +
                4 * (baseValues inputLength Work.horizon + 2) =
              Fintype.card tm.Q + (k + 2) *
                  (baseValues inputLength Work.horizon + 1) +
                (index.val + 1) *
                  (baseValues inputLength Work.horizon + 2) * 4 := by
          ring
        have htotal : (k + 2) *
              (baseValues inputLength Work.horizon + 2) * 4 =
            4 * (k + 2) *
              (baseValues inputLength Work.horizon + 2) := by
          ring
        unfold stepAtomCount
        dsimp only [startAt, tapeCount]
        rw [htotal] at hmul
        rw [hrewrite]
        omega
    · intro index inputLength
      have heffect := emitStepCellTapeFormulas_effect_internal tm
        (tapeAt index) (trajectory index.val inputLength)
        (htrajectoryPhase index.val inputLength)
        (htrajectoryLimit index.val inputLength)
      rw [htrajectoryHorizon index.val inputLength] at heffect
      rw [heffect]
      have hprefix := cellPrefixBlock_internal tm
        (baseValues inputLength Work.horizon) (tapeAt index)
      have hidx := tapeSlotEquiv_symm_index_internal index
      change (tapeAt index).index.val = index.val at hidx
      rw [hidx] at hprefix
      have havailable :
          trajectory index.val inputLength Work.available +
              prefixSize (stepCellPositionEffectSizeInternal tm
                (tapeAt index) (baseValues inputLength Work.horizon))
                (baseValues inputLength Work.horizon + 2) =
            baseValues inputLength Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (baseValues inputLength Work.horizon))
                (startAt (index.val + 1) inputLength) := by
        rw [show trajectory index.val inputLength Work.available =
            baseValues inputLength Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (baseValues inputLength Work.horizon))
                (startAt index.val inputLength) by
          simp [trajectory, Work.available, Work.limit₁]]
        calc
          baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (startAt index.val inputLength) +
              prefixSize (stepCellPositionEffectSizeInternal tm
                (tapeAt index) (baseValues inputLength Work.horizon))
                (baseValues inputLength Work.horizon + 2) =
              baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (Fintype.card tm.Q + (k + 2) *
                      (baseValues inputLength Work.horizon + 1) +
                    index.val *
                      (baseValues inputLength Work.horizon + 2) * 4 +
                    4 * (baseValues inputLength Work.horizon + 2)) := by
                rw [hprefix]
                dsimp only [startAt, tapeCount]
                omega
          _ = baseValues inputLength Work.available +
                prefixSize (stepFormulaSizeAtSpecializedInternal tm
                  (baseValues inputLength Work.horizon))
                  (startAt (index.val + 1) inputLength) := by
            congr 2
            simp [startAt]
            ring
      funext current
      by_cases hcurrent : current = Work.available
      · subst current
        simpa [trajectory, Work.available, Work.limit₁] using havailable
      · simp [trajectory, hcurrent]
  have hzero : trajectory 0 = fun inputLength =>
      Function.update
        (Function.update (baseValues inputLength) Work.limit₁
          (baseValues inputLength Work.horizon + 2))
        Work.available
        (baseValues inputLength Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (baseValues inputLength Work.horizon))
            (Fintype.card tm.Q +
              (k + 2) * (baseValues inputLength Work.horizon + 1))) := by
    funext inputLength index
    simp [trajectory, startAt, tapeCount]
  rw [hzero] at hseq
  rw [List.map_ofFn]
  simpa only [tapeAt, tapeCount] using! hseq

private theorem emitStepHeadTapeList_effect_formula (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (BinaryRoutine.seqList
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepHeadTapeFormulas tm))).effect
      (Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 1))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon)) (Fintype.card tm.Q))) =
      Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 1))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1))) := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let startAt : ℕ → ℕ := fun count =>
    Fintype.card tm.Q + count * (values Work.horizon + 1)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update values Work.limit₁ (values Work.horizon + 1))
      Work.available
      (values Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values Work.horizon)) (startAt count))
  have hphase : ∀ count, StepPhaseCleanInternal (trajectory count) := by
    intro count
    have hlimit := update_limit₁_preserves_phaseClean_internal
      hclean.phaseClean_forSpace_internal (values Work.horizon + 1)
    simpa [trajectory] using
      update_available_preserves_phaseClean_forSpace_internal hlimit _
  have hhorizonAt : ∀ count,
      trajectory count Work.horizon = values Work.horizon := by
    intro count
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hlimitAt : ∀ count,
      trajectory count Work.limit₁ = trajectory count Work.horizon + 1 := by
    intro count
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hstep : ∀ index : Fin (k + 2),
      (emitStepHeadTapeFormulas tm (tapeAt index)).effect
          (trajectory index.val) = trajectory (index.val + 1) := by
    intro index
    have heffect := emitStepHeadTapeFormulas_effect_internal tm
      (tapeAt index) (trajectory index.val) (hphase index.val)
      (by simpa [hhorizonAt index.val] using hhorizon) (hlimitAt index.val)
    rw [hhorizonAt index.val] at heffect
    rw [heffect]
    have hprefix := headPrefixBlock_internal tm (values Work.horizon)
      (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    change (tapeAt index).index.val = index.val at hidx
    rw [hidx] at hprefix
    have havailable :
        trajectory index.val Work.available +
            (values Work.horizon + 1) *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon)
                (movedHeadCaseSelectedAt tm (tapeAt index))
                (effectCaseChoiceAt tm) =
          values Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (values Work.horizon)) (startAt (index.val + 1)) := by
      rw [show trajectory index.val Work.available =
          values Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (values Work.horizon)) (startAt index.val) by
        simp [trajectory, Work.available, Work.limit₁]]
      calc
        values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon)) (startAt index.val) +
            (values Work.horizon + 1) *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon)
                (movedHeadCaseSelectedAt tm (tapeAt index))
                (effectCaseChoiceAt tm) =
            values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon))
                (Fintype.card tm.Q + index.val *
                  (values Work.horizon + 1) +
                  (values Work.horizon + 1)) := by
            rw [hprefix]
            dsimp only [startAt]
            omega
        _ = values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon)) (startAt (index.val + 1)) := by
          congr 2
          simp [startAt]
          ring
    funext current
    by_cases hcurrent : current = Work.available
    · subst current
      simpa [trajectory, Work.available, Work.limit₁] using havailable
    · simp [trajectory, hcurrent]
  have hend := BinaryRoutine.seqList_ofFn_effect_eq_trajectory (k + 2)
    (fun index => emitStepHeadTapeFormulas tm (tapeAt index))
    (trajectory 0) trajectory rfl hstep
  rw [List.map_ofFn]
  have hstart : Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 1))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon)) (Fintype.card tm.Q)) = trajectory 0 := by
    funext index
    simp [trajectory, startAt]
  have hfinish : trajectory (k + 2) =
      Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 1))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (Fintype.card tm.Q +
              (k + 2) * (values Work.horizon + 1))) := by
    funext index
    simp [trajectory, startAt]
  rw [hstart, ← hfinish]
  simpa only [tapeAt] using! hend

private theorem emitStepCellTapeList_effect_formula (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (BinaryRoutine.seqList
      ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepCellTapeFormulas tm))).effect
      (Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 2))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1)))) =
      Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 2))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (stepAtomCount (Fintype.card tm.Q) k
              (values Work.horizon))) := by
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let startAt : ℕ → ℕ := fun count =>
    Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
      count * (values Work.horizon + 2) * 4
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update values Work.limit₁ (values Work.horizon + 2))
      Work.available
      (values Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values Work.horizon)) (startAt count))
  have hphase : ∀ count, StepPhaseCleanInternal (trajectory count) := by
    intro count
    have hlimit := update_limit₁_preserves_phaseClean_internal
      hclean.phaseClean_forSpace_internal (values Work.horizon + 2)
    simpa [trajectory] using
      update_available_preserves_phaseClean_forSpace_internal hlimit _
  have hhorizonAt : ∀ count,
      trajectory count Work.horizon = values Work.horizon := by
    intro count
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hlimitAt : ∀ count,
      trajectory count Work.limit₁ = trajectory count Work.horizon + 2 := by
    intro count
    simp [trajectory, Work.limit₁, Work.available, Work.horizon]
  have hstep : ∀ index : Fin (k + 2),
      (emitStepCellTapeFormulas tm (tapeAt index)).effect
          (trajectory index.val) = trajectory (index.val + 1) := by
    intro index
    have heffect := emitStepCellTapeFormulas_effect_internal tm
      (tapeAt index) (trajectory index.val) (hphase index.val)
      (hlimitAt index.val)
    rw [hhorizonAt index.val] at heffect
    rw [heffect]
    have hprefix := cellPrefixBlock_internal tm (values Work.horizon)
      (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    change (tapeAt index).index.val = index.val at hidx
    rw [hidx] at hprefix
    have havailable :
        trajectory index.val Work.available +
            prefixSize (stepCellPositionEffectSizeInternal tm
              (tapeAt index) (values Work.horizon))
              (values Work.horizon + 2) =
          values Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (values Work.horizon)) (startAt (index.val + 1)) := by
      rw [show trajectory index.val Work.available =
          values Work.available +
            prefixSize (stepFormulaSizeAtSpecializedInternal tm
              (values Work.horizon)) (startAt index.val) by
        simp [trajectory, Work.available, Work.limit₁]]
      calc
        values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon)) (startAt index.val) +
            prefixSize (stepCellPositionEffectSizeInternal tm
              (tapeAt index) (values Work.horizon))
              (values Work.horizon + 2) =
            values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon))
                (Fintype.card tm.Q + (k + 2) *
                    (values Work.horizon + 1) +
                  index.val * (values Work.horizon + 2) * 4 +
                  4 * (values Work.horizon + 2)) := by
            rw [hprefix]
            dsimp only [startAt]
            omega
        _ = values Work.available +
              prefixSize (stepFormulaSizeAtSpecializedInternal tm
                (values Work.horizon)) (startAt (index.val + 1)) := by
          congr 2
          simp [startAt]
          ring
    funext current
    by_cases hcurrent : current = Work.available
    · subst current
      simpa [trajectory, Work.available, Work.limit₁] using havailable
    · simp [trajectory, hcurrent]
  have hend := BinaryRoutine.seqList_ofFn_effect_eq_trajectory (k + 2)
    (fun index => emitStepCellTapeFormulas tm (tapeAt index))
    (trajectory 0) trajectory rfl hstep
  have hroutines :
      (List.ofFn (tapeSlotEquiv k).symm).map
          (emitStepCellTapeFormulas tm) =
        List.ofFn (fun index : Fin (k + 2) =>
          emitStepCellTapeFormulas tm (tapeAt index)) := by
    rw [List.map_ofFn]
    rfl
  rw [hroutines]
  have hstart : Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 2))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1))) =
      trajectory 0 := by
    funext index
    simp [trajectory, startAt]
  have hfinish : trajectory (k + 2) =
      Function.update
        (Function.update values Work.limit₁ (values Work.horizon + 2))
        Work.available
        (values Work.available +
          prefixSize (stepFormulaSizeAtSpecializedInternal tm
            (values Work.horizon))
            (stepAtomCount (Fintype.card tm.Q) k
              (values Work.horizon))) := by
    funext current
    by_cases hcurrent : current = Work.available
    · subst current
      simp [trajectory, startAt, stepAtomCount, Work.available,
        Work.limit₁]
      congr 2
      ring
    · simp [trajectory, hcurrent]
  rw [hstart, ← hfinish]
  simpa only [tapeAt] using hend

/-- The complete forward formula phase stays within the shared width
envelope. -/
theorem emitStepFormulas_spaceBoundByWidth_internal (tm : NTM k)
    {initialSpace : ℕ → ℕ}
    {values : ℕ → BinaryValues WorkCount} {width : ℕ → ℕ}
    (hclean : ∀ inputLength, StepClean (values inputLength))
    (hhorizon : ∀ inputLength, 0 < values inputLength Work.horizon)
    (henvelope : ∀ inputLength,
      StepWidthEnvelope tm (values inputLength) (width inputLength)) :
    BinaryRoutine.SpaceBoundByWidthAt (emitStepFormulas tm)
      initialSpace values width := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let afterState : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update (values inputLength) Work.available
      (values inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon)) (Fintype.card tm.Q))
  let afterLimit₁ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (values inputLength) Work.limit₁
        (values inputLength Work.horizon + 1))
      Work.available
      (values inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon)) (Fintype.card tm.Q))
  let afterHeads : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (values inputLength) Work.limit₁
        (values inputLength Work.horizon + 1))
      Work.available
      (values inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon))
          (Fintype.card tm.Q +
            (k + 2) * (values inputLength Work.horizon + 1)))
  let afterLimit₂ : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (values inputLength) Work.limit₁
        (values inputLength Work.horizon + 2))
      Work.available
      (values inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon))
          (Fintype.card tm.Q +
            (k + 2) * (values inputLength Work.horizon + 1)))
  let afterCells : ℕ → BinaryValues WorkCount := fun inputLength =>
    Function.update
      (Function.update (values inputLength) Work.limit₁
        (values inputLength Work.horizon + 2))
      Work.available
      (values inputLength Work.available +
        prefixSize (stepFormulaSizeAtSpecializedInternal tm
          (values inputLength Work.horizon))
          (stepAtomCount (Fintype.card tm.Q) k
            (values inputLength Work.horizon)))
  have hstateEffect (inputLength : ℕ) :
      (emitStepStateFormulas tm).effect (values inputLength) =
        afterState inputLength := by
    rw [emitStepStateFormulas_effect_internal tm _ (hclean inputLength)]
    change Function.update (values inputLength) Work.available
        (values inputLength Work.available +
          stepStateFormulasEffectSizeInternal tm
            (values inputLength Work.horizon)) = afterState inputLength
    rw [stepStateFormulasEffectSize_eq_prefixSize_internal]
  have hstateEffectFamily :
      (fun inputLength =>
        (emitStepStateFormulas tm).effect (values inputLength)) =
        afterState := by
    funext inputLength
    exact hstateEffect inputLength
  have hstateSpace : BinaryRoutine.SpaceBoundByWidthAt
      (emitStepStateFormulas tm) initialSpace values width :=
    emitStepStateFormulas_spaceBoundByWidthAt_formula tm hclean henvelope
  have hafterStateValues : ∀ inputLength index,
      afterState inputLength index ≤ width inputLength := by
    intro inputLength index
    dsimp only [afterState]
    exact BinaryRoutine.values_update_le Work.available
      (henvelope inputLength).values_le
      ((henvelope inputLength).formulaPrefix_le_internal (by
        unfold stepAtomCount
        omega)) index
  have hafterStateHorizon (inputLength : ℕ) :
      afterState inputLength Work.horizon =
        values inputLength Work.horizon := by
    dsimp only [afterState]
    simp [Work.available, Work.horizon]
  have hlimit₁Result (inputLength : ℕ) :
      afterState inputLength Work.horizon + 1 ≤ width inputLength := by
    rw [hafterStateHorizon]
    have hbound := (henvelope inputLength).horizon_add_two_le_internal
    omega
  have hlimit₁Space : BinaryRoutine.SpaceBoundByWidthAt
      (setStepPositionLimit 1) initialSpace afterState width :=
    setStepPositionLimit_spaceBoundByWidthAt_internal 1 hafterStateValues
      hlimit₁Result
  have hlimit₁Effect (inputLength : ℕ) :
      (setStepPositionLimit 1).effect (afterState inputLength) =
        afterLimit₁ inputLength := by
    rw [setStepPositionLimit_effect_local_internal, hafterStateHorizon]
    dsimp only [afterState, afterLimit₁]
    rw [Function.update_comm (show Work.available ≠ Work.limit₁ by
      decide)]
  have hfirstTwo : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [emitStepStateFormulas tm, setStepPositionLimit 1]
        initialSpace values width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    refine ⟨hstateSpace, ?_⟩
    exact ⟨by simpa only [hstateEffectFamily] using hlimit₁Space, trivial⟩
  have hfirstTwoEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          [emitStepStateFormulas tm, setStepPositionLimit 1]).effect
            (values inputLength)) = afterLimit₁ := by
    funext inputLength
    simpa only [BinaryRoutine.seqList, BinaryRoutine.seq,
      BinaryRoutine.identity, BinaryRoutine.emitBits,
      hstateEffect inputLength] using! hlimit₁Effect inputLength
  have hheadSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (tapes.map (emitStepHeadTapeFormulas tm)) initialSpace afterLimit₁
        width := by
    simpa only [tapes, afterLimit₁] using
      emitStepHeadTapeList_spaceBoundByWidthAt_formula tm hclean hhorizon
        henvelope
  have hthroughHeads : BinaryRoutine.SeqListSpaceBoundByWidthAt
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm)) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      [emitStepStateFormulas tm, setStepPositionLimit 1]
      (tapes.map (emitStepHeadTapeFormulas tm)) hfirstTwo (by
        simpa only [hfirstTwoEffect] using hheadSeq)
  have hheadEffect (inputLength : ℕ) :
      (BinaryRoutine.seqList
        (tapes.map (emitStepHeadTapeFormulas tm))).effect
          (afterLimit₁ inputLength) = afterHeads inputLength := by
    simpa only [tapes, afterLimit₁, afterHeads] using
      emitStepHeadTapeList_effect_formula tm (values inputLength)
        (hclean inputLength) (hhorizon inputLength)
  have hthroughHeadsEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
            tapes.map (emitStepHeadTapeFormulas tm))).effect
              (values inputLength)) = afterHeads := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      [emitStepStateFormulas tm, setStepPositionLimit 1]).effect
        (values inputLength) = afterLimit₁ inputLength by
          exact congrFun hfirstTwoEffect inputLength]
    exact hheadEffect inputLength
  have hafterHeadsValues : ∀ inputLength index,
      afterHeads inputLength index ≤ width inputLength := by
    intro inputLength index
    dsimp only [afterHeads]
    exact BinaryRoutine.values_update_le Work.available
      (BinaryRoutine.values_update_le Work.limit₁
        (henvelope inputLength).values_le (by
          have hbound :=
            (henvelope inputLength).horizon_add_two_le_internal
          omega))
      ((henvelope inputLength).formulaPrefix_le_internal (by
        unfold stepAtomCount
        omega)) index
  have hafterHeadsHorizon (inputLength : ℕ) :
      afterHeads inputLength Work.horizon =
        values inputLength Work.horizon := by
    dsimp only [afterHeads]
    simp [Work.limit₁, Work.available, Work.horizon]
  have hlimit₂Result (inputLength : ℕ) :
      afterHeads inputLength Work.horizon + 2 ≤ width inputLength := by
    rw [hafterHeadsHorizon]
    exact (henvelope inputLength).horizon_add_two_le_internal
  have hlimit₂Space : BinaryRoutine.SpaceBoundByWidthAt
      (setStepPositionLimit 2) initialSpace afterHeads width :=
    setStepPositionLimit_spaceBoundByWidthAt_internal 2 hafterHeadsValues
      hlimit₂Result
  have hlimit₂Effect (inputLength : ℕ) :
      (setStepPositionLimit 2).effect (afterHeads inputLength) =
        afterLimit₂ inputLength := by
    rw [setStepPositionLimit_effect_local_internal, hafterHeadsHorizon]
    dsimp only [afterHeads, afterLimit₂]
    rw [Function.update_comm (show Work.available ≠ Work.limit₁ by
      decide), Function.update_idem]
  have hlimit₂Seq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [setStepPositionLimit 2] initialSpace afterHeads width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    exact ⟨hlimit₂Space, trivial⟩
  have hthroughLimit₂ : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2]) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm))
      [setStepPositionLimit 2] hthroughHeads (by
        simpa only [hthroughHeadsEffect] using hlimit₂Seq)
  have hthroughLimit₂Effect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          (([emitStepStateFormulas tm, setStepPositionLimit 1] ++
              tapes.map (emitStepHeadTapeFormulas tm)) ++
            [setStepPositionLimit 2])).effect (values inputLength)) =
        afterLimit₂ := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm))).effect
          (values inputLength) = afterHeads inputLength by
            exact congrFun hthroughHeadsEffect inputLength]
    exact hlimit₂Effect inputLength
  have hcellSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (tapes.map (emitStepCellTapeFormulas tm)) initialSpace afterLimit₂
        width := by
    simpa only [tapes, afterLimit₂] using
      emitStepCellTapeList_spaceBoundByWidthAt_formula tm hclean henvelope
  have hthroughCells : BinaryRoutine.SeqListSpaceBoundByWidthAt
      ((([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeFormulas tm)) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      (([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2])
      (tapes.map (emitStepCellTapeFormulas tm)) hthroughLimit₂ (by
        simpa only [hthroughLimit₂Effect] using hcellSeq)
  have hcellEffect (inputLength : ℕ) :
      (BinaryRoutine.seqList
        (tapes.map (emitStepCellTapeFormulas tm))).effect
          (afterLimit₂ inputLength) = afterCells inputLength := by
    simpa only [tapes, afterLimit₂, afterCells] using
      emitStepCellTapeList_effect_formula tm (values inputLength)
        (hclean inputLength)
  have hthroughCellsEffect :
      (fun inputLength =>
        (BinaryRoutine.seqList
          ((([emitStepStateFormulas tm, setStepPositionLimit 1] ++
              tapes.map (emitStepHeadTapeFormulas tm)) ++
            [setStepPositionLimit 2]) ++
            tapes.map (emitStepCellTapeFormulas tm))).effect
              (values inputLength)) = afterCells := by
    funext inputLength
    rw [BinaryRoutine.seqList_append_effect]
    rw [show (BinaryRoutine.seqList
      (([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2])).effect (values inputLength) =
          afterLimit₂ inputLength by
            exact congrFun hthroughLimit₂Effect inputLength]
    exact hcellEffect inputLength
  have hafterCellsLimit (inputLength : ℕ) :
      afterCells inputLength Work.limit₁ ≤ width inputLength := by
    dsimp only [afterCells]
    simpa [Work.limit₁, Work.available] using
      (henvelope inputLength).horizon_add_two_le_internal
  have hclearSpace : BinaryRoutine.SpaceBoundByWidthAt
      (BinaryRoutine.clear Work.limit₁) initialSpace afterCells width :=
    BinaryRoutine.SpaceBoundByWidthAt.clear Work.limit₁ hafterCellsLimit
  have hclearSeq : BinaryRoutine.SeqListSpaceBoundByWidthAt
      [BinaryRoutine.clear Work.limit₁] initialSpace afterCells width := by
    simp only [BinaryRoutine.SeqListSpaceBoundByWidthAt]
    exact ⟨hclearSpace, trivial⟩
  have htotal : BinaryRoutine.SeqListSpaceBoundByWidthAt
      (((([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeFormulas tm)) ++
        [BinaryRoutine.clear Work.limit₁]) initialSpace values width :=
    BinaryRoutine.SeqListSpaceBoundByWidthAt.append
      ((([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        [setStepPositionLimit 2]) ++
        tapes.map (emitStepCellTapeFormulas tm))
      [BinaryRoutine.clear Work.limit₁] hthroughCells (by
        simpa only [hthroughCellsEffect] using hclearSeq)
  unfold emitStepFormulas
  apply BinaryRoutine.SpaceBoundByWidthAt.seqList
  simpa only [tapes, List.append_assoc] using htotal

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
