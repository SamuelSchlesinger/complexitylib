/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs

/-!
# Exact effects of the direct packed-step generator

This file records the pure register effects of the formula and delayed-copy
phases.  The statements deliberately retain the exact numeric schedule sizes:
they do not assume that the saved formula cursor or either gate register is
initially zero.
-/


@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

open scoped BigOperators

/-- Scratch invariant retained while an outer step position limit is active. -/
structure StepPhaseCleanInternal (values : BinaryValues WorkCount) : Prop where
  movedHeadClean : MovedHeadFormulaClean values
  position : values Work.position = 0

private theorem StepClean.phaseClean_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    StepPhaseCleanInternal values :=
  { movedHeadClean := hclean.movedHeadClean
    position := hclean.position }

/-- Restrict the full step-clean invariant to the scratch invariant used by
the step-space proof while an outer position limit is active. -/
theorem StepClean.phaseClean_forSpace_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    StepPhaseCleanInternal values :=
  hclean.phaseClean_internal

private theorem StepClean.caseFormulaClean_forEffect
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    CaseFormulaClean values := by
  have hupdate : Function.update values Work.position 0 = values := by
    funext i
    by_cases hi : i = Work.position
    · subst i
      simp [hclean.position]
    · simp [hi]
  simpa [hupdate] using hclean.movedHeadClean.caseClean

/-- Recover case-formula scratch cleanliness from a fully clean step entry for
the internal step-space proof. -/
theorem StepClean.caseFormulaClean_forSpace_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    CaseFormulaClean values :=
  hclean.caseFormulaClean_forEffect

/-- Recover case-formula scratch cleanliness while an outer step position
limit is active. -/
theorem StepPhaseCleanInternal.caseFormulaClean_forSpace_internal
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values) :
    CaseFormulaClean values := by
  have hupdate : Function.update values Work.position 0 = values := by
    funext i
    by_cases hi : i = Work.position
    · subst i
      simp [hclean.position]
    · simp [hi]
  simpa [hupdate] using hclean.movedHeadClean.caseClean

private theorem MovedHeadFormulaClean.updateOuter_forEffect_internal
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (idx : Fin WorkCount) (value : ℕ)
    (hidx : idx = Work.gateBound ∨ idx = Work.configBase ∨
      idx = Work.gateCount ∨ idx = Work.loop₂) :
    MovedHeadFormulaClean (Function.update values idx value) := by
  rcases hidx with rfl | rfl | rfl | rfl <;>
    refine
      { caseClean := ?_
        limit₂ := ?_
        loop₁ := ?_
        savedOutput := ?_
        direction := ?_
        atomKind := ?_ }
  all_goals
    first
    | exact
        { toReadFormulaClean :=
            { position := by simp [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position]
              loop₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.loop₀] using
                  hclean.caseClean.loop₀
              limit₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.limit₀] using
                  hclean.caseClean.limit₀
              reference₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.reference₀] using
                  hclean.caseClean.reference₀
              reference₁ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.reference₁] using
                  hclean.caseClean.reference₁
              emitCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.emitCounter] using
                  hclean.caseClean.emitCounter
              copyCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.copyCounter] using
                  hclean.caseClean.copyCounter
              multiplyCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.multiplyCounter] using
                  hclean.caseClean.multiplyCounter
              addCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.addCounter] using
                  hclean.caseClean.addCounter
              temporary₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.temporary₀] using
                  hclean.caseClean.temporary₀
              temporary₁ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.temporary₁] using
                  hclean.caseClean.temporary₁
              temporary₂ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.loop₂, Work.position, Work.temporary₂] using
                  hclean.caseClean.temporary₂ }
          loop₃ := by simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂,
              Work.position, Work.loop₃] using hclean.caseClean.loop₃
          temporary₃ := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.loop₂, Work.position, Work.temporary₃] using
                hclean.caseClean.temporary₃
          polynomialScratch := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.loop₂, Work.position, Work.polynomialScratch] using
                hclean.caseClean.polynomialScratch
          tapeIndex := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.loop₂, Work.position, Work.tapeIndex] using
                hclean.caseClean.tapeIndex
          symbolIndex := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.loop₂, Work.position, Work.symbolIndex] using
                hclean.caseClean.symbolIndex }
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂, Work.limit₂]
        using hclean.limit₂
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂, Work.loop₁]
        using hclean.loop₁
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂,
        Work.savedOutput] using hclean.savedOutput
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂, Work.direction]
        using hclean.direction
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂, Work.atomKind]
        using hclean.atomKind

theorem StepClean.updateOuter_forEffect_internal
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (idx : Fin WorkCount) (value : ℕ)
    (hidx : idx = Work.gateBound ∨ idx = Work.configBase ∨
      idx = Work.gateCount ∨ idx = Work.loop₂) :
    StepClean (Function.update values idx value) :=
  { movedHeadClean := hclean.movedHeadClean.updateOuter_forEffect_internal values idx
      value hidx
    position := by rcases hidx with rfl | rfl | rfl | rfl <;>
      simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂,
        Work.position]
        using hclean.position
    limit₁ := by rcases hidx with rfl | rfl | rfl | rfl <;>
      simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₂,
        Work.limit₁]
        using hclean.limit₁ }

private theorem StepPhaseCleanInternal.movedHeadClean_atPosition_internal
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (position : ℕ) :
    MovedHeadFormulaClean (Function.update values Work.position position) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hupdate :
        Function.update (Function.update values Work.position position)
            Work.position 0 =
          Function.update values Work.position 0 := by
      funext i
      by_cases hi : i = Work.position <;> simp [hi]
    simpa [hupdate] using hclean.movedHeadClean.caseClean
  · simpa [Work.position, Work.limit₂] using hclean.movedHeadClean.limit₂
  · simpa [Work.position, Work.loop₁] using hclean.movedHeadClean.loop₁
  · simpa [Work.position, Work.savedOutput] using
      hclean.movedHeadClean.savedOutput
  · simpa [Work.position, Work.direction] using
      hclean.movedHeadClean.direction
  · simpa [Work.position, Work.atomKind] using hclean.movedHeadClean.atomKind

/-- Recover moved-head scratch cleanliness at a position selected by an outer
step loop. -/
theorem StepPhaseCleanInternal.movedHeadClean_atPosition_forSpace_internal
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (position : ℕ) :
    MovedHeadFormulaClean (Function.update values Work.position position) :=
  hclean.movedHeadClean_atPosition_internal position

private theorem update_available_preserves_caseClean
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (value : ℕ) :
    CaseFormulaClean (Function.update values Work.available value) := by
  let updated := Function.update values Work.available value
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
      temporary₂ := ?_
      loop₃ := ?_
      temporary₃ := ?_
      polynomialScratch := ?_
      tapeIndex := ?_
      symbolIndex := ?_ }
  all_goals
    first
    | simpa [updated, Function.update_apply, Work.available] using! hclean.position
    | simpa [updated, Function.update_apply, Work.available] using! hclean.loop₀
    | simpa [updated, Function.update_apply, Work.available] using! hclean.limit₀
    | simpa [updated, Function.update_apply, Work.available] using! hclean.reference₀
    | simpa [updated, Function.update_apply, Work.available] using! hclean.reference₁
    | simpa [updated, Function.update_apply, Work.available] using! hclean.emitCounter
    | simpa [updated, Function.update_apply, Work.available] using! hclean.copyCounter
    | simpa [updated, Function.update_apply, Work.available] using! hclean.multiplyCounter
    | simpa [updated, Function.update_apply, Work.available] using! hclean.addCounter
    | simpa [updated, Function.update_apply, Work.available] using! hclean.temporary₀
    | simpa [updated, Function.update_apply, Work.available] using! hclean.temporary₁
    | simpa [updated, Function.update_apply, Work.available] using! hclean.temporary₂
    | simpa [updated, Function.update_apply, Work.available] using! hclean.loop₃
    | simpa [updated, Function.update_apply, Work.available] using! hclean.temporary₃
    | simpa [updated, Function.update_apply, Work.available] using! hclean.polynomialScratch
    | simpa [updated, Function.update_apply, Work.available] using! hclean.tapeIndex
    | simpa [updated, Function.update_apply, Work.available] using! hclean.symbolIndex

private theorem update_available_preserves_movedClean
    {values : BinaryValues WorkCount}
    (hclean : MovedHeadFormulaClean values) (value : ℕ) :
    MovedHeadFormulaClean (Function.update values Work.available value) := by
  have hne : Work.position ≠ Work.available := by
    simp [Work.position, Work.available]
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · rw [Function.update_comm hne.symm]
    exact update_available_preserves_caseClean hclean.caseClean value
  all_goals
    first
    | simpa [Work.available, Work.limit₂] using! hclean.limit₂
    | simpa [Work.available, Work.loop₁] using! hclean.loop₁
    | simpa [Work.available, Work.savedOutput] using! hclean.savedOutput
    | simpa [Work.available, Work.direction] using! hclean.direction
    | simpa [Work.available, Work.atomKind] using! hclean.atomKind

theorem update_available_preserves_stepClean_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) (value : ℕ) :
    StepClean (Function.update values Work.available value) := by
  let updated := Function.update values Work.available value
  refine { movedHeadClean := ?_, position := ?_, limit₁ := ?_ }
  · refine
      { caseClean := ?_
        limit₂ := ?_
        loop₁ := ?_
        savedOutput := ?_
        direction := ?_
        atomKind := ?_ }
    · have hpositionUpdate :
          Function.update updated Work.position 0 =
            Function.update
              (Function.update values Work.position 0) Work.available value := by
          funext i
          by_cases hposition : i = Work.position
          · subst i
            simp [updated, Work.position, Work.available]
          · by_cases havailable : i = Work.available
            · subst i
              simp [updated, Work.position, Work.available] at hposition ⊢
            · simp [updated, hposition, havailable]
      rw [hpositionUpdate]
      exact update_available_preserves_caseClean
        hclean.movedHeadClean.caseClean value
    all_goals
      first
      | simpa [updated, Function.update_apply, Work.available, Work.limit₂]
          using hclean.movedHeadClean.limit₂
      | simpa [updated, Function.update_apply, Work.available, Work.loop₁]
          using hclean.movedHeadClean.loop₁
      | simpa [updated, Function.update_apply, Work.available, Work.savedOutput]
          using hclean.movedHeadClean.savedOutput
      | simpa [updated, Function.update_apply, Work.available, Work.direction]
          using hclean.movedHeadClean.direction
      | simpa [updated, Function.update_apply, Work.available, Work.atomKind]
          using hclean.movedHeadClean.atomKind
  · simpa [updated, Function.update_apply, Work.available, Work.position]
      using hclean.position
  · simpa [updated, Function.update_apply, Work.available, Work.limit₁]
      using hclean.limit₁

private theorem update_available_preserves_phaseClean
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (value : ℕ) :
    StepPhaseCleanInternal (Function.update values Work.available value) :=
  { movedHeadClean := update_available_preserves_movedClean
      hclean.movedHeadClean value
    position := by
      simpa [Work.available, Work.position] using hclean.position }

/-- Advancing the formula frontier preserves the scratch invariant used by the
step-space proof. -/
theorem update_available_preserves_phaseClean_forSpace_internal
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (value : ℕ) :
    StepPhaseCleanInternal (Function.update values Work.available value) :=
  update_available_preserves_phaseClean hclean value

private theorem update_limit₁_preserves_caseClean
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (value : ℕ) :
    CaseFormulaClean (Function.update values Work.limit₁ value) := by
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
      temporary₂ := ?_
      loop₃ := ?_
      temporary₃ := ?_
      polynomialScratch := ?_
      tapeIndex := ?_
      symbolIndex := ?_ }
  all_goals
    first
    | simpa [Work.limit₁] using! hclean.position
    | simpa [Work.limit₁] using! hclean.loop₀
    | simpa [Work.limit₁] using! hclean.limit₀
    | simpa [Work.limit₁] using! hclean.reference₀
    | simpa [Work.limit₁] using! hclean.reference₁
    | simpa [Work.limit₁] using! hclean.emitCounter
    | simpa [Work.limit₁] using! hclean.copyCounter
    | simpa [Work.limit₁] using! hclean.multiplyCounter
    | simpa [Work.limit₁] using! hclean.addCounter
    | simpa [Work.limit₁] using! hclean.temporary₀
    | simpa [Work.limit₁] using! hclean.temporary₁
    | simpa [Work.limit₁] using! hclean.temporary₂
    | simpa [Work.limit₁] using! hclean.loop₃
    | simpa [Work.limit₁] using! hclean.temporary₃
    | simpa [Work.limit₁] using! hclean.polynomialScratch
    | simpa [Work.limit₁] using! hclean.tapeIndex
    | simpa [Work.limit₁] using! hclean.symbolIndex

theorem update_limit₁_preserves_phaseClean_internal
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (value : ℕ) :
    StepPhaseCleanInternal (Function.update values Work.limit₁ value) := by
  refine
    { movedHeadClean := ?_
      position := ?_ }
  · refine
      { caseClean := ?_
        limit₂ := ?_
        loop₁ := ?_
        savedOutput := ?_
        direction := ?_
        atomKind := ?_ }
    · have hne : Work.position ≠ Work.limit₁ := by
        simp [Work.position, Work.limit₁]
      rw [Function.update_comm hne.symm]
      exact update_limit₁_preserves_caseClean hclean.movedHeadClean.caseClean
        value
    all_goals
      first
      | simpa [Work.limit₁] using! hclean.movedHeadClean.limit₂
      | simpa [Work.limit₁] using! hclean.movedHeadClean.loop₁
      | simpa [Work.limit₁] using! hclean.movedHeadClean.savedOutput
      | simpa [Work.limit₁] using! hclean.movedHeadClean.direction
      | simpa [Work.limit₁] using! hclean.movedHeadClean.atomKind
  · simpa [Work.limit₁, Work.position] using hclean.position

private theorem seqList_stateFormulas_effect
    (tm : NTM k) (states : List tm.Q) (values : BinaryValues WorkCount)
    (hclean : CaseFormulaClean values) :
    (BinaryRoutine.seqList (states.map (emitNextStateFormula tm))).effect
        values =
      Function.update values Work.available
        (values Work.available +
          (states.map fun state =>
            nextStateFormulaScheduleSize (transitionCases tm).length k
              (values Work.horizon)
              (effectCaseSelectedAt tm fun effect =>
                decide (effect.nextState = state))
              (effectCaseChoiceAt tm)).sum) := by
  induction states generalizing values with
  | nil =>
      funext i
      by_cases hi : i = Work.available <;>
        simp [BinaryRoutine.seqList, BinaryRoutine.identity,
          BinaryRoutine.emitBits, hi]
  | cons state states ih =>
      rw [List.map_cons, BinaryRoutine.seqList, BinaryRoutine.seq]
      change (BinaryRoutine.seqList (states.map (emitNextStateFormula tm))).effect
        ((emitNextStateFormula tm state).effect values) = _
      rw [Complexity.CircuitUnrolling.Serializer.DirectGenerator.emitNextStateFormula_effect
        tm state values hclean]
      rw [ih _ (update_available_preserves_caseClean hclean _)]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp [Work.available, Work.horizon]
        omega
      · simp [Work.available] at hi
        simp [Work.available, Work.horizon, hi]

/-- Exact state-formula phase effect. -/
theorem emitStepStateFormulas_effect_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepStateFormulas tm).effect values =
      Function.update values Work.available
        (values Work.available +
          ((List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
              let state := (Fintype.equivFin tm.Q).symm stateIndex
              nextStateFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon)
                (effectCaseSelectedAt tm fun effect =>
                  decide (effect.nextState = state))
                (effectCaseChoiceAt tm)).sum)) := by
  unfold emitStepStateFormulas
  rw [show (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      emitNextStateFormula tm ((Fintype.equivFin tm.Q).symm stateIndex)) =
      (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
        (Fintype.equivFin tm.Q).symm stateIndex).map
          (emitNextStateFormula tm) by
        apply List.ext_getElem
        · simp
        · intro i hleft hright
          simp]
  simpa using! seqList_stateFormulas_effect tm
      (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      (Fintype.equivFin tm.Q).symm stateIndex) values
      hclean.caseFormulaClean_forEffect

private theorem MovedHeadFormulaClean.tapeIndex_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.tapeIndex = 0 := by
  have h := hclean.caseClean.tapeIndex
  simpa [Work.position, Work.tapeIndex] using h

private theorem MovedHeadFormulaClean.symbolIndex_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.symbolIndex = 0 := by
  have h := hclean.caseClean.symbolIndex
  simpa [Work.position, Work.symbolIndex] using h

private theorem MovedHeadFormulaClean.temporary₀_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.temporary₀ = 0 := by
  have h := hclean.caseClean.temporary₀
  simpa [Work.position, Work.temporary₀] using h

private theorem MovedHeadFormulaClean.temporary₁_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.temporary₁ = 0 := by
  have h := hclean.caseClean.temporary₁
  simpa [Work.position, Work.temporary₁] using h

private theorem MovedHeadFormulaClean.temporary₂_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.temporary₂ = 0 := by
  have h := hclean.caseClean.temporary₂
  simpa [Work.position, Work.temporary₂] using h

private theorem MovedHeadFormulaClean.reference₀_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.reference₀ = 0 := by
  have h := hclean.caseClean.reference₀
  simpa [Work.position, Work.reference₀] using h

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

private theorem seqList_nextCellCopies_effect
    (stateCount tapeCount tapeIndex : ℕ) (symbols : List Γ)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    (BinaryRoutine.seqList (symbols.map fun symbol =>
        emitNextCellCopy stateCount tapeCount tapeIndex
          (CircuitUnrolling.symbolIndex symbol))).effect values =
      Function.update values Work.available
        (values Work.available + symbols.length) := by
  induction symbols generalizing values with
  | nil =>
      funext i
      by_cases hi : i = Work.available <;>
        simp [BinaryRoutine.seqList, BinaryRoutine.identity,
          BinaryRoutine.emitBits, hi]
  | cons symbol symbols ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList (symbols.map fun symbol =>
          emitNextCellCopy stateCount tapeCount tapeIndex
            (CircuitUnrolling.symbolIndex symbol))).effect
        ((emitNextCellCopy stateCount tapeCount tapeIndex
          (CircuitUnrolling.symbolIndex symbol)).effect values) = _
      rw [emitNextCellCopy_effect _ _ _ _ values hclean.tapeIndex_internal
        hclean.symbolIndex_internal hclean.temporary₀_internal
        hclean.temporary₁_internal hclean.temporary₂_internal
        hclean.reference₀_internal]
      rw [ih _ (update_available_preserves_movedClean hclean _)]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp
        omega
      · simp [hi]

/-- The four immutable-cell formulas restore scratch and add four gates. -/
theorem emitStepImmutableCellPosition_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values) :
    (emitStepImmutableCellPosition tm tape).effect values =
      Function.update values Work.available (values Work.available + 4) := by
  unfold emitStepImmutableCellPosition
  rw [show (List.ofFn fun symbolIndex : Fin 4 =>
      emitNextCellCopy (Fintype.card tm.Q) (k + 2) tape.index
        (symbolEquiv.symm symbolIndex |>
          CircuitUnrolling.symbolIndex)) =
      (List.ofFn fun symbolIndex : Fin 4 =>
        symbolEquiv.symm symbolIndex).map (fun symbol =>
          emitNextCellCopy (Fintype.card tm.Q) (k + 2) tape.index
            (CircuitUnrolling.symbolIndex symbol)) by
        apply List.ext_getElem
        · simp
        · intro i hleft hright
          simp]
  simpa using seqList_nextCellCopies_effect (Fintype.card tm.Q) (k + 2)
    tape.index (List.ofFn fun symbolIndex : Fin 4 =>
      symbolEquiv.symm symbolIndex) values hclean

private theorem MovedHeadFormulaClean.writtenCellClean_internal
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    WrittenCellFormulaClean values := by
  exact
    { caseClean := hclean.caseClean
      limit₂ := hclean.limit₂
      savedOutput := hclean.savedOutput }

private theorem seqList_writableCellFormulas_effect
    (tm : NTM k) (tape : WritableSlot k) (symbols : List Γ)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    (BinaryRoutine.seqList (symbols.map fun symbol =>
        BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
          (emitNextWrittenCellFormula tm tape symbol))).effect values =
      Function.update values Work.available
        (values Work.available +
          (symbols.map fun symbol =>
            if values Work.position = 0 then 1 else
              nextWrittenCellFormulaScheduleSize
                (transitionCases tm).length k (values Work.horizon)
                (writtenCellEffectSelectedAt tm tape symbol)
                (effectCaseChoiceAt tm)).sum) := by
  induction symbols generalizing values with
  | nil =>
      funext i
      by_cases hi : i = Work.available <;>
        simp [BinaryRoutine.seqList, BinaryRoutine.identity,
          BinaryRoutine.emitBits, hi]
  | cons symbol symbols ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList (symbols.map fun symbol =>
          BinaryRoutine.branchZero Work.position
            (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
            (emitNextWrittenCellFormula tm tape symbol))).effect
        ((BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
          (emitNextWrittenCellFormula tm tape symbol)).effect values) = _
      by_cases hposition : values Work.position = 0
      · have hposition' : values 30 = 0 := by
          simpa [Work.position] using hposition
        rw [show (BinaryRoutine.branchZero Work.position
            (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
            (emitNextWrittenCellFormula tm tape symbol)).effect values =
            (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index
              (CircuitUnrolling.symbolIndex symbol)).effect values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [emitNextCellCopy_effect _ _ _ _ values hclean.tapeIndex_internal
          hclean.symbolIndex_internal hclean.temporary₀_internal
          hclean.temporary₁_internal hclean.temporary₂_internal
          hclean.reference₀_internal]
        rw [ih _ (update_available_preserves_movedClean hclean _)]
        funext i
        by_cases hi : i = Work.available
        · subst i
          simp [Work.available, Work.position, hposition']
          omega
        · simp [Work.available] at hi
          simp [Work.available, Work.position, hposition', hi]
      · have hposition' : values 30 ≠ 0 := by
          simpa [Work.position] using hposition
        rw [show (BinaryRoutine.branchZero Work.position
            (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
            (emitNextWrittenCellFormula tm tape symbol)).effect values =
            (emitNextWrittenCellFormula tm tape symbol).effect values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [emitNextWrittenCellFormula_effect tm tape symbol values
          hclean.writtenCellClean_internal]
        rw [ih _ (update_available_preserves_movedClean hclean _)]
        funext i
        by_cases hi : i = Work.available
        · subst i
          simp [Work.available, Work.position, Work.horizon, hposition']
          omega
        · simp [Work.available] at hi
          simp [Work.available, Work.position, Work.horizon, hposition', hi]

/-- Exact four-symbol writable-cell phase effect at the current position. -/
theorem emitStepWritableCellPosition_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values) :
    (emitStepWritableCellPosition tm tape).effect values =
      Function.update values Work.available
        (values Work.available +
          ((List.ofFn fun symbolIndex : Fin 4 =>
            let symbol := symbolEquiv.symm symbolIndex
            if values Work.position = 0 then 1 else
              nextWrittenCellFormulaScheduleSize
                (transitionCases tm).length k (values Work.horizon)
                (writtenCellEffectSelectedAt tm tape symbol)
                (effectCaseChoiceAt tm)).sum)) := by
  unfold emitStepWritableCellPosition
  rw [show (List.ofFn fun symbolIndex : Fin 4 =>
      let symbol := symbolEquiv.symm symbolIndex
      BinaryRoutine.branchZero Work.position
        (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
        (emitNextWrittenCellFormula tm tape symbol)) =
      (List.ofFn fun symbolIndex : Fin 4 =>
        symbolEquiv.symm symbolIndex).map fun symbol =>
          BinaryRoutine.branchZero Work.position
            (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
              tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
            (emitNextWrittenCellFormula tm tape symbol) by
        apply List.ext_getElem
        · simp
        · intro i hleft hright
          simp]
  simpa using seqList_writableCellFormulas_effect tm tape
    (List.ofFn fun symbolIndex : Fin 4 => symbolEquiv.symm symbolIndex)
      values hclean

private theorem headFormula_binaryForValues_effect
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values) (hhorizon : 0 < values Work.horizon)
    (count : ℕ) (hcount : count ≤ values Work.horizon + 1) :
    BinaryRoutine.binaryForValues (emitNextHeadFormula tm tape) Work.position
        values count =
      Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + count *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) := by
  induction count with
  | zero =>
      have hpositionZero : values 30 = 0 := by
        simpa [Work.position] using hclean.position
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [BinaryRoutine.binaryForValues, Work.position, Work.available,
          hpositionZero]
      · by_cases havailable : i = Work.available
        · subst i
          simp [BinaryRoutine.binaryForValues, Work.position, Work.available]
        · simp [BinaryRoutine.binaryForValues, hposition, havailable]
  | succ count ih =>
      have hcount' : count ≤ values Work.horizon + 1 := by omega
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        ih hcount']
      let current := Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + count *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm))
      have hcurrentClean : MovedHeadFormulaClean current := by
        have hmoved :=
          (update_available_preserves_phaseClean hclean
            (values Work.available + count *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                (effectCaseChoiceAt tm))).movedHeadClean_atPosition_internal
              count
        have hne : Work.position ≠ Work.available := by
          simp [Work.position, Work.available]
        simpa [current, Function.update_comm hne] using hmoved
      have hcurrentHorizon : current Work.horizon = values Work.horizon := by
        simp [current, Work.position, Work.available, Work.horizon]
      have hcurrentPosition : current Work.position = count := by
        simp [current, Work.position, Work.available]
      have htarget : current Work.position ≤ current Work.horizon := by
        rw [hcurrentPosition, hcurrentHorizon]
        omega
      rw [emitNextHeadFormula_effect tm tape current hcurrentClean (by
        simpa [hcurrentHorizon] using hhorizon) htarget]
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [current, Work.position,
          Work.available, Work.horizon]
      · by_cases havailable : i = Work.available
        · subst i
          simp [current, Work.position,
            Work.available, Work.horizon]
          ring
        · simp [Work.position] at hposition
          simp [Work.available] at havailable
          simp [current, hposition, havailable, Work.position, Work.available,
            Work.horizon]

/-- Exact trajectory of a prefix of one tape's head-formula loop, exposed only
for the internal step-space proof. -/
theorem headFormula_binaryForValues_effect_forSpace_internal
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values) (hhorizon : 0 < values Work.horizon)
    (count : ℕ) (hcount : count ≤ values Work.horizon + 1) :
    BinaryRoutine.binaryForValues (emitNextHeadFormula tm tape) Work.position
        values count =
      Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + count *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) :=
  headFormula_binaryForValues_effect tm tape values hclean hhorizon count hcount

/-- Exact effect of the complete head-position loop for one tape. -/
theorem emitStepHeadTapeFormulas_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values) (hhorizon : 0 < values Work.horizon)
    (hlimit : values Work.limit₁ = values Work.horizon + 1) :
    (emitStepHeadTapeFormulas tm tape).effect values =
      Function.update values Work.available
        (values Work.available + (values Work.horizon + 1) *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)) := by
  rw [emitStepHeadTapeFormulas, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.position).effect
    (BinaryRoutine.binaryForValues (emitNextHeadFormula tm tape) Work.position
      values (values Work.limit₁ - values Work.position)) = _
  rw [hclean.position, hlimit, Nat.sub_zero,
    headFormula_binaryForValues_effect tm tape values hclean hhorizon _ (by
      omega)]
  funext i
  have hpositionZero : values 30 = 0 := by
    simpa [Work.position] using hclean.position
  by_cases hposition : i = Work.position
  · subst i
    simp [BinaryRoutine.clear, Work.position, Work.available, hpositionZero]
  · simp [Work.position] at hposition
    by_cases havailable : i = Work.available
    · subst i
      simp [BinaryRoutine.clear, Work.position, Work.available]
    · simp [Work.available] at havailable
      simp [BinaryRoutine.clear, Work.position, Work.available, hposition,
        havailable]

/-- Exact formula-gate count for one tape at one numeric cell position. -/
noncomputable def stepCellPositionEffectSizeInternal (tm : NTM k)
    (tape : TapeSlot k) (T position : ℕ) : ℕ :=
  match tape with
  | .input => 4
  | .work index =>
      (List.ofFn fun symbolIndex : Fin 4 =>
        let symbol := symbolEquiv.symm symbolIndex
        if position = 0 then 1 else
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
            (writtenCellEffectSelectedAt tm (.work index) symbol)
            (effectCaseChoiceAt tm)).sum
  | .output =>
      (List.ofFn fun symbolIndex : Fin 4 =>
        let symbol := symbolEquiv.symm symbolIndex
        if position = 0 then 1 else
          nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
            (writtenCellEffectSelectedAt tm .output symbol)
            (effectCaseChoiceAt tm)).sum

private theorem cellFormulaBody_effect (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    (match tape with
      | .input => emitStepImmutableCellPosition tm .input
      | .work index => emitStepWritableCellPosition tm (.work index)
      | .output => emitStepWritableCellPosition tm .output).effect values =
      Function.update values Work.available
        (values Work.available + stepCellPositionEffectSizeInternal tm tape
          (values Work.horizon) (values Work.position)) := by
  cases tape with
  | input =>
      simpa [stepCellPositionEffectSizeInternal] using
        emitStepImmutableCellPosition_effect_internal tm .input values
          hclean
  | work index =>
      simpa [stepCellPositionEffectSizeInternal] using
        emitStepWritableCellPosition_effect_internal tm (.work index) values
          hclean
  | output =>
      simpa [stepCellPositionEffectSizeInternal] using
        emitStepWritableCellPosition_effect_internal tm .output values
          hclean

private theorem binaryForValues_positionSize_effect
    (body : BinaryRoutine WorkCount) (sizeAt : ℕ → ℕ)
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values)
    (hbody : ∀ current : BinaryValues WorkCount, MovedHeadFormulaClean current →
      current Work.horizon = values Work.horizon →
      body.effect current = Function.update current Work.available
        (current Work.available + sizeAt (current Work.position)))
    (count : ℕ) :
    BinaryRoutine.binaryForValues body Work.position values count =
      Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + prefixSize sizeAt count) := by
  induction count with
  | zero =>
      have hpositionZero : values 30 = 0 := by
        simpa [Work.position] using hclean.position
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [BinaryRoutine.binaryForValues, prefixSize, Work.position,
          Work.available, hpositionZero]
      · by_cases havailable : i = Work.available
        · subst i
          simp [BinaryRoutine.binaryForValues, prefixSize, Work.position,
            Work.available]
        · simp [BinaryRoutine.binaryForValues, prefixSize, hposition,
            havailable]
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep, ih]
      let current := Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + prefixSize sizeAt count)
      have hcurrentClean : MovedHeadFormulaClean current := by
        have havailable := update_available_preserves_phaseClean hclean
          (values Work.available + prefixSize sizeAt count)
        have hne : Work.position ≠ Work.available := by
          simp [Work.position, Work.available]
        have hmoved := havailable.movedHeadClean_atPosition_internal count
        simpa [current, Function.update_comm hne] using hmoved
      have hcurrentHorizon : current Work.horizon = values Work.horizon := by
        simp [current, Work.position, Work.available, Work.horizon]
      rw [hbody current hcurrentClean hcurrentHorizon]
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [current, prefixSize, Work.position, Work.available]
      · by_cases havailable : i = Work.available
        · subst i
          simp [current, prefixSize, Work.position, Work.available]
          omega
        · simp [Work.position] at hposition
          simp [Work.available] at havailable
          simp [current, prefixSize, hposition, havailable, Work.position,
            Work.available]

private theorem cellFormula_binaryForValues_effect
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values) (count : ℕ) :
    BinaryRoutine.binaryForValues
        (match tape with
          | .input => emitStepImmutableCellPosition tm .input
          | .work index => emitStepWritableCellPosition tm (.work index)
          | .output => emitStepWritableCellPosition tm .output)
        Work.position values count =
      Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + prefixSize
          (stepCellPositionEffectSizeInternal tm tape (values Work.horizon)) count) := by
  apply binaryForValues_positionSize_effect _ _ values hclean
  intro current hcurrent hcurrentHorizon
  rw [← hcurrentHorizon]
  simpa [Work.position, Work.horizon, Work.available] using
    cellFormulaBody_effect tm tape current hcurrent

/-- Exact trajectory of a prefix of one tape's cell-formula loop, exposed only
for the internal step-space proof. -/
theorem cellFormula_binaryForValues_effect_forSpace_internal
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values) (count : ℕ) :
    BinaryRoutine.binaryForValues
        (match tape with
          | .input => emitStepImmutableCellPosition tm .input
          | .work index => emitStepWritableCellPosition tm (.work index)
          | .output => emitStepWritableCellPosition tm .output)
        Work.position values count =
      Function.update
        (Function.update values Work.position count) Work.available
        (values Work.available + prefixSize
          (stepCellPositionEffectSizeInternal tm tape (values Work.horizon)) count) :=
  cellFormula_binaryForValues_effect tm tape values hclean count

private theorem clearPosition_after_position_available
    (values : BinaryValues WorkCount) (positionValue availableValue : ℕ)
    (hposition : values Work.position = 0) :
    (BinaryRoutine.clear Work.position).effect
        (Function.update (Function.update values Work.position positionValue)
          Work.available availableValue) =
      Function.update values Work.available availableValue := by
  have hposition' : values 30 = 0 := by
    simpa [Work.position] using hposition
  funext i
  by_cases hiposition : i = Work.position
  · subst i
    simp [BinaryRoutine.clear, Work.position, Work.available, hposition']
  · by_cases hiavailable : i = Work.available
    · subst i
      simp [BinaryRoutine.clear, Work.position, Work.available]
    · simp [BinaryRoutine.clear, hiposition, hiavailable]

/-- Exact effect of all cell-position formulas for one named tape. -/
theorem emitStepCellTapeFormulas_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : StepPhaseCleanInternal values)
    (hlimit : values Work.limit₁ = values Work.horizon + 2) :
    (emitStepCellTapeFormulas tm tape).effect values =
      Function.update values Work.available
        (values Work.available + prefixSize
          (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
          (values Work.horizon + 2)) := by
  cases tape with
  | input =>
      rw [emitStepCellTapeFormulas, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues (emitStepImmutableCellPosition tm .input)
          Work.position values
            (values Work.limit₁ - values Work.position)) = _
      rw [hclean.position, hlimit, Nat.sub_zero,
        cellFormula_binaryForValues_effect tm .input values hclean]
      exact clearPosition_after_position_available values _ _ hclean.position
  | work index =>
      rw [emitStepCellTapeFormulas, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues
          (emitStepWritableCellPosition tm (.work index)) Work.position values
            (values Work.limit₁ - values Work.position)) = _
      rw [hclean.position, hlimit, Nat.sub_zero,
        cellFormula_binaryForValues_effect tm (.work index) values hclean]
      exact clearPosition_after_position_available values _ _ hclean.position
  | output =>
      rw [emitStepCellTapeFormulas, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues (emitStepWritableCellPosition tm .output)
          Work.position values
            (values Work.limit₁ - values Work.position)) = _
      rw [hclean.position, hlimit, Nat.sub_zero,
        cellFormula_binaryForValues_effect tm .output values hclean]
      exact clearPosition_after_position_available values _ _ hclean.position

/-- Exact total size of the state-formula prefix. -/
noncomputable def stepStateFormulasEffectSizeInternal (tm : NTM k) (T : ℕ) : ℕ :=
  (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
    let state := (Fintype.equivFin tm.Q).symm stateIndex
    nextStateFormulaScheduleSize (transitionCases tm).length k T
      (effectCaseSelectedAt tm fun effect => decide (effect.nextState = state))
      (effectCaseChoiceAt tm)).sum

/-- Exact total size of all head-formula blocks. -/
noncomputable def stepHeadFormulasEffectSizeInternal (tm : NTM k) (T : ℕ) : ℕ :=
  ((List.ofFn (tapeSlotEquiv k).symm).map fun tape =>
    (T + 1) * nextHeadFormulaScheduleSize (transitionCases tm).length k T
      (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)).sum

/-- Exact total size of all cell-formula blocks. -/
noncomputable def stepCellFormulasEffectSizeInternal (tm : NTM k) (T : ℕ) : ℕ :=
  ((List.ofFn (tapeSlotEquiv k).symm).map fun tape =>
    prefixSize (stepCellPositionEffectSizeInternal tm tape T) (T + 2)).sum

/-- Exact complete forward formula-stream gate count. -/
noncomputable def stepFormulasEffectSizeInternal (tm : NTM k) (T : ℕ) : ℕ :=
  stepStateFormulasEffectSizeInternal tm T + stepHeadFormulasEffectSizeInternal tm T +
    stepCellFormulasEffectSizeInternal tm T

private theorem seqList_append_effect
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).effect values =
      (BinaryRoutine.seqList second).effect
        ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil => rfl
  | cons routine routines ih =>
      rw [List.cons_append, BinaryRoutine.seqList, BinaryRoutine.seq]
      change (BinaryRoutine.seqList (routines ++ second)).effect
        (routine.effect values) = _
      exact ih (routine.effect values)

private theorem seqList_headTapeFormulas_effect
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values)
    (hhorizon : 0 < values Work.horizon)
    (hlimit : values Work.limit₁ = values Work.horizon + 1) :
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeFormulas tm))).effect
        values =
      Function.update values Work.available
        (values Work.available +
          (tapes.map fun tape =>
            (values Work.horizon + 1) *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                (effectCaseChoiceAt tm)).sum) := by
  induction tapes generalizing values with
  | nil =>
      funext i
      by_cases hi : i = Work.available <;>
        simp [BinaryRoutine.seqList, BinaryRoutine.identity,
          BinaryRoutine.emitBits, hi]
  | cons tape tapes ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList
        (tapes.map (emitStepHeadTapeFormulas tm))).effect
          ((emitStepHeadTapeFormulas tm tape).effect values) = _
      rw [emitStepHeadTapeFormulas_effect_internal tm tape values hclean
        hhorizon hlimit]
      have hnextClean := update_available_preserves_phaseClean hclean
        (values Work.available + (values Work.horizon + 1) *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm))
      have hnextHorizon :
          (Function.update values Work.available
            (values Work.available + (values Work.horizon + 1) *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                (effectCaseChoiceAt tm))) Work.horizon =
            values Work.horizon := by
        simp [Work.available, Work.horizon]
      rw [ih _ hnextClean (by simpa [hnextHorizon] using hhorizon) (by
        simpa [Work.available, Work.limit₁, Work.horizon] using hlimit)]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp [Work.available, Work.horizon]
        omega
      · simp [Work.available] at hi
        simp [Work.available, Work.horizon, hi]

/-- Exact endpoint of a finite head-tape formula prefix, exposed to the
step-space proof without duplicating its phase-invariant induction. -/
theorem seqList_headTapeFormulas_effect_forSpace_internal
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values)
    (hhorizon : 0 < values Work.horizon)
    (hlimit : values Work.limit₁ = values Work.horizon + 1) :
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeFormulas tm))).effect
        values =
      Function.update values Work.available
        (values Work.available +
          (tapes.map fun tape =>
            (values Work.horizon + 1) *
              nextHeadFormulaScheduleSize (transitionCases tm).length k
                (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                (effectCaseChoiceAt tm)).sum) :=
  seqList_headTapeFormulas_effect tm tapes values hclean hhorizon hlimit

private theorem seqList_cellTapeFormulas_effect
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values)
    (hlimit : values Work.limit₁ = values Work.horizon + 2) :
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
        values =
      Function.update values Work.available
        (values Work.available +
          (tapes.map fun tape =>
            prefixSize
              (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
              (values Work.horizon + 2)).sum) := by
  induction tapes generalizing values with
  | nil =>
      funext i
      by_cases hi : i = Work.available <;>
        simp [BinaryRoutine.seqList, BinaryRoutine.identity,
          BinaryRoutine.emitBits, hi]
  | cons tape tapes ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList
        (tapes.map (emitStepCellTapeFormulas tm))).effect
          ((emitStepCellTapeFormulas tm tape).effect values) = _
      rw [emitStepCellTapeFormulas_effect_internal tm tape values hclean hlimit]
      have hnextClean := update_available_preserves_phaseClean hclean
        (values Work.available + prefixSize
          (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
          (values Work.horizon + 2))
      rw [ih _ hnextClean (by
        simpa [Work.available, Work.limit₁, Work.horizon] using hlimit)]
      funext i
      by_cases hi : i = Work.available
      · subst i
        simp [Work.available, Work.horizon]
        omega
      · simp [Work.available] at hi
        simp [Work.available, Work.horizon, hi]

/-- Exact endpoint of a finite cell-tape formula prefix, exposed to the
step-space proof without duplicating its phase-invariant induction. -/
theorem seqList_cellTapeFormulas_effect_forSpace_internal
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values)
    (hlimit : values Work.limit₁ = values Work.horizon + 2) :
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
        values =
      Function.update values Work.available
        (values Work.available +
          (tapes.map fun tape =>
            prefixSize
              (stepCellPositionEffectSizeInternal tm tape
                (values Work.horizon))
              (values Work.horizon + 2)).sum) :=
  seqList_cellTapeFormulas_effect tm tapes values hclean hlimit

theorem setStepPositionLimit_effect_local_internal (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (setStepPositionLimit extra).effect values =
      Function.update values Work.limit₁ (values Work.horizon + extra) := by
  simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst]

/-- The complete forward formula phase restores its outer counters and
advances exactly by the explicit formula schedule size. -/
theorem emitStepFormulas_effect_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStepFormulas tm).effect values =
      Function.update values Work.available
        (values Work.available +
          stepFormulasEffectSizeInternal tm (values Work.horizon)) := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  have hschedule :
      [emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm) ++
          [setStepPositionLimit 2] ++
          tapes.map (emitStepCellTapeFormulas tm) ++
          [BinaryRoutine.clear Work.limit₁] =
        ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeFormulas tm)) ++
        ([setStepPositionLimit 2] ++
          tapes.map (emitStepCellTapeFormulas tm)) ++
        [BinaryRoutine.clear Work.limit₁] := by
    simp [List.append_assoc]
  rw [emitStepFormulas]
  change (BinaryRoutine.seqList
    ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
      tapes.map (emitStepHeadTapeFormulas tm) ++
      [setStepPositionLimit 2] ++
      tapes.map (emitStepCellTapeFormulas tm) ++
      [BinaryRoutine.clear Work.limit₁])).effect values = _
  rw [hschedule]
  rw [seqList_append_effect,
    seqList_append_effect
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm)),
    seqList_append_effect
      [emitStepStateFormulas tm, setStepPositionLimit 1],
    seqList_append_effect [setStepPositionLimit 2]]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeFormulas tm))).effect
            ((setStepPositionLimit 1).effect
              ((emitStepStateFormulas tm).effect values))))) = _
  rw [emitStepStateFormulas_effect_internal tm values hclean]
  let afterState := Function.update values Work.available
    (values Work.available + stepStateFormulasEffectSizeInternal tm
      (values Work.horizon))
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeFormulas tm))).effect
            ((setStepPositionLimit 1).effect afterState)))) = _
  nth_rewrite 2 [setStepPositionLimit_effect_local_internal]
  let afterLimit₁ := Function.update afterState Work.limit₁
    (afterState Work.horizon + 1)
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeFormulas tm))).effect afterLimit₁))) = _
  have hafterStatePhase : StepPhaseCleanInternal afterState := by
    exact (update_available_preserves_stepClean_internal hclean _).phaseClean_internal
  have hafterLimitPhase : StepPhaseCleanInternal afterLimit₁ := by
    exact update_limit₁_preserves_phaseClean_internal hafterStatePhase _
  have hafterLimit : afterLimit₁ Work.limit₁ =
      afterLimit₁ Work.horizon + 1 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.horizon,
      Work.available]
  rw [seqList_headTapeFormulas_effect tm tapes afterLimit₁ hafterLimitPhase
    (by simpa [afterLimit₁, afterState, Work.limit₁, Work.horizon,
      Work.available] using hhorizon) hafterLimit]
  let afterHeads := Function.update afterLimit₁ Work.available
    (afterLimit₁ Work.available +
      (tapes.map fun tape =>
        (afterLimit₁ Work.horizon + 1) *
          nextHeadFormulaScheduleSize (transitionCases tm).length k
            (afterLimit₁ Work.horizon) (movedHeadCaseSelectedAt tm tape)
            (effectCaseChoiceAt tm)).sum)
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      ((setStepPositionLimit 2).effect afterHeads)) = _
  rw [setStepPositionLimit_effect_local_internal]
  let afterLimit₂ := Function.update afterHeads Work.limit₁
    (afterHeads Work.horizon + 2)
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      afterLimit₂) = _
  have hafterHeadsPhase : StepPhaseCleanInternal afterHeads := by
    exact update_available_preserves_phaseClean hafterLimitPhase _
  have hafterLimit₂Phase : StepPhaseCleanInternal afterLimit₂ := by
    exact update_limit₁_preserves_phaseClean_internal hafterHeadsPhase _
  have hafterLimit₂ : afterLimit₂ Work.limit₁ =
      afterLimit₂ Work.horizon + 2 := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.horizon, Work.available]
  rw [seqList_cellTapeFormulas_effect tm tapes afterLimit₂
    hafterLimit₂Phase hafterLimit₂]
  funext i
  by_cases hlimit : i = Work.limit₁
  · subst i
    have hlimitZero : values 17 = 0 := by
      simpa [Work.limit₁] using hclean.limit₁
    simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
      afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
      stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
      Work.limit₁, Work.available, Work.horizon, hlimitZero]
  · simp [Work.limit₁] at hlimit
    by_cases havailable : i = Work.available
    · subst i
      simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
        afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
        stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
        Work.limit₁, Work.available, Work.horizon]
      omega
    · simp [Work.available] at havailable
      simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
        afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
        stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
        Work.limit₁, Work.available, Work.horizon, hlimit, havailable]

private theorem seqList_packedCopies_cons_effect
    (polynomial : Polynomial ℕ) (polynomials : List (Polynomial ℕ))
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.seqList ((polynomial :: polynomials).map
      emitPackedFormulaCopy)).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                ((polynomial :: polynomials).map fun p =>
                  p.eval (values Work.horizon)).sum))
            Work.available
              (values Work.available + (polynomial :: polynomials).length))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  induction polynomials generalizing polynomial values with
  | nil =>
      simp only [List.map_cons, List.map_nil, BinaryRoutine.seqList,
        BinaryRoutine.seq]
      rw [emitPackedFormulaCopy_effect]
      rfl
  | cons next rest ih =>
      simp only [List.map_cons, BinaryRoutine.seqList, BinaryRoutine.seq]
      change (BinaryRoutine.seqList
        ((next :: rest).map emitPackedFormulaCopy)).effect
          ((emitPackedFormulaCopy polynomial).effect values) = _
      rw [emitPackedFormulaCopy_effect, ih]
      funext i
      by_cases hgateCount : i = Work.gateCount
      · subst i
        simp [Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃, Work.horizon]
        omega
      · by_cases havailable : i = Work.available
        · subst i
          simp [Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃, Work.horizon]
          omega
        · by_cases hreference : i = Work.reference₀
          · subst i
            simp [Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
          · by_cases htemporary : i = Work.temporary₃
            · subst i
              simp [Work.gateCount, Work.available, Work.reference₀,
                Work.temporary₃]
            · simp [Work.gateCount] at hgateCount
              simp [Work.available] at havailable
              simp [Work.reference₀] at hreference
              simp [Work.temporary₃] at htemporary
              simp [hgateCount, havailable, hreference, htemporary,
                Work.gateCount, Work.available, Work.reference₀,
                Work.temporary₃, Work.horizon]

/-- Exact delayed state-copy effect. -/
theorem emitStepStateCopies_effect_internal (tm : NTM k)
    (values : BinaryValues WorkCount) :
    (emitStepStateCopies tm).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + stepStateFormulasEffectSizeInternal tm
                (values Work.horizon)))
            Work.available
              (values Work.available + Fintype.card tm.Q))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  have hcard : 0 < Fintype.card tm.Q := Fintype.card_pos_iff.mpr ⟨tm.qstart⟩
  obtain ⟨stateCount, hstateCount⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hcard)
  unfold emitStepStateCopies
  let polynomials := List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
    stateNextFormulaPolynomial tm ((Fintype.equivFin tm.Q).symm stateIndex)
  have hnonempty : polynomials ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [polynomials, hstateCount] at this
  obtain ⟨polynomial, rest, hpolynomials⟩ := List.exists_cons_of_ne_nil hnonempty
  rw [show (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      emitPackedFormulaCopy
        (stateNextFormulaPolynomial tm
          ((Fintype.equivFin tm.Q).symm stateIndex))) =
      polynomials.map emitPackedFormulaCopy by
        apply List.ext_getElem
        · simp [polynomials]
        · intro i hleft hright
          simp [polynomials]]
  rw [hpolynomials, seqList_packedCopies_cons_effect]
  have hsizes :
      ((polynomial :: rest).map fun p =>
        p.eval (values Work.horizon)).sum =
        stepStateFormulasEffectSizeInternal tm (values Work.horizon) := by
    rw [← hpolynomials]
    simp [polynomials, stepStateFormulasEffectSizeInternal, Function.comp_def]
  have hlength : rest.length + 1 = Fintype.card tm.Q := by
    rw [← List.length_ofFn (f := fun stateIndex : Fin (Fintype.card tm.Q) =>
      stateNextFormulaPolynomial tm ((Fintype.equivFin tm.Q).symm stateIndex))]
    rw [show (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      stateNextFormulaPolynomial tm ((Fintype.equivFin tm.Q).symm stateIndex)) =
      polynomials by rfl, hpolynomials]
    simp
  rw [hsizes]
  simp only [List.length_cons]
  rw [hlength]

/-- Four immutable delayed copies advance the rolling cursor by four formula
gates and append four packed outputs. -/
theorem emitStepImmutableCellCopies_effect_internal
    (values : BinaryValues WorkCount) :
    emitStepImmutableCellCopies.effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + 4))
            Work.available (values Work.available + 4))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  unfold emitStepImmutableCellCopies BinaryRoutine.repeatRoutine
  rw [show List.replicate 4 (emitPackedFormulaCopy (Polynomial.C 1)) =
      ([Polynomial.C 1, Polynomial.C 1, Polynomial.C 1, Polynomial.C 1] :
        List (Polynomial ℕ)).map emitPackedFormulaCopy by simp]
  rw [seqList_packedCopies_cons_effect]
  simp

private theorem seqList_writableCopies_eq_packed
    (tm : NTM k) (tape : WritableSlot k) (symbols : List Γ)
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.seqList (symbols.map fun symbol =>
      BinaryRoutine.branchZero Work.position
        (emitPackedFormulaCopy (Polynomial.C 1))
        (emitPackedFormulaCopy
          (writtenNextFormulaPolynomial tm tape symbol)))).effect values =
      (BinaryRoutine.seqList ((symbols.map fun symbol =>
        if values Work.position = 0 then Polynomial.C 1 else
          writtenNextFormulaPolynomial tm tape symbol).map
            emitPackedFormulaCopy)).effect values := by
  induction symbols generalizing values with
  | nil => rfl
  | cons symbol symbols ih =>
      simp only [List.map_cons, BinaryRoutine.seqList, BinaryRoutine.seq]
      by_cases hposition : values Work.position = 0
      · rw [show (BinaryRoutine.branchZero Work.position
            (emitPackedFormulaCopy (Polynomial.C 1))
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol))).effect values =
            (emitPackedFormulaCopy (Polynomial.C 1)).effect values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [ih]
        simp only [hposition, ↓reduceIte]
        have hnextPosition :
            (emitPackedFormulaCopy (Polynomial.C 1)).effect values
                Work.position = values Work.position := by
          simp [emitPackedFormulaCopy_effect, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
        rw [hnextPosition, hposition]
        simp
      · rw [show (BinaryRoutine.branchZero Work.position
            (emitPackedFormulaCopy (Polynomial.C 1))
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol))).effect values =
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol)).effect values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [ih]
        simp only [hposition, ↓reduceIte]
        have hnextPosition :
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol)).effect values
                Work.position = values Work.position := by
          simp [emitPackedFormulaCopy_effect, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
        rw [hnextPosition]
        simp [hposition]

/-- Exact delayed writable-cell copies at the current position. -/
theorem emitStepWritableCellCopies_effect_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount) :
    (emitStepWritableCellCopies tm tape).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                stepCellPositionEffectSizeInternal tm tape.toTapeSlot
                  (values Work.horizon) (values Work.position)))
            Work.available (values Work.available + 4))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  unfold emitStepWritableCellCopies
  let polynomials := List.ofFn fun symbolIndex : Fin 4 =>
    let symbol := symbolEquiv.symm symbolIndex
    if values Work.position = 0 then Polynomial.C 1 else
      writtenNextFormulaPolynomial tm tape symbol
  have hnonempty : polynomials ≠ [] := by simp [polynomials]
  obtain ⟨polynomial, rest, hpolynomials⟩ := List.exists_cons_of_ne_nil hnonempty
  let symbols := List.ofFn fun symbolIndex : Fin 4 =>
    symbolEquiv.symm symbolIndex
  rw [show (List.ofFn fun symbolIndex : Fin 4 =>
        let symbol := symbolEquiv.symm symbolIndex
        BinaryRoutine.branchZero Work.position
          (emitPackedFormulaCopy (Polynomial.C 1))
          (emitPackedFormulaCopy
            (writtenNextFormulaPolynomial tm tape symbol))) =
      symbols.map (fun symbol =>
        BinaryRoutine.branchZero Work.position
          (emitPackedFormulaCopy (Polynomial.C 1))
          (emitPackedFormulaCopy
            (writtenNextFormulaPolynomial tm tape symbol))) by
        apply List.ext_getElem
        · simp [symbols]
        · intro i hleft hright
          simp [symbols]]
  rw [seqList_writableCopies_eq_packed]
  change (BinaryRoutine.seqList (polynomials.map emitPackedFormulaCopy)).effect
    values = _
  rw [hpolynomials, seqList_packedCopies_cons_effect]
  have hsizes :
      ((polynomial :: rest).map fun p =>
        p.eval (values Work.horizon)).sum =
        stepCellPositionEffectSizeInternal tm tape.toTapeSlot
          (values Work.horizon) (values Work.position) := by
    rw [← hpolynomials]
    cases tape with
    | work index =>
        by_cases hposition : values Work.position = 0 <;>
          simp [polynomials, stepCellPositionEffectSizeInternal,
            WritableSlot.toTapeSlot, hposition]
    | output =>
        by_cases hposition : values Work.position = 0 <;>
          simp [polynomials, stepCellPositionEffectSizeInternal,
            WritableSlot.toTapeSlot, hposition]
  have hlength : (polynomial :: rest).length = 4 := by
    rw [← hpolynomials]
    simp [polynomials]
  rw [hsizes, hlength]

private theorem binaryForValues_copy_succ_effect
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
    (hpositionZero : values Work.position = 0)
    (count : ℕ) :
    BinaryRoutine.binaryForValues body Work.position values (count + 1) =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.position (count + 1))
              Work.gateCount
                (values Work.gateCount + prefixSize sizeAt (count + 1)))
            Work.available
              (values Work.available + outputCount * (count + 1)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  induction count with
  | zero =>
      have hpositionZero' : values 30 = 0 := by
        simpa [Work.position] using hpositionZero
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep,
        BinaryRoutine.binaryForValues]
      rw [hbody values rfl]
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [prefixSize, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, hpositionZero']
      · by_cases hgateCount : i = Work.gateCount
        · subst i
          simp [prefixSize, Work.position, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃, hpositionZero']
        · by_cases havailable : i = Work.available
          · subst i
            simp [prefixSize, Work.position, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · by_cases hreference : i = Work.reference₀
            · subst i
              simp [prefixSize, Work.position, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃]
            · by_cases htemporary : i = Work.temporary₃
              · subst i
                simp [prefixSize, Work.position, Work.gateCount,
                  Work.available, Work.reference₀, Work.temporary₃,
                  hpositionZero']
              · simp [prefixSize, hposition, hgateCount, havailable,
                hreference, htemporary]

  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, BinaryRoutine.binaryForStep, ih]
      let current := Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.position (count + 1))
              Work.gateCount
                (values Work.gateCount + prefixSize sizeAt (count + 1)))
            Work.available
              (values Work.available + outputCount * (count + 1)))
          Work.reference₀ 0) Work.temporary₃ 0
      have hcurrentHorizon : current Work.horizon = values Work.horizon := by
        simp [current, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.horizon]
      rw [hbody current hcurrentHorizon]
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [current, prefixSize, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃]
      · by_cases hgateCount : i = Work.gateCount
        · subst i
          simp [current, prefixSize, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
          omega
        · by_cases havailable : i = Work.available
          · subst i
            simp [current, prefixSize, Work.position, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃]
            ring
          · by_cases hreference : i = Work.reference₀
            · subst i
              simp [current, prefixSize, Work.position, Work.gateCount,
                Work.available, Work.reference₀, Work.temporary₃]
            · by_cases htemporary : i = Work.temporary₃
              · subst i
                simp [current, prefixSize, Work.position, Work.gateCount,
                  Work.available, Work.reference₀, Work.temporary₃]
              · simp [Work.position] at hposition
                simp [Work.gateCount] at hgateCount
                simp [Work.available] at havailable
                simp [Work.reference₀] at hreference
                simp [Work.temporary₃] at htemporary
                simp [current, prefixSize, hposition, hgateCount, havailable,
                  hreference, htemporary, Work.position, Work.gateCount,
                  Work.available, Work.reference₀, Work.temporary₃]

/-- Exact trajectory of a nonempty packed-copy loop prefix, exposed only for
the internal step-space proof. -/
theorem binaryForValues_copy_succ_effect_forSpace_internal
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
    (hpositionZero : values Work.position = 0)
    (count : ℕ) :
    BinaryRoutine.binaryForValues body Work.position values (count + 1) =
      Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update values Work.position (count + 1))
              Work.gateCount
                (values Work.gateCount + prefixSize sizeAt (count + 1)))
            Work.available
              (values Work.available + outputCount * (count + 1)))
          Work.reference₀ 0) Work.temporary₃ 0 :=
  binaryForValues_copy_succ_effect body sizeAt outputCount values hbody
    hpositionZero count

private theorem prefixSize_const (size count : ℕ) :
    prefixSize (fun _ => size) count = count * size := by
  induction count with
  | zero => simp [prefixSize]
  | succ count ih =>
      rw [prefixSize, ih]
      ring

/-- Exact delayed head-copy loop effect for one tape. -/
theorem emitStepHeadTapeCopies_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1) :
    (emitStepHeadTapeCopies tm tape).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + (values Work.horizon + 1) *
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                  (effectCaseChoiceAt tm)))
            Work.available (values Work.available + values Work.horizon + 1))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  rw [emitStepHeadTapeCopies, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.position).effect
    (BinaryRoutine.binaryForValues
      (emitPackedFormulaCopy (headNextFormulaPolynomial tm tape)) Work.position
      values (values Work.limit₁ - values Work.position)) = _
  rw [hposition, hlimit, Nat.sub_zero]
  rw [show values Work.horizon + 1 = values Work.horizon + 1 by rfl,
    binaryForValues_copy_succ_effect
      (emitPackedFormulaCopy (headNextFormulaPolynomial tm tape))
      (fun _ => (headNextFormulaPolynomial tm tape).eval
        (values Work.horizon)) 1 values (by
        intro current hcurrentHorizon
        rw [emitPackedFormulaCopy_effect]
        rw [hcurrentHorizon]) hposition (values Work.horizon)]
  rw [prefixSize_const]
  funext i
  by_cases hiposition : i = Work.position
  · subst i
    have hposition' : values 30 = 0 := by
      simpa [Work.position] using hposition
    simp [BinaryRoutine.clear, headNextFormulaPolynomial_eval,
      Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃, hposition']
  · simp [Work.position] at hiposition
    by_cases hgateCount : i = Work.gateCount
    · subst i
      simp [BinaryRoutine.clear, headNextFormulaPolynomial_eval,
        Work.position, Work.gateCount, Work.available, Work.reference₀,
        Work.temporary₃]
    · by_cases havailable : i = Work.available
      · subst i
        simp [BinaryRoutine.clear, headNextFormulaPolynomial_eval,
          Work.position, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
        omega
      · by_cases hreference : i = Work.reference₀
        · subst i
          simp [BinaryRoutine.clear, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
        · by_cases htemporary : i = Work.temporary₃
          · subst i
            simp [BinaryRoutine.clear, Work.position, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃]
          · simp [Work.gateCount] at hgateCount
            simp [Work.available] at havailable
            simp [Work.reference₀] at hreference
            simp [Work.temporary₃] at htemporary
            simp [BinaryRoutine.clear, hiposition, hgateCount, havailable,
              hreference, htemporary, Work.position, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃]

private theorem cellCopyBody_effect (tm : NTM k) (tape : TapeSlot k)
    (values : BinaryValues WorkCount) :
    (match tape with
      | .input => emitStepImmutableCellCopies
      | .work index => emitStepWritableCellCopies tm (.work index)
      | .output => emitStepWritableCellCopies tm .output).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + stepCellPositionEffectSizeInternal tm tape
                (values Work.horizon) (values Work.position)))
            Work.available (values Work.available + 4))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  cases tape with
  | input =>
      simpa [stepCellPositionEffectSizeInternal] using
        emitStepImmutableCellCopies_effect_internal values
  | work index =>
      simpa using! emitStepWritableCellCopies_effect_internal tm (.work index)
        values
  | output =>
      simpa using! emitStepWritableCellCopies_effect_internal tm .output values

private theorem clearPosition_after_copyUpdates
    (values : BinaryValues WorkCount)
    (positionValue gateCountValue availableValue : ℕ)
    (hposition : values Work.position = 0) :
    (BinaryRoutine.clear Work.position).effect
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update values Work.position positionValue)
                Work.gateCount gateCountValue)
              Work.available availableValue)
            Work.reference₀ 0) Work.temporary₃ 0) =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount gateCountValue)
            Work.available availableValue)
          Work.reference₀ 0) Work.temporary₃ 0 := by
  funext i
  by_cases hiposition : i = Work.position
  · subst i
    have hposition' : values 30 = 0 := by
      simpa [Work.position] using hposition
    simp [BinaryRoutine.clear, Work.position, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃, hposition']
  · by_cases hgateCount : i = Work.gateCount
    · subst i
      simp [BinaryRoutine.clear, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
    · by_cases havailable : i = Work.available
      · subst i
        simp [BinaryRoutine.clear, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃]
      · by_cases hreference : i = Work.reference₀
        · subst i
          simp [BinaryRoutine.clear, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
        · by_cases htemporary : i = Work.temporary₃
          · subst i
            simp [BinaryRoutine.clear, Work.position, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃]
          · simp [BinaryRoutine.clear, hiposition, hgateCount, havailable,
              hreference, htemporary]

/-- Exact delayed cell-copy effect for one named tape. -/
theorem emitStepCellTapeCopies_effect_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2) :
    (emitStepCellTapeCopies tm tape).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + prefixSize
                (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
                (values Work.horizon + 2)))
            Work.available
              (values Work.available + 4 * (values Work.horizon + 2)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  cases tape with
  | input =>
      rw [emitStepCellTapeCopies, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues emitStepImmutableCellCopies Work.position
          values (values Work.limit₁ - values Work.position)) = _
      rw [hposition, hlimit, Nat.sub_zero]
      rw [show values Work.horizon + 2 = (values Work.horizon + 1) + 1 by
        omega, binaryForValues_copy_succ_effect emitStepImmutableCellCopies
          (stepCellPositionEffectSizeInternal tm .input (values Work.horizon)) 4 values
          (by
            intro current hcurrentHorizon
            simpa [stepCellPositionEffectSizeInternal] using
              emitStepImmutableCellCopies_effect_internal current)
          hposition (values Work.horizon + 1)]
      exact clearPosition_after_copyUpdates values _ _ _ hposition
  | work index =>
      rw [emitStepCellTapeCopies, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues
          (emitStepWritableCellCopies tm (.work index)) Work.position values
            (values Work.limit₁ - values Work.position)) = _
      rw [hposition, hlimit, Nat.sub_zero]
      rw [show values Work.horizon + 2 = (values Work.horizon + 1) + 1 by
        omega, binaryForValues_copy_succ_effect
          (emitStepWritableCellCopies tm (.work index))
          (stepCellPositionEffectSizeInternal tm (.work index)
            (values Work.horizon)) 4 values
          (by
            intro current hcurrentHorizon
            rw [← hcurrentHorizon]
            exact emitStepWritableCellCopies_effect_internal tm (.work index)
              current)
          hposition (values Work.horizon + 1)]
      exact clearPosition_after_copyUpdates values _ _ _ hposition
  | output =>
      rw [emitStepCellTapeCopies, BinaryRoutine.seq]
      change (BinaryRoutine.clear Work.position).effect
        (BinaryRoutine.binaryForValues (emitStepWritableCellCopies tm .output)
          Work.position values (values Work.limit₁ - values Work.position)) = _
      rw [hposition, hlimit, Nat.sub_zero]
      rw [show values Work.horizon + 2 = (values Work.horizon + 1) + 1 by
        omega, binaryForValues_copy_succ_effect
          (emitStepWritableCellCopies tm .output)
          (stepCellPositionEffectSizeInternal tm .output (values Work.horizon)) 4
          values (by
            intro current hcurrentHorizon
            rw [← hcurrentHorizon]
            exact emitStepWritableCellCopies_effect_internal tm .output current)
          hposition (values Work.horizon + 1)]
      exact clearPosition_after_copyUpdates values _ _ _ hposition

private theorem seqList_headTapeCopies_effect
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeCopies tm))).effect
        values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                (tapes.map fun tape =>
                  (values Work.horizon + 1) *
                    nextHeadFormulaScheduleSize (transitionCases tm).length k
                      (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                      (effectCaseChoiceAt tm)).sum))
            Work.available
              (values Work.available + tapes.length *
                (values Work.horizon + 1)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  induction tapes generalizing values with
  | nil =>
      simp only [List.map_nil, BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
      funext i
      by_cases hreferenceIdx : i = Work.reference₀
      · subst i
        simpa [Work.reference₀, Work.temporary₃] using hreference
      · by_cases htemporaryIdx : i = Work.temporary₃
        · subst i
          simpa [hreferenceIdx] using htemporary
        · simp [hreferenceIdx, htemporaryIdx]
  | cons tape tapes ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList
        (tapes.map (emitStepHeadTapeCopies tm))).effect
          ((emitStepHeadTapeCopies tm tape).effect values) = _
      rw [emitStepHeadTapeCopies_effect_internal tm tape values hposition hlimit]
      let next := Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + (values Work.horizon + 1) *
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                  (effectCaseChoiceAt tm)))
            Work.available (values Work.available + values Work.horizon + 1))
          Work.reference₀ 0) Work.temporary₃ 0
      rw [ih next (by
        simpa [next, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃] using hposition) (by
        simpa [next, Work.limit₁, Work.horizon, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃] using hlimit) (by
        simp [next, Work.reference₀, Work.temporary₃]) (by
        simp [next, Work.reference₀, Work.temporary₃])]
      funext i
      by_cases hgateCount : i = Work.gateCount
      · subst i
        simp [next, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃, Work.horizon]
        omega
      · by_cases havailable : i = Work.available
        · subst i
          simp [next, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃, Work.horizon]
          ring
        · by_cases hreferenceIdx : i = Work.reference₀
          · subst i
            simp [next, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
          · by_cases htemporaryIdx : i = Work.temporary₃
            · subst i
              simp [next, Work.gateCount, Work.available, Work.reference₀,
                Work.temporary₃]
            · simp [Work.gateCount] at hgateCount
              simp [Work.available] at havailable
              simp [Work.reference₀] at hreferenceIdx
              simp [Work.temporary₃] at htemporaryIdx
              simp [next, hgateCount, havailable, hreferenceIdx,
                htemporaryIdx, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]

private theorem seqList_cellTapeCopies_effect
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
        values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                (tapes.map fun tape => prefixSize
                  (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
                  (values Work.horizon + 2)).sum))
            Work.available
              (values Work.available + tapes.length * 4 *
                (values Work.horizon + 2)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  induction tapes generalizing values with
  | nil =>
      simp only [List.map_nil, BinaryRoutine.seqList, BinaryRoutine.identity,
        BinaryRoutine.emitBits]
      funext i
      by_cases hreferenceIdx : i = Work.reference₀
      · subst i
        simpa [Work.reference₀, Work.temporary₃] using hreference
      · by_cases htemporaryIdx : i = Work.temporary₃
        · subst i
          simpa [hreferenceIdx] using htemporary
        · simp [hreferenceIdx, htemporaryIdx]
  | cons tape tapes ih =>
      rw [List.map_cons, BinaryRoutine.seqList]
      change (BinaryRoutine.seqList
        (tapes.map (emitStepCellTapeCopies tm))).effect
          ((emitStepCellTapeCopies tm tape).effect values) = _
      rw [emitStepCellTapeCopies_effect_internal tm tape values hposition hlimit]
      let next := Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + prefixSize
                (stepCellPositionEffectSizeInternal tm tape (values Work.horizon))
                (values Work.horizon + 2)))
            Work.available
              (values Work.available + 4 * (values Work.horizon + 2)))
          Work.reference₀ 0) Work.temporary₃ 0
      rw [ih next (by
        simpa [next, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃] using hposition) (by
        simpa [next, Work.limit₁, Work.horizon, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃] using hlimit) (by
        simp [next, Work.reference₀, Work.temporary₃]) (by
        simp [next, Work.reference₀, Work.temporary₃])]
      funext i
      by_cases hgateCount : i = Work.gateCount
      · subst i
        simp [next, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃, Work.horizon]
        omega
      · by_cases havailable : i = Work.available
        · subst i
          simp [next, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃, Work.horizon]
          ring
        · by_cases hreferenceIdx : i = Work.reference₀
          · subst i
            simp [next, Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃]
          · by_cases htemporaryIdx : i = Work.temporary₃
            · subst i
              simp [next, Work.gateCount, Work.available, Work.reference₀,
                Work.temporary₃]
            · simp [Work.gateCount] at hgateCount
              simp [Work.available] at havailable
              simp [Work.reference₀] at hreferenceIdx
              simp [Work.temporary₃] at htemporaryIdx
              simp [next, hgateCount, havailable, hreferenceIdx,
                htemporaryIdx, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃, Work.horizon]

/-- The delayed-copy phase consumes exactly one output gate per configuration
atom while advancing the saved formula cursor by the complete formula prefix. -/
theorem emitStepPackedCopies_effect_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepPackedCopies tm).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount +
                stepFormulasEffectSizeInternal tm (values Work.horizon)))
            Work.available
              (values Work.available +
                stepAtomCount (Fintype.card tm.Q) k
                  (values Work.horizon)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  have hschedule :
      [emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm) ++
          [setStepPositionLimit 2] ++
          tapes.map (emitStepCellTapeCopies tm) ++
          [BinaryRoutine.clear Work.limit₁] =
        ([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm)) ++
        ([setStepPositionLimit 2] ++
          tapes.map (emitStepCellTapeCopies tm)) ++
        [BinaryRoutine.clear Work.limit₁] := by
    simp [List.append_assoc]
  rw [emitStepPackedCopies]
  change (BinaryRoutine.seqList
    ([emitStepStateCopies tm, setStepPositionLimit 1] ++
      tapes.map (emitStepHeadTapeCopies tm) ++
      [setStepPositionLimit 2] ++
      tapes.map (emitStepCellTapeCopies tm) ++
      [BinaryRoutine.clear Work.limit₁])).effect values = _
  rw [hschedule]
  rw [seqList_append_effect,
    seqList_append_effect
      ([emitStepStateCopies tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeCopies tm)),
    seqList_append_effect
      [emitStepStateCopies tm, setStepPositionLimit 1],
    seqList_append_effect [setStepPositionLimit 2]]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeCopies tm))).effect
            ((setStepPositionLimit 1).effect
              ((emitStepStateCopies tm).effect values))))) = _
  rw [emitStepStateCopies_effect_internal tm values]
  let afterState := Function.update
    (Function.update
      (Function.update
        (Function.update values Work.gateCount
          (values Work.gateCount + stepStateFormulasEffectSizeInternal tm
            (values Work.horizon)))
        Work.available
          (values Work.available + Fintype.card tm.Q))
      Work.reference₀ 0) Work.temporary₃ 0
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeCopies tm))).effect
            ((setStepPositionLimit 1).effect afterState)))) = _
  nth_rewrite 2 [setStepPositionLimit_effect_local_internal]
  let afterLimit₁ := Function.update afterState Work.limit₁
    (afterState Work.horizon + 1)
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      ((setStepPositionLimit 2).effect
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeCopies tm))).effect afterLimit₁))) = _
  have hafterPosition : afterLimit₁ Work.position = 0 := by
    simpa [afterLimit₁, afterState, Work.limit₁, Work.position,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
      using hclean.position
  have hafterLimit : afterLimit₁ Work.limit₁ =
      afterLimit₁ Work.horizon + 1 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.horizon,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
  have hafterReference : afterLimit₁ Work.reference₀ = 0 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  have hafterTemporary : afterLimit₁ Work.temporary₃ = 0 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  rw [seqList_headTapeCopies_effect tm tapes afterLimit₁ hafterPosition
    hafterLimit hafterReference hafterTemporary]
  let afterHeads := Function.update
    (Function.update
      (Function.update
        (Function.update afterLimit₁ Work.gateCount
          (afterLimit₁ Work.gateCount +
            (tapes.map fun tape =>
              (afterLimit₁ Work.horizon + 1) *
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (afterLimit₁ Work.horizon)
                  (movedHeadCaseSelectedAt tm tape)
                  (effectCaseChoiceAt tm)).sum))
        Work.available
          (afterLimit₁ Work.available + tapes.length *
            (afterLimit₁ Work.horizon + 1)))
      Work.reference₀ 0) Work.temporary₃ 0
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      ((setStepPositionLimit 2).effect afterHeads)) = _
  rw [setStepPositionLimit_effect_local_internal]
  let afterLimit₂ := Function.update afterHeads Work.limit₁
    (afterHeads Work.horizon + 2)
  change (BinaryRoutine.clear Work.limit₁).effect
    ((BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      afterLimit₂) = _
  have hafterPosition₂ : afterLimit₂ Work.position = 0 := by
    simpa [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃] using hclean.position
  have hafterLimit₂ : afterLimit₂ Work.limit₁ =
      afterLimit₂ Work.horizon + 2 := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hafterReference₂ : afterLimit₂ Work.reference₀ = 0 := by
    simp [afterLimit₂, afterHeads, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  have hafterTemporary₂ : afterLimit₂ Work.temporary₃ = 0 := by
    simp [afterLimit₂, afterHeads, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  rw [seqList_cellTapeCopies_effect tm tapes afterLimit₂ hafterPosition₂
    hafterLimit₂ hafterReference₂ hafterTemporary₂]
  funext i
  by_cases hlimit : i = Work.limit₁
  · subst i
    have hlimitZero : values 17 = 0 := by
      simpa [Work.limit₁] using hclean.limit₁
    simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
      afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
      stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
      stepAtomCount, Work.limit₁, Work.gateCount,
      Work.available, Work.reference₀, Work.temporary₃, Work.horizon,
      hlimitZero]
  · simp [Work.limit₁] at hlimit
    by_cases hgateCount : i = Work.gateCount
    · subst i
      simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
        afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
        stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
        stepAtomCount, Work.limit₁, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
      omega
    · by_cases havailable : i = Work.available
      · subst i
        simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
          afterState, stepFormulasEffectSizeInternal, stepStateFormulasEffectSizeInternal,
          stepHeadFormulasEffectSizeInternal, stepCellFormulasEffectSizeInternal, tapes,
          stepAtomCount, Work.limit₁, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
        ring
      · by_cases hreference : i = Work.reference₀
        · subst i
          simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
            afterState, Work.limit₁, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃]
        · by_cases htemporary : i = Work.temporary₃
          · subst i
            simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
              afterState, Work.limit₁, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃]
          · simp [Work.gateCount] at hgateCount
            simp [Work.available] at havailable
            simp [Work.reference₀] at hreference
            simp [Work.temporary₃] at htemporary
            simp [BinaryRoutine.clear, afterLimit₂, afterHeads, afterLimit₁,
              afterState, hlimit, hgateCount, havailable, hreference,
              htemporary, Work.limit₁, Work.gateCount,
              Work.available, Work.reference₀, Work.temporary₃,
              Work.horizon]

/-- Exact whole-step register effect, expressed using the generator's explicit
formula-prefix count. The formula end is retained as the next configuration
base, and both temporary gate registers are cleared. -/
theorem emitStep_effect_explicit_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available
              (values Work.available +
                stepFormulasEffectSizeInternal tm.toNTM (values Work.horizon) +
                stepAtomCount (Fintype.card tm.Q) k
                  (values Work.horizon)))
            Work.configBase
              (values Work.available +
                stepFormulasEffectSizeInternal tm.toNTM (values Work.horizon)))
          Work.gateBound 0) Work.gateCount 0 := by
  let afterBound := Function.update values Work.gateBound
    (values Work.available)
  have hcleanBound : StepClean afterBound :=
    hclean.updateOuter_forEffect_internal values Work.gateBound
      (values Work.available) (Or.inl rfl)
  have hhorizonBound : 0 < afterBound Work.horizon := by
    simpa [afterBound, Work.gateBound, Work.horizon] using hhorizon
  let afterFormulas := Function.update afterBound Work.available
    (afterBound Work.available +
      stepFormulasEffectSizeInternal tm.toNTM (afterBound Work.horizon))
  have hformulaEffect :
      (emitStepFormulas tm.toNTM).effect afterBound = afterFormulas := by
    exact emitStepFormulas_effect_internal tm.toNTM afterBound hcleanBound
      hhorizonBound
  let afterBase := Function.update afterFormulas Work.configBase
    (afterFormulas Work.available)
  have hcleanFormulas : StepClean afterFormulas :=
    update_available_preserves_stepClean_internal hcleanBound _
  have hcleanBase : StepClean afterBase :=
    hcleanFormulas.updateOuter_forEffect_internal afterFormulas Work.configBase
      (afterFormulas Work.available) (Or.inr (Or.inl rfl))
  let afterCount := Function.update afterBase Work.gateCount
    (afterBase Work.gateBound)
  have hcleanCount : StepClean afterCount :=
    hcleanBase.updateOuter_forEffect_internal afterBase Work.gateCount
      (afterBase Work.gateBound) (Or.inr (Or.inr (Or.inl rfl)))
  have hpackedEffect := emitStepPackedCopies_effect_internal tm.toNTM
    afterCount hcleanCount
  simp only [emitStep, BinaryRoutine.seqList, BinaryRoutine.seq]
  change (BinaryRoutine.clear Work.gateCount).effect
    ((BinaryRoutine.clear Work.gateBound).effect
      ((emitStepPackedCopies tm.toNTM).effect
        ((BinaryRoutine.binaryCopy Work.gateBound Work.gateCount
          Work.copyCounter).effect
            ((BinaryRoutine.binaryCopy Work.available Work.configBase
              Work.copyCounter).effect
                ((emitStepFormulas tm.toNTM).effect
                  ((BinaryRoutine.binaryCopy Work.available Work.gateBound
                    Work.copyCounter).effect values)))))) = _
  change (BinaryRoutine.clear Work.gateCount).effect
    ((BinaryRoutine.clear Work.gateBound).effect
      ((emitStepPackedCopies tm.toNTM).effect
        (Function.update
          (Function.update
            ((emitStepFormulas tm.toNTM).effect
              (Function.update values Work.gateBound
                (values Work.available)))
            Work.configBase
              (((emitStepFormulas tm.toNTM).effect
                (Function.update values Work.gateBound
                  (values Work.available))) Work.available))
          Work.gateCount
            ((Function.update
              ((emitStepFormulas tm.toNTM).effect
                (Function.update values Work.gateBound
                  (values Work.available)))
              Work.configBase
                (((emitStepFormulas tm.toNTM).effect
                  (Function.update values Work.gateBound
                    (values Work.available))) Work.available))
              Work.gateBound)))) = _
  rw [hformulaEffect]
  change (BinaryRoutine.clear Work.gateCount).effect
    ((BinaryRoutine.clear Work.gateBound).effect
      ((emitStepPackedCopies tm.toNTM).effect afterCount)) = _
  rw [hpackedEffect]
  have hreference : values Work.reference₀ = 0 := by
    simpa [Work.position, Work.reference₀] using
      hclean.movedHeadClean.caseClean.reference₀
  have htemporary : values Work.temporary₃ = 0 := by
    simpa [Work.position, Work.temporary₃] using
      hclean.movedHeadClean.caseClean.temporary₃
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  funext i
  by_cases havailable : i = Work.available
  · subst i
    simp [BinaryRoutine.clear, afterCount, afterBase, afterFormulas,
      afterBound, Work.available, Work.configBase, Work.gateBound,
      Work.gateCount, Work.reference₀, Work.temporary₃, Work.horizon, hcard]
  · by_cases hbase : i = Work.configBase
    · subst i
      simp [BinaryRoutine.clear, afterCount, afterBase, afterFormulas,
        afterBound, Work.available, Work.configBase, Work.gateBound,
        Work.gateCount, Work.reference₀, Work.temporary₃, Work.horizon]
    · by_cases hbound : i = Work.gateBound
      · subst i
        simp [BinaryRoutine.clear, Work.gateBound, Work.gateCount]
      · by_cases hcount : i = Work.gateCount
        · subst i
          simp [BinaryRoutine.clear, Work.gateBound, Work.gateCount]
        · by_cases href : i = Work.reference₀
          · subst i
            simpa [BinaryRoutine.clear, afterCount, afterBase, afterFormulas,
              afterBound, Work.available, Work.configBase, Work.gateBound,
              Work.gateCount, Work.reference₀, Work.temporary₃] using
                hreference.symm
          · by_cases htemp : i = Work.temporary₃
            · subst i
              simpa [BinaryRoutine.clear, afterCount, afterBase,
                afterFormulas, afterBound, Work.available, Work.configBase,
                Work.gateBound, Work.gateCount, Work.reference₀,
                Work.temporary₃] using htemporary.symm
            · simp [Work.available] at havailable
              simp [Work.configBase] at hbase
              simp [Work.gateBound] at hbound
              simp [Work.gateCount] at hcount
              simp [Work.reference₀] at href
              simp [Work.temporary₃] at htemp
              simp [BinaryRoutine.clear, afterCount, afterBase,
                afterFormulas, afterBound, havailable, hbase, hbound, hcount,
                href, htemp, Work.available, Work.configBase, Work.gateBound,
                Work.gateCount, Work.reference₀, Work.temporary₃,
                Work.horizon]

/-- A complete packed step restores the reusable nested scratch convention. -/
theorem emitStep_effect_stepClean_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    StepClean ((emitStep tm).effect values) := by
  rw [emitStep_effect_explicit_internal tm values hclean hhorizon]
  let afterAvailable := Function.update values Work.available
    (values Work.available +
      stepFormulasEffectSizeInternal tm.toNTM (values Work.horizon) +
      stepAtomCount (Fintype.card tm.Q) k (values Work.horizon))
  have havailableClean : StepClean afterAvailable :=
    update_available_preserves_stepClean_internal hclean _
  let afterBase := Function.update afterAvailable Work.configBase
    (values Work.available +
      stepFormulasEffectSizeInternal tm.toNTM (values Work.horizon))
  have hbaseClean : StepClean afterBase :=
    havailableClean.updateOuter_forEffect_internal afterAvailable Work.configBase _
      (Or.inr (Or.inl rfl))
  let afterBound := Function.update afterBase Work.gateBound 0
  have hboundClean : StepClean afterBound :=
    hbaseClean.updateOuter_forEffect_internal afterBase Work.gateBound 0 (Or.inl rfl)
  exact hboundClean.updateOuter_forEffect_internal afterBound Work.gateCount 0
    (Or.inr (Or.inr (Or.inl rfl)))
end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
