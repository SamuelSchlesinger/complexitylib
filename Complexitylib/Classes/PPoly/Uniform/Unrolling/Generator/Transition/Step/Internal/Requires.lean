/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Next
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.PackedCopy
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Defs

/-!
# Packed-step generator domains

Reachable-position loop invariants and exact scratch-domain proofs for the
formula and delayed-copy phases of one packed transition step.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem MovedHeadFormulaClean.updateAvailable_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (available : ℕ) :
    MovedHeadFormulaClean
      (Function.update values Work.available available) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hcase := hclean.caseClean
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
    · simp [Work.available, Work.position]
    · simpa [Work.available, Work.position] using! hcase.loop₀
    · simpa [Work.available, Work.position] using! hcase.limit₀
    · simpa [Work.available, Work.position] using! hcase.reference₀
    · simpa [Work.available, Work.position] using! hcase.reference₁
    · simpa [Work.available, Work.position] using! hcase.emitCounter
    · simpa [Work.available, Work.position] using! hcase.copyCounter
    · simpa [Work.available, Work.position] using! hcase.multiplyCounter
    · simpa [Work.available, Work.position] using! hcase.addCounter
    · simpa [Work.available, Work.position] using! hcase.temporary₀
    · simpa [Work.available, Work.position] using! hcase.temporary₁
    · simpa [Work.available, Work.position] using! hcase.temporary₂
    · simpa [Work.available, Work.position] using! hcase.loop₃
    · simpa [Work.available, Work.position] using! hcase.temporary₃
    · simpa [Work.available, Work.position] using! hcase.polynomialScratch
    · simpa [Work.available, Work.position] using! hcase.tapeIndex
    · simpa [Work.available, Work.position] using! hcase.symbolIndex
  all_goals
    simp only [Function.update_apply]
    rw [ite_eq_right (by decide)]
  · exact hclean.limit₂
  · exact hclean.loop₁
  · exact hclean.savedOutput
  · exact hclean.direction
  · exact hclean.atomKind

private theorem MovedHeadFormulaClean.updatePosition_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (position : ℕ) :
    MovedHeadFormulaClean
      (Function.update values Work.position position) := by
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
    simpa [hupdate] using hclean.caseClean
  · simpa [Work.position, Work.limit₂] using hclean.limit₂
  · simpa [Work.position, Work.loop₁] using hclean.loop₁
  · simpa [Work.position, Work.savedOutput] using hclean.savedOutput
  · simpa [Work.position, Work.direction] using hclean.direction
  · simpa [Work.position, Work.atomKind] using hclean.atomKind

private theorem MovedHeadFormulaClean.updateLimit₁_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (limit : ℕ) :
    MovedHeadFormulaClean (Function.update values Work.limit₁ limit) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hcase := hclean.caseClean
    refine
      { toReadFormulaClean :=
          { position := by simp [Work.limit₁, Work.position]
            loop₀ := by simpa [Work.limit₁, Work.loop₀] using! hcase.loop₀
            limit₀ := by simpa [Work.limit₁, Work.limit₀] using! hcase.limit₀
            reference₀ := by simpa [Work.limit₁, Work.reference₀] using! hcase.reference₀
            reference₁ := by simpa [Work.limit₁, Work.reference₁] using! hcase.reference₁
            emitCounter := by simpa [Work.limit₁, Work.emitCounter] using! hcase.emitCounter
            copyCounter := by simpa [Work.limit₁, Work.copyCounter] using! hcase.copyCounter
            multiplyCounter := by simpa [Work.limit₁, Work.multiplyCounter]
              using! hcase.multiplyCounter
            addCounter := by simpa [Work.limit₁, Work.addCounter] using! hcase.addCounter
            temporary₀ := by simpa [Work.limit₁, Work.temporary₀] using! hcase.temporary₀
            temporary₁ := by simpa [Work.limit₁, Work.temporary₁] using! hcase.temporary₁
            temporary₂ := by simpa [Work.limit₁, Work.temporary₂] using! hcase.temporary₂ }
        loop₃ := by simpa [Work.limit₁, Work.loop₃] using! hcase.loop₃
        temporary₃ := by simpa [Work.limit₁, Work.temporary₃] using! hcase.temporary₃
        polynomialScratch := by simpa [Work.limit₁, Work.polynomialScratch]
          using! hcase.polynomialScratch
        tapeIndex := by simpa [Work.limit₁, Work.tapeIndex] using! hcase.tapeIndex
        symbolIndex := by simpa [Work.limit₁, Work.symbolIndex] using! hcase.symbolIndex }
  · simpa [Work.limit₁, Work.limit₂] using hclean.limit₂
  · simpa [Work.limit₁, Work.loop₁] using hclean.loop₁
  · simpa [Work.limit₁, Work.savedOutput] using hclean.savedOutput
  · simpa [Work.limit₁, Work.direction] using hclean.direction
  · simpa [Work.limit₁, Work.atomKind] using hclean.atomKind

private theorem MovedHeadFormulaClean.caseClean_forStep
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position = 0) :
    CaseFormulaClean values := by
  have hupdate : Function.update values Work.position 0 = values := by
    funext i
    by_cases hi : i = Work.position
    · subst i
      simp [hposition]
    · simp [hi]
  simpa [hupdate] using hclean.caseClean

private theorem MovedHeadFormulaClean.writtenClean_forStep
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    WrittenCellFormulaClean values :=
  { caseClean := hclean.caseClean
    limit₂ := hclean.limit₂
    savedOutput := hclean.savedOutput }

private theorem MovedHeadFormulaClean.copyScratch_forStep
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.copyCounter = 0 ∧ values Work.addCounter = 0 ∧
      values Work.multiplyCounter = 0 ∧ values Work.emitCounter = 0 := by
  have hcase := hclean.caseClean
  simpa [Work.position, Work.copyCounter, Work.addCounter,
    Work.multiplyCounter, Work.emitCounter] using
      And.intro hcase.copyCounter
        (And.intro hcase.addCounter
          (And.intro hcase.multiplyCounter hcase.emitCounter))

private theorem MovedHeadFormulaClean.packedCopyScratch_forStep
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values) :
    values Work.temporary₃ = 0 ∧
      values Work.polynomialScratch = 0 ∧
      values Work.multiplyCounter = 0 ∧ values Work.addCounter = 0 ∧
      values Work.copyCounter = 0 ∧ values Work.emitCounter = 0 := by
  have hcase := hclean.caseClean
  simpa [Work.position, Work.temporary₃, Work.polynomialScratch,
    Work.multiplyCounter, Work.addCounter, Work.copyCounter,
    Work.emitCounter] using
      And.intro hcase.temporary₃
        (And.intro hcase.polynomialScratch
          (And.intro hcase.multiplyCounter
            (And.intro hcase.addCounter
              (And.intro hcase.copyCounter hcase.emitCounter))))

private theorem MovedHeadFormulaClean.afterPackedCopy_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (sizePolynomial : Polynomial ℕ) :
    MovedHeadFormulaClean
      ((emitPackedFormulaCopy sizePolynomial).effect values) := by
  rw [emitPackedFormulaCopy_effect]
  have havailable := MovedHeadFormulaClean.updateAvailable_forStep values hclean
    (values Work.available + 1)
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · let final :=
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (values Work.gateCount + sizePolynomial.eval
                (values Work.horizon)))
            Work.available (values Work.available + 1)) Work.reference₀ 0)
        Work.temporary₃ 0
    refine
      { toReadFormulaClean :=
          { position := by simp [Work.position]
            loop₀ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position] using! havailable.caseClean.loop₀
            limit₀ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position] using! havailable.caseClean.limit₀
            reference₀ := by simp [Work.reference₀, Work.temporary₃,
              Work.position]
            reference₁ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.reference₁
            emitCounter := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.emitCounter
            copyCounter := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.copyCounter
            multiplyCounter := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.multiplyCounter
            addCounter := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.addCounter
            temporary₀ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.temporary₀
            temporary₁ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.temporary₁
            temporary₂ := by simpa [final, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃, Work.position]
                using! havailable.caseClean.temporary₂ }
        loop₃ := by simpa [final, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.position] using! havailable.caseClean.loop₃
        temporary₃ := by simp [Work.temporary₃, Work.position]
        polynomialScratch := by simpa [final, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.position]
            using! havailable.caseClean.polynomialScratch
        tapeIndex := by simpa [final, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.position] using! havailable.caseClean.tapeIndex
        symbolIndex := by simpa [final, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.position] using! havailable.caseClean.symbolIndex }
  all_goals
    simp only [Function.update_apply]
    repeat' rw [ite_eq_right (by decide)]
  · exact hclean.limit₂
  · exact hclean.loop₁
  · exact hclean.savedOutput
  · exact hclean.direction
  · exact hclean.atomKind

private theorem seqList_requires_preserves_forStep
    (routines : List (BinaryRoutine WorkCount))
    (P : BinaryValues WorkCount → Prop)
    (hrequires : ∀ routine ∈ routines, ∀ values, P values →
      routine.requires values)
    (hpreserves : ∀ routine ∈ routines, ∀ values, P values →
      P (routine.effect values))
    (values : BinaryValues WorkCount) (hP : P values) :
    (BinaryRoutine.seqList routines).requires values ∧
      P ((BinaryRoutine.seqList routines).effect values) := by
  induction routines generalizing values with
  | nil => simpa [BinaryRoutine.seqList, BinaryRoutine.identity,
      BinaryRoutine.emitBits]
  | cons routine routines ih =>
      simp only [BinaryRoutine.seqList, BinaryRoutine.seq]
      have hroutineRequires := hrequires routine (by simp) values hP
      have hroutinePreserves := hpreserves routine (by simp) values hP
      have htail := ih
        (fun next hnext => hrequires next (by simp [hnext]))
        (fun next hnext => hpreserves next (by simp [hnext]))
        (routine.effect values) hroutinePreserves
      exact ⟨⟨hroutineRequires, htail.1⟩, htail.2⟩

private theorem binaryFor_requires_preserves_forStep
    (body : BinaryRoutine WorkCount) (counterIdx limitIdx : Fin WorkCount)
    (P : BinaryValues WorkCount → Prop) (values : BinaryValues WorkCount)
    (hne : counterIdx ≠ limitIdx) (hle : values counterIdx ≤ values limitIdx)
    (hP : P values)
    (hbody : ∀ current, P current → current counterIdx < current limitIdx →
      body.requires current ∧
        body.effect current counterIdx = current counterIdx ∧
        body.effect current limitIdx = current limitIdx ∧
        P (BinaryRoutine.binaryForStep body counterIdx current)) :
    (BinaryRoutine.binaryFor body counterIdx limitIdx).requires values ∧
      P ((BinaryRoutine.binaryFor body counterIdx limitIdx).effect values) := by
  let total := BinaryRoutine.binaryForCount counterIdx limitIdx values
  have hinvariant : ∀ count, count ≤ total →
      let current := BinaryRoutine.binaryForValues body counterIdx values count
      P current ∧ current counterIdx = values counterIdx + count ∧
        current limitIdx = values limitIdx := by
    intro count hcount
    induction count with
    | zero => simpa [BinaryRoutine.binaryForValues]
    | succ count ih =>
        have hprevious := ih (by omega)
        let previous := BinaryRoutine.binaryForValues body counterIdx values count
        have hlt : previous counterIdx < previous limitIdx := by
          rcases hprevious with ⟨_hP, hcounter, hlimit⟩
          dsimp only [total, BinaryRoutine.binaryForCount] at hcount
          dsimp only [previous]
          omega
        have hstep := hbody previous hprevious.1 hlt
        simp only [BinaryRoutine.binaryForValues]
        refine ⟨hstep.2.2.2, ?_, ?_⟩
        · simp [BinaryRoutine.binaryForStep, hprevious.2.1]
          omega
        · rw [BinaryRoutine.binaryForStep,
            Function.update_of_ne (Ne.symm hne), hstep.2.2.1]
          exact hprevious.2.2
  constructor
  · refine ⟨hne, hle, ?_⟩
    intro count hcount
    have hcurrent := hinvariant count (Nat.le_of_lt hcount)
    have hlt :
        BinaryRoutine.binaryForValues body counterIdx values count counterIdx <
          BinaryRoutine.binaryForValues body counterIdx values count limitIdx := by
      dsimp only [total, BinaryRoutine.binaryForCount] at hcount
      omega
    exact (hbody _ hcurrent.1 hlt).1
      |> fun hrequires =>
        ⟨hrequires, (hbody _ hcurrent.1 hlt).2.1,
          (hbody _ hcurrent.1 hlt).2.2.1⟩
  · exact (hinvariant total le_rfl).1

private structure StepPhaseCleanInternal (values : BinaryValues WorkCount) : Prop where
  moved : MovedHeadFormulaClean values
  position : values Work.position = 0

private theorem StepPhaseCleanInternal.updateAvailable
    {values : BinaryValues WorkCount} (hclean : StepPhaseCleanInternal values)
    (available : ℕ) :
    StepPhaseCleanInternal (Function.update values Work.available available) :=
  { moved := MovedHeadFormulaClean.updateAvailable_forStep values hclean.moved
      available
    position := by simpa [Work.available, Work.position] using hclean.position }

private theorem MovedHeadFormulaClean.nextCellCopy_requires_forStep
    {values : BinaryValues WorkCount} (hclean : MovedHeadFormulaClean values)
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    (emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).requires
      values := by
  rcases hclean.copyScratch_forStep with ⟨hcopy, hadd, hmultiply, hemit⟩
  exact emitNextCellCopy_requires stateCount tapeCount tapeIndex symbolIndex
    values hcopy hadd hmultiply hemit

private theorem MovedHeadFormulaClean.afterNextCellCopy_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (stateCount tapeCount tapeIndex symbolIndex : ℕ) :
    MovedHeadFormulaClean
      ((emitNextCellCopy stateCount tapeCount tapeIndex symbolIndex).effect
        values) := by
  have hcase := hclean.caseClean
  rw [emitNextCellCopy_effect stateCount tapeCount tapeIndex symbolIndex values
    (by simpa [Work.position, Work.tapeIndex] using hcase.tapeIndex)
    (by simpa [Work.position, Work.symbolIndex] using hcase.symbolIndex)
    (by simpa [Work.position, Work.temporary₀] using hcase.temporary₀)
    (by simpa [Work.position, Work.temporary₁] using hcase.temporary₁)
    (by simpa [Work.position, Work.temporary₂] using hcase.temporary₂)
    (by simpa [Work.position, Work.reference₀] using hcase.reference₀)]
  exact MovedHeadFormulaClean.updateAvailable_forStep values hclean _

private theorem emitStepStateFormulas_requires_preserves_forStep (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepPhaseCleanInternal values) :
    (emitStepStateFormulas tm).requires values ∧
      StepPhaseCleanInternal ((emitStepStateFormulas tm).effect values) ∧
      (emitStepStateFormulas tm).effect values Work.horizon =
        values Work.horizon := by
  let P := fun current : BinaryValues WorkCount =>
    StepPhaseCleanInternal current ∧ current Work.horizon = values Work.horizon
  have hresult := seqList_requires_preserves_forStep
    (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      emitNextStateFormula tm ((Fintype.equivFin tm.Q).symm stateIndex)) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨stateIndex, rfl⟩ := hroutine
      exact emitNextStateFormula_requires tm
        ((Fintype.equivFin tm.Q).symm stateIndex) current
        (hcurrent.1.moved.caseClean_forStep hcurrent.1.position))
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨stateIndex, rfl⟩ := hroutine
      rw [emitNextStateFormula_effect tm
        ((Fintype.equivFin tm.Q).symm stateIndex) current
        (hcurrent.1.moved.caseClean_forStep hcurrent.1.position)]
      exact ⟨hcurrent.1.updateAvailable _, by simpa [Work.available,
        Work.horizon] using hcurrent.2⟩)
    values ⟨hclean, rfl⟩
  exact ⟨hresult.1, hresult.2.1, hresult.2.2⟩

theorem emitStepStateFormulas_requires_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepStateFormulas tm).requires values :=
  (emitStepStateFormulas_requires_preserves_forStep tm values
    ⟨hclean.movedHeadClean, hclean.position⟩).1

private structure HeadLoopClean (values : BinaryValues WorkCount) : Prop where
  moved : MovedHeadFormulaClean values
  horizon : 0 < values Work.horizon
  limit : values Work.limit₁ = values Work.horizon + 1

private theorem emitStepHeadTapeFormulas_requires_preserves_forStep
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : HeadLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepHeadTapeFormulas tm tape).requires values ∧
      HeadLoopClean ((emitStepHeadTapeFormulas tm tape).effect values) ∧
      (emitStepHeadTapeFormulas tm tape).effect values Work.position = 0 := by
  have hloop := binaryFor_requires_preserves_forStep
    (emitNextHeadFormula tm tape) Work.position Work.limit₁ HeadLoopClean
    values (by decide) hle hclean (by
      intro current hcurrent hposition
      have htarget : current Work.position ≤ current Work.horizon := by
        rw [hcurrent.limit] at hposition
        omega
      have hrequires := emitNextHeadFormula_requires tm tape current
        hcurrent.moved hcurrent.horizon htarget
      have heffect := emitNextHeadFormula_effect tm tape current
        hcurrent.moved hcurrent.horizon htarget
      refine ⟨hrequires, ?_, ?_, ?_⟩
      · rw [heffect]
        simp [Work.available, Work.position]
      · rw [heffect]
        simp [Work.available, Work.limit₁]
      · rw [BinaryRoutine.binaryForStep, heffect]
        refine
          { moved := ?_
            horizon := ?_
            limit := ?_ }
        · exact MovedHeadFormulaClean.updatePosition_forStep _
            (MovedHeadFormulaClean.updateAvailable_forStep current
              hcurrent.moved _) _
        · simpa [Work.available, Work.position, Work.horizon] using
            hcurrent.horizon
        · simpa [Work.available, Work.position, Work.limit₁, Work.horizon]
            using hcurrent.limit)
  simp only [emitStepHeadTapeFormulas, BinaryRoutine.seq]
  refine ⟨⟨hloop.1, trivial⟩, ?_, by simp [BinaryRoutine.clear]⟩
  refine
    { moved := MovedHeadFormulaClean.updatePosition_forStep _ hloop.2.moved 0
      horizon := ?_
      limit := ?_ }
  · simpa [BinaryRoutine.clear, Work.position, Work.horizon] using
      hloop.2.horizon
  · simpa [BinaryRoutine.clear, Work.position, Work.limit₁,
      Work.horizon] using hloop.2.limit

theorem emitStepHeadTapeFormulas_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepHeadTapeFormulas tm tape).requires values :=
  (emitStepHeadTapeFormulas_requires_preserves_forStep tm tape values
    ⟨hclean, hhorizon, hlimit⟩ hle).1

theorem emitStepImmutableCellPosition_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values) :
    (emitStepImmutableCellPosition tm tape).requires values := by
  apply (seqList_requires_preserves_forStep _ MovedHeadFormulaClean
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      exact hcurrent.nextCellCopy_requires_forStep _ _ _ _)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      exact hcurrent.afterNextCellCopy_forStep current _ _ _ _)
    values hclean).1

private theorem emitStepImmutableCellPosition_requires_preserves_forStep
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values) :
    (emitStepImmutableCellPosition tm tape).requires values ∧
      MovedHeadFormulaClean
        ((emitStepImmutableCellPosition tm tape).effect values) ∧
      (emitStepImmutableCellPosition tm tape).effect values Work.position =
        values Work.position ∧
      (emitStepImmutableCellPosition tm tape).effect values Work.horizon =
        values Work.horizon ∧
      (emitStepImmutableCellPosition tm tape).effect values Work.limit₁ =
        values Work.limit₁ := by
  let P := fun current : BinaryValues WorkCount =>
    MovedHeadFormulaClean current ∧
      current Work.position = values Work.position ∧
      current Work.horizon = values Work.horizon ∧
      current Work.limit₁ = values Work.limit₁
  have hresult := seqList_requires_preserves_forStep
    (List.ofFn fun symbolIndex : Fin 4 =>
      emitNextCellCopy (Fintype.card tm.Q) (k + 2) tape.index
        (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex))) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      exact hcurrent.1.nextCellCopy_requires_forStep _ _ _ _)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      have heffect := emitNextCellCopy_effect (Fintype.card tm.Q) (k + 2)
        tape.index (CircuitUnrolling.symbolIndex
          (symbolEquiv.symm symbolIndex)) current
        (by simpa [Work.position, Work.tapeIndex] using
          hcurrent.1.caseClean.tapeIndex)
        (by simpa [Work.position, Work.symbolIndex] using
          hcurrent.1.caseClean.symbolIndex)
        (by simpa [Work.position, Work.temporary₀] using
          hcurrent.1.caseClean.temporary₀)
        (by simpa [Work.position, Work.temporary₁] using
          hcurrent.1.caseClean.temporary₁)
        (by simpa [Work.position, Work.temporary₂] using
          hcurrent.1.caseClean.temporary₂)
        (by simpa [Work.position, Work.reference₀] using
          hcurrent.1.caseClean.reference₀)
      rw [heffect]
      exact ⟨MovedHeadFormulaClean.updateAvailable_forStep current
        hcurrent.1 _, by simpa [Work.available, Work.position] using
          hcurrent.2.1, by simpa [Work.available, Work.horizon] using
          hcurrent.2.2.1, by simpa [Work.available, Work.limit₁] using
          hcurrent.2.2.2⟩)
    values ⟨hclean, rfl, rfl, rfl⟩
  exact ⟨hresult.1, hresult.2.1, hresult.2.2.1,
    hresult.2.2.2.1, hresult.2.2.2.2⟩

private theorem emitStepWritableCellPosition_requires_preserves_forStep
    (tm : NTM k) (tape : WritableSlot k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitStepWritableCellPosition tm tape).requires values ∧
      MovedHeadFormulaClean
        ((emitStepWritableCellPosition tm tape).effect values) ∧
      (emitStepWritableCellPosition tm tape).effect values Work.position =
        values Work.position ∧
      (emitStepWritableCellPosition tm tape).effect values Work.horizon =
        values Work.horizon ∧
      (emitStepWritableCellPosition tm tape).effect values Work.limit₁ =
        values Work.limit₁ := by
  let P := fun current : BinaryValues WorkCount =>
    MovedHeadFormulaClean current ∧
      current Work.position = values Work.position ∧
      current Work.horizon = values Work.horizon ∧
      current Work.limit₁ = values Work.limit₁
  have hresult := seqList_requires_preserves_forStep
    (List.ofFn fun symbolIndex : Fin 4 =>
      let symbol := symbolEquiv.symm symbolIndex
      BinaryRoutine.branchZero Work.position
        (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index (CircuitUnrolling.symbolIndex symbol))
        (emitNextWrittenCellFormula tm tape symbol)) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      have hcurrentPosition :
          current Work.position ≤ current Work.horizon + 1 := by
        rw [hcurrent.2.1, hcurrent.2.2.1]
        exact hposition
      by_cases hzero : current Work.position = 0
      · simp only [BinaryRoutine.branchZero, hzero, ite_true]
        exact hcurrent.1.nextCellCopy_requires_forStep _ _ _ _
      · simp only [BinaryRoutine.branchZero, hzero, ite_false]
        exact emitNextWrittenCellFormula_requires tm tape
          (symbolEquiv.symm symbolIndex) current
          hcurrent.1.writtenClean_forStep hcurrentPosition)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      by_cases hzero : current Work.position = 0
      · simp only [BinaryRoutine.branchZero, hzero, ite_true]
        have hcase := hcurrent.1.caseClean
        have heffect := emitNextCellCopy_effect (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index
          (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex)) current
          (by simpa [Work.position, Work.tapeIndex] using hcase.tapeIndex)
          (by simpa [Work.position, Work.symbolIndex] using hcase.symbolIndex)
          (by simpa [Work.position, Work.temporary₀] using hcase.temporary₀)
          (by simpa [Work.position, Work.temporary₁] using hcase.temporary₁)
          (by simpa [Work.position, Work.temporary₂] using hcase.temporary₂)
          (by simpa [Work.position, Work.reference₀] using hcase.reference₀)
        rw [heffect]
        exact ⟨MovedHeadFormulaClean.updateAvailable_forStep current
          hcurrent.1 _, by simpa [Work.available, Work.position] using
            hcurrent.2.1, by simpa [Work.available, Work.horizon] using
            hcurrent.2.2.1, by simpa [Work.available, Work.limit₁] using
            hcurrent.2.2.2⟩
      · simp only [BinaryRoutine.branchZero, hzero, ite_false]
        rw [emitNextWrittenCellFormula_effect tm tape
          (symbolEquiv.symm symbolIndex) current hcurrent.1.writtenClean_forStep]
        refine ⟨MovedHeadFormulaClean.updateAvailable_forStep current
          hcurrent.1 _, ?_, ?_, ?_⟩
        · simpa [Work.available, Work.position] using hcurrent.2.1
        · simpa [Work.available, Work.horizon] using hcurrent.2.2.1
        · simpa [Work.available, Work.limit₁] using hcurrent.2.2.2)
    values ⟨hclean, rfl, rfl, rfl⟩
  simpa only [emitStepWritableCellPosition] using hresult

theorem emitStepWritableCellPosition_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position ≤ values Work.horizon + 1) :
    (emitStepWritableCellPosition tm tape).requires values :=
  (emitStepWritableCellPosition_requires_preserves_forStep tm tape values
    hclean hposition).1

private structure CellLoopClean (values : BinaryValues WorkCount) : Prop where
  moved : MovedHeadFormulaClean values
  limit : values Work.limit₁ = values Work.horizon + 2

private theorem emitStepWritableTapeCellFormulas_requires_preserves_forStep
    (tm : NTM k) (tape : WritableSlot k)
    (values : BinaryValues WorkCount) (hclean : CellLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepWritableCellPosition tm tape)
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)).requires values ∧
      CellLoopClean
        ((BinaryRoutine.seq
          (BinaryRoutine.binaryFor (emitStepWritableCellPosition tm tape)
            Work.position Work.limit₁)
          (BinaryRoutine.clear Work.position)).effect values) ∧
      (BinaryRoutine.seq
          (BinaryRoutine.binaryFor (emitStepWritableCellPosition tm tape)
            Work.position Work.limit₁)
          (BinaryRoutine.clear Work.position)).effect values Work.position = 0 := by
  have hloop := binaryFor_requires_preserves_forStep
    (emitStepWritableCellPosition tm tape) Work.position Work.limit₁
    CellLoopClean values (by decide) hle hclean (by
      intro current hcurrent hlt
      have hposition : current Work.position ≤ current Work.horizon + 1 := by
        rw [hcurrent.limit] at hlt
        omega
      have hbody := emitStepWritableCellPosition_requires_preserves_forStep
        tm tape current hcurrent.moved hposition
      refine ⟨hbody.1, hbody.2.2.1, hbody.2.2.2.2, ?_⟩
      refine
        { moved := MovedHeadFormulaClean.updatePosition_forStep _
            hbody.2.1 _
          limit := ?_ }
      simp only [BinaryRoutine.binaryForStep, Function.update_apply]
      rw [ite_eq_right (by decide), hbody.2.2.2.2,
        ite_eq_right (by decide), hbody.2.2.2.1]
      exact hcurrent.limit)
  simp only [BinaryRoutine.seq]
  exact ⟨⟨hloop.1, trivial⟩,
    ⟨MovedHeadFormulaClean.updatePosition_forStep _ hloop.2.moved 0,
      by simpa [BinaryRoutine.clear, Work.position, Work.limit₁,
        Work.horizon] using hloop.2.limit⟩,
    by simp [BinaryRoutine.clear]⟩

private theorem emitStepCellTapeFormulas_requires_preserves_forStep
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : CellLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepCellTapeFormulas tm tape).requires values ∧
      CellLoopClean ((emitStepCellTapeFormulas tm tape).effect values) ∧
      (emitStepCellTapeFormulas tm tape).effect values Work.position = 0 := by
  cases tape with
  | input =>
      have hloop := binaryFor_requires_preserves_forStep
        (emitStepImmutableCellPosition tm .input) Work.position Work.limit₁
        CellLoopClean values (by decide) hle hclean (by
          intro current hcurrent _hlt
          have hbody := emitStepImmutableCellPosition_requires_preserves_forStep
            tm .input current hcurrent.moved
          refine ⟨hbody.1, hbody.2.2.1, hbody.2.2.2.2, ?_⟩
          · refine
              { moved := MovedHeadFormulaClean.updatePosition_forStep _
                  hbody.2.1 _
                limit := ?_ }
            simp only [BinaryRoutine.binaryForStep, Function.update_apply]
            rw [ite_eq_right (by decide), hbody.2.2.2.2,
              ite_eq_right (by decide), hbody.2.2.2.1]
            exact hcurrent.limit)
      simp only [emitStepCellTapeFormulas, BinaryRoutine.seq]
      refine ⟨⟨hloop.1, trivial⟩,
        ⟨MovedHeadFormulaClean.updatePosition_forStep _ hloop.2.moved 0,
          ?_⟩, by simp [BinaryRoutine.clear]⟩
      simpa [BinaryRoutine.clear, Work.position, Work.limit₁,
        Work.horizon] using hloop.2.limit
  | work index =>
      simpa only [emitStepCellTapeFormulas] using
        emitStepWritableTapeCellFormulas_requires_preserves_forStep tm
          (.work index) values hclean hle
  | output =>
      simpa only [emitStepCellTapeFormulas] using
        emitStepWritableTapeCellFormulas_requires_preserves_forStep tm .output
          values hclean hle

theorem emitStepCellTapeFormulas_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepCellTapeFormulas tm tape).requires values :=
  (emitStepCellTapeFormulas_requires_preserves_forStep tm tape values
    ⟨hclean, hlimit⟩ hle).1

private theorem setStepPositionLimit_requires_forStep (extra : ℕ)
    (values : BinaryValues WorkCount)
    (hcopy : values Work.copyCounter = 0) :
    (setStepPositionLimit extra).requires values := by
  simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, Work.horizon, Work.limit₁, Work.copyCounter]
  simpa [Work.copyCounter] using hcopy

private theorem setStepPositionLimit_effect_forStep (extra : ℕ)
    (values : BinaryValues WorkCount) :
    (setStepPositionLimit extra).effect values =
      Function.update values Work.limit₁
        (values Work.horizon + extra) := by
  simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst]

private structure PositionedHeadLoopClean
    (values : BinaryValues WorkCount) : Prop extends HeadLoopClean values where
  position : values Work.position = 0

private theorem emitStepHeadTapes_requires_preserves_forStep (tm : NTM k)
    (tapes : List (TapeSlot k)) (values : BinaryValues WorkCount)
    (hclean : PositionedHeadLoopClean values) :
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeFormulas tm))).requires
        values ∧
      PositionedHeadLoopClean
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeFormulas tm))).effect values) := by
  apply seqList_requires_preserves_forStep _ PositionedHeadLoopClean
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepHeadTapeFormulas_requires_preserves_forStep tm tape current
      hcurrent.toHeadLoopClean (by
        rw [hcurrent.position, hcurrent.limit]
        omega)).1
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    have hresult := emitStepHeadTapeFormulas_requires_preserves_forStep tm tape
      current hcurrent.toHeadLoopClean
      (by
        rw [hcurrent.position, hcurrent.limit]
        omega)
    exact ⟨hresult.2.1, hresult.2.2⟩
  · exact hclean

private structure PositionedCellLoopClean
    (values : BinaryValues WorkCount) : Prop extends CellLoopClean values where
  position : values Work.position = 0

private theorem emitStepCellTapes_requires_preserves_forStep (tm : NTM k)
    (tapes : List (TapeSlot k)) (values : BinaryValues WorkCount)
    (hclean : PositionedCellLoopClean values) :
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).requires
        values ∧
      PositionedCellLoopClean
        ((BinaryRoutine.seqList
          (tapes.map (emitStepCellTapeFormulas tm))).effect values) := by
  apply seqList_requires_preserves_forStep _ PositionedCellLoopClean
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepCellTapeFormulas_requires_preserves_forStep tm tape current
      hcurrent.toCellLoopClean (by
        rw [hcurrent.position, hcurrent.limit]
        omega)).1
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    have hresult := emitStepCellTapeFormulas_requires_preserves_forStep tm tape
      current hcurrent.toCellLoopClean
      (by
        rw [hcurrent.position, hcurrent.limit]
        omega)
    exact ⟨hresult.2.1, hresult.2.2⟩
  · exact hclean

private theorem seqList_append_effect_forStep
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

private theorem seqList_append_requires_forStep
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

private theorem emitStepFormulas_requires_preserves_forStep (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStepFormulas tm).requires values ∧
      StepClean ((emitStepFormulas tm).effect values) := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let afterStates := (emitStepStateFormulas tm).effect values
  have hstates := emitStepStateFormulas_requires_preserves_forStep tm values
    ⟨hclean.movedHeadClean, hclean.position⟩
  have hcopyAfterStates : afterStates Work.copyCounter = 0 :=
    hstates.2.1.moved.caseClean.copyCounter
  let afterHeadLimit := (setStepPositionLimit 1).effect afterStates
  have hheadLimitRequires := setStepPositionLimit_requires_forStep 1
    afterStates hcopyAfterStates
  have hheadLimitEffect := setStepPositionLimit_effect_forStep 1 afterStates
  have hhorizonAfterStates : 0 < afterStates Work.horizon := by
    dsimp only [afterStates]
    rw [hstates.2.2]
    exact hhorizon
  have hheadStart : PositionedHeadLoopClean afterHeadLimit := by
    dsimp only [afterHeadLimit]
    rw [hheadLimitEffect]
    refine
      { moved := MovedHeadFormulaClean.updateLimit₁_forStep afterStates
          hstates.2.1.moved (afterStates Work.horizon + 1)
        horizon := ?_
        limit := ?_
        position := ?_ }
    · simpa [Work.limit₁, Work.horizon] using hhorizonAfterStates
    · simp [Work.limit₁, Work.horizon]
    · simpa [Work.limit₁, Work.position] using hstates.2.1.position
  let afterHeads :=
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeFormulas tm))).effect
      afterHeadLimit
  have hheads := emitStepHeadTapes_requires_preserves_forStep tm tapes
    afterHeadLimit hheadStart
  have hcopyAfterHeads : afterHeads Work.copyCounter = 0 :=
    hheads.2.moved.caseClean.copyCounter
  let afterCellLimit := (setStepPositionLimit 2).effect afterHeads
  have hcellLimitRequires := setStepPositionLimit_requires_forStep 2 afterHeads
    hcopyAfterHeads
  have hcellLimitEffect := setStepPositionLimit_effect_forStep 2 afterHeads
  have hcellStart : PositionedCellLoopClean afterCellLimit := by
    dsimp only [afterCellLimit]
    rw [hcellLimitEffect]
    refine
      { moved := MovedHeadFormulaClean.updateLimit₁_forStep afterHeads
          hheads.2.moved (afterHeads Work.horizon + 2)
        limit := by simp [Work.limit₁, Work.horizon]
        position := by simpa [Work.limit₁, Work.position] using
          hheads.2.position }
  let afterCells :=
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeFormulas tm))).effect
      afterCellLimit
  have hcells := emitStepCellTapes_requires_preserves_forStep tm tapes
    afterCellLimit hcellStart
  have hfinal : StepClean
      ((BinaryRoutine.clear Work.limit₁).effect afterCells) :=
    { movedHeadClean := MovedHeadFormulaClean.updateLimit₁_forStep _
        hcells.2.moved 0
      position := by simpa [BinaryRoutine.clear, Work.limit₁,
        Work.position] using hcells.2.position
      limit₁ := by simp [BinaryRoutine.clear] }
  dsimp only [emitStepFormulas]
  simp only [seqList_append_requires_forStep,
    seqList_append_effect_forStep, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    List.cons_append, List.nil_append]
  exact ⟨⟨hstates.1, hheadLimitRequires,
    ⟨⟨hheads.1, hcellLimitRequires, trivial⟩, hcells.1⟩,
      ⟨trivial, trivial⟩⟩,
    hfinal⟩

theorem emitStepFormulas_requires_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStepFormulas tm).requires values :=
  (emitStepFormulas_requires_preserves_forStep tm values hclean hhorizon).1

private theorem emitPackedFormulaCopy_requires_preserves_forStep
    (sizePolynomial : Polynomial ℕ) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hpositive : 0 < sizePolynomial.eval (values Work.horizon)) :
    (emitPackedFormulaCopy sizePolynomial).requires values ∧
      MovedHeadFormulaClean
        ((emitPackedFormulaCopy sizePolynomial).effect values) ∧
      (emitPackedFormulaCopy sizePolynomial).effect values Work.position =
        values Work.position ∧
      (emitPackedFormulaCopy sizePolynomial).effect values Work.horizon =
        values Work.horizon ∧
      (emitPackedFormulaCopy sizePolynomial).effect values Work.limit₁ =
        values Work.limit₁ := by
  refine ⟨(emitPackedFormulaCopy_requires sizePolynomial values).2 ?_,
    hclean.afterPackedCopy_forStep values sizePolynomial, ?_, ?_, ?_⟩
  · exact ⟨hclean.packedCopyScratch_forStep.1,
      hclean.packedCopyScratch_forStep.2.1,
      hclean.packedCopyScratch_forStep.2.2.1,
      hclean.packedCopyScratch_forStep.2.2.2.1,
      hclean.packedCopyScratch_forStep.2.2.2.2.1,
      hclean.packedCopyScratch_forStep.2.2.2.2.2, hpositive⟩
  all_goals
    simp [emitPackedFormulaCopy_effect, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃, Work.position, Work.horizon,
      Work.limit₁]

private theorem emitStepStateCopies_requires_preserves_forStep (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepStateCopies tm).requires values ∧
      StepClean ((emitStepStateCopies tm).effect values) ∧
      (emitStepStateCopies tm).effect values Work.horizon =
        values Work.horizon := by
  let P := fun current : BinaryValues WorkCount =>
    StepClean current ∧ current Work.horizon = values Work.horizon
  have hresult := seqList_requires_preserves_forStep
    (List.ofFn fun stateIndex : Fin (Fintype.card tm.Q) =>
      emitPackedFormulaCopy (stateNextFormulaPolynomial tm
        ((Fintype.equivFin tm.Q).symm stateIndex))) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨stateIndex, rfl⟩ := hroutine
      exact (emitPackedFormulaCopy_requires_preserves_forStep _ current
        hcurrent.1.movedHeadClean
        (stateNextFormulaPolynomial_eval_pos tm
          ((Fintype.equivFin tm.Q).symm stateIndex) _)).1)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨stateIndex, rfl⟩ := hroutine
      have hresult := emitPackedFormulaCopy_requires_preserves_forStep _ current
        hcurrent.1.movedHeadClean
        (stateNextFormulaPolynomial_eval_pos tm
          ((Fintype.equivFin tm.Q).symm stateIndex) _)
      exact ⟨⟨hresult.2.1, hresult.2.2.1.trans hcurrent.1.position,
        hresult.2.2.2.2.trans hcurrent.1.limit₁⟩,
        hresult.2.2.2.1.trans hcurrent.2⟩)
    values ⟨hclean, rfl⟩
  exact ⟨hresult.1, hresult.2.1, hresult.2.2⟩

theorem emitStepStateCopies_requires_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepStateCopies tm).requires values :=
  (emitStepStateCopies_requires_preserves_forStep tm values hclean).1

private structure PackedHeadLoopClean (values : BinaryValues WorkCount) : Prop where
  moved : MovedHeadFormulaClean values
  limit : values Work.limit₁ = values Work.horizon + 1

private structure PositionedPackedHeadLoopClean
    (values : BinaryValues WorkCount) : Prop extends PackedHeadLoopClean values where
  position : values Work.position = 0

private theorem emitStepHeadTapeCopies_requires_preserves_forStep
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : PackedHeadLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepHeadTapeCopies tm tape).requires values ∧
      PositionedPackedHeadLoopClean
        ((emitStepHeadTapeCopies tm tape).effect values) := by
  have hloop := binaryFor_requires_preserves_forStep
    (emitPackedFormulaCopy (headNextFormulaPolynomial tm tape)) Work.position
    Work.limit₁ PackedHeadLoopClean values (by decide) hle hclean (by
      intro current hcurrent _hlt
      have hbody := emitPackedFormulaCopy_requires_preserves_forStep _ current
        hcurrent.moved (headNextFormulaPolynomial_eval_pos tm tape _)
      refine ⟨hbody.1, hbody.2.2.1, hbody.2.2.2.2, ?_⟩
      refine
        { moved := MovedHeadFormulaClean.updatePosition_forStep _
            hbody.2.1 _
          limit := ?_ }
      simp only [BinaryRoutine.binaryForStep, Function.update_apply]
      rw [ite_eq_right (by decide), hbody.2.2.2.2,
        ite_eq_right (by decide), hbody.2.2.2.1]
      exact hcurrent.limit)
  simp only [emitStepHeadTapeCopies, BinaryRoutine.seq]
  refine ⟨⟨hloop.1, trivial⟩, ?_⟩
  exact
    { moved := MovedHeadFormulaClean.updatePosition_forStep _ hloop.2.moved 0
      limit := by simpa [BinaryRoutine.clear, Work.position, Work.limit₁,
        Work.horizon] using hloop.2.limit
      position := by simp [BinaryRoutine.clear] }

private theorem emitStepHeadTapeCopiesList_requires_preserves_forStep
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount)
    (hclean : PositionedPackedHeadLoopClean values) :
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeCopies tm))).requires
        values ∧
      PositionedPackedHeadLoopClean
        ((BinaryRoutine.seqList
          (tapes.map (emitStepHeadTapeCopies tm))).effect values) := by
  apply seqList_requires_preserves_forStep _ PositionedPackedHeadLoopClean
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepHeadTapeCopies_requires_preserves_forStep tm tape current
      hcurrent.toPackedHeadLoopClean
      (by rw [hcurrent.position, hcurrent.limit]; omega)).1
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepHeadTapeCopies_requires_preserves_forStep tm tape current
      hcurrent.toPackedHeadLoopClean
      (by rw [hcurrent.position, hcurrent.limit]; omega)).2
  · exact hclean

theorem emitStepHeadTapeCopies_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepHeadTapeCopies tm tape).requires values :=
  (emitStepHeadTapeCopies_requires_preserves_forStep tm tape values
    ⟨hclean, hlimit⟩ hle).1

private theorem emitStepImmutableCellCopies_requires_preserves_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    emitStepImmutableCellCopies.requires values ∧
      MovedHeadFormulaClean (emitStepImmutableCellCopies.effect values) ∧
      emitStepImmutableCellCopies.effect values Work.position =
        values Work.position ∧
      emitStepImmutableCellCopies.effect values Work.horizon =
        values Work.horizon ∧
      emitStepImmutableCellCopies.effect values Work.limit₁ =
        values Work.limit₁ := by
  let P := fun current : BinaryValues WorkCount =>
    MovedHeadFormulaClean current ∧
      current Work.position = values Work.position ∧
      current Work.horizon = values Work.horizon ∧
      current Work.limit₁ = values Work.limit₁
  have hresult := seqList_requires_preserves_forStep
    (List.replicate 4 (emitPackedFormulaCopy (Polynomial.C 1))) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_replicate] at hroutine
      rw [hroutine.2]
      exact (emitPackedFormulaCopy_requires_preserves_forStep
        (Polynomial.C 1) current hcurrent.1
        (by simpa only [Polynomial.eval_C] using Nat.zero_lt_one)).1)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_replicate] at hroutine
      rw [hroutine.2]
      have hbody := emitPackedFormulaCopy_requires_preserves_forStep
        (Polynomial.C 1) current hcurrent.1
        (by simpa only [Polynomial.eval_C] using Nat.zero_lt_one)
      exact ⟨hbody.2.1, hbody.2.2.1.trans hcurrent.2.1,
        hbody.2.2.2.1.trans hcurrent.2.2.1,
        hbody.2.2.2.2.trans hcurrent.2.2.2⟩)
    values ⟨hclean, rfl, rfl, rfl⟩
  simpa only [emitStepImmutableCellCopies, BinaryRoutine.repeatRoutine] using
    hresult

private theorem emitStepWritableCellCopies_requires_preserves_forStep
    (tm : NTM k) (tape : WritableSlot k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values) :
    (emitStepWritableCellCopies tm tape).requires values ∧
      MovedHeadFormulaClean
        ((emitStepWritableCellCopies tm tape).effect values) ∧
      (emitStepWritableCellCopies tm tape).effect values Work.position =
        values Work.position ∧
      (emitStepWritableCellCopies tm tape).effect values Work.horizon =
        values Work.horizon ∧
      (emitStepWritableCellCopies tm tape).effect values Work.limit₁ =
        values Work.limit₁ := by
  let P := fun current : BinaryValues WorkCount =>
    MovedHeadFormulaClean current ∧
      current Work.position = values Work.position ∧
      current Work.horizon = values Work.horizon ∧
      current Work.limit₁ = values Work.limit₁
  have hresult := seqList_requires_preserves_forStep
    (List.ofFn fun symbolIndex : Fin 4 =>
      let symbol := symbolEquiv.symm symbolIndex
      BinaryRoutine.branchZero Work.position
        (emitPackedFormulaCopy (Polynomial.C 1))
        (emitPackedFormulaCopy
          (writtenNextFormulaPolynomial tm tape symbol))) P
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      by_cases hzero : current Work.position = 0
      · simp only [BinaryRoutine.branchZero, hzero, ite_true]
        exact (emitPackedFormulaCopy_requires_preserves_forStep
          (Polynomial.C 1) current hcurrent.1
          (by simpa only [Polynomial.eval_C] using Nat.zero_lt_one)).1
      · simp only [BinaryRoutine.branchZero, hzero, ite_false]
        exact (emitPackedFormulaCopy_requires_preserves_forStep _ current
          hcurrent.1 (writtenNextFormulaPolynomial_eval_pos tm tape _ _)).1)
    (fun routine hroutine current hcurrent => by
      simp only [List.mem_ofFn] at hroutine
      obtain ⟨symbolIndex, rfl⟩ := hroutine
      by_cases hzero : current Work.position = 0
      · simp only [BinaryRoutine.branchZero, hzero, ite_true]
        have hbody := emitPackedFormulaCopy_requires_preserves_forStep
          (Polynomial.C 1) current hcurrent.1
          (by simpa only [Polynomial.eval_C] using Nat.zero_lt_one)
        exact ⟨hbody.2.1, hbody.2.2.1.trans hcurrent.2.1,
          hbody.2.2.2.1.trans hcurrent.2.2.1,
          hbody.2.2.2.2.trans hcurrent.2.2.2⟩
      · simp only [BinaryRoutine.branchZero, hzero, ite_false]
        have hbody := emitPackedFormulaCopy_requires_preserves_forStep
          (writtenNextFormulaPolynomial tm tape
            (symbolEquiv.symm symbolIndex)) current hcurrent.1
          (writtenNextFormulaPolynomial_eval_pos tm tape
            (symbolEquiv.symm symbolIndex) _)
        exact ⟨hbody.2.1, hbody.2.2.1.trans hcurrent.2.1,
          hbody.2.2.2.1.trans hcurrent.2.2.1,
          hbody.2.2.2.2.trans hcurrent.2.2.2⟩)
    values ⟨hclean, rfl, rfl, rfl⟩
  simpa only [emitStepWritableCellCopies] using hresult

theorem emitStepWritableCellCopies_requires_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values) :
    (emitStepWritableCellCopies tm tape).requires values :=
  (emitStepWritableCellCopies_requires_preserves_forStep tm tape values
    hclean).1

private theorem emitStepWritableTapeCellCopies_requires_preserves_forStep
    (tm : NTM k) (tape : WritableSlot k)
    (values : BinaryValues WorkCount)
    (hclean : CellLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (BinaryRoutine.seq
        (BinaryRoutine.binaryFor (emitStepWritableCellCopies tm tape)
          Work.position Work.limit₁)
        (BinaryRoutine.clear Work.position)).requires values ∧
      PositionedCellLoopClean
        ((BinaryRoutine.seq
          (BinaryRoutine.binaryFor (emitStepWritableCellCopies tm tape)
            Work.position Work.limit₁)
          (BinaryRoutine.clear Work.position)).effect values) := by
  have hloop := binaryFor_requires_preserves_forStep
    (emitStepWritableCellCopies tm tape) Work.position Work.limit₁
    CellLoopClean values (by decide) hle hclean (by
      intro current hcurrent _hlt
      have hbody := emitStepWritableCellCopies_requires_preserves_forStep
        tm tape current hcurrent.moved
      refine ⟨hbody.1, hbody.2.2.1, hbody.2.2.2.2, ?_⟩
      refine
        { moved := MovedHeadFormulaClean.updatePosition_forStep _
            hbody.2.1 _
          limit := ?_ }
      simp only [BinaryRoutine.binaryForStep, Function.update_apply]
      rw [ite_eq_right (by decide), hbody.2.2.2.2,
        ite_eq_right (by decide), hbody.2.2.2.1]
      exact hcurrent.limit)
  simp only [BinaryRoutine.seq]
  refine ⟨⟨hloop.1, trivial⟩, ?_⟩
  exact
    { toCellLoopClean :=
        { moved := MovedHeadFormulaClean.updatePosition_forStep _
            hloop.2.moved 0
          limit := by simpa [BinaryRoutine.clear, Work.position, Work.limit₁,
            Work.horizon] using hloop.2.limit }
      position := by simp [BinaryRoutine.clear] }

private theorem emitStepCellTapeCopies_requires_preserves_forStep
    (tm : NTM k) (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : CellLoopClean values)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepCellTapeCopies tm tape).requires values ∧
      PositionedCellLoopClean
        ((emitStepCellTapeCopies tm tape).effect values) := by
  cases tape with
  | input =>
      have hloop := binaryFor_requires_preserves_forStep
        emitStepImmutableCellCopies Work.position Work.limit₁ CellLoopClean
        values (by decide) hle hclean (by
          intro current hcurrent _hlt
          have hbody :=
            emitStepImmutableCellCopies_requires_preserves_forStep current
              hcurrent.moved
          refine ⟨hbody.1, hbody.2.2.1, hbody.2.2.2.2, ?_⟩
          refine
            { moved := MovedHeadFormulaClean.updatePosition_forStep _
                hbody.2.1 _
              limit := ?_ }
          simp only [BinaryRoutine.binaryForStep, Function.update_apply]
          rw [ite_eq_right (by decide), hbody.2.2.2.2,
            ite_eq_right (by decide), hbody.2.2.2.1]
          exact hcurrent.limit)
      simp only [emitStepCellTapeCopies, BinaryRoutine.seq]
      refine ⟨⟨hloop.1, trivial⟩, ?_⟩
      exact
        { toCellLoopClean :=
            { moved := MovedHeadFormulaClean.updatePosition_forStep _
                hloop.2.moved 0
              limit := by simpa [BinaryRoutine.clear, Work.position,
                Work.limit₁, Work.horizon] using hloop.2.limit }
          position := by simp [BinaryRoutine.clear] }
  | work index =>
      simpa only [emitStepCellTapeCopies] using
        emitStepWritableTapeCellCopies_requires_preserves_forStep tm
          (.work index) values hclean hle
  | output =>
      simpa only [emitStepCellTapeCopies] using
        emitStepWritableTapeCellCopies_requires_preserves_forStep tm .output
          values hclean hle

private theorem emitStepCellTapeCopiesList_requires_preserves_forStep
    (tm : NTM k) (tapes : List (TapeSlot k))
    (values : BinaryValues WorkCount) (hclean : PositionedCellLoopClean values) :
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).requires
        values ∧
      PositionedCellLoopClean
        ((BinaryRoutine.seqList
          (tapes.map (emitStepCellTapeCopies tm))).effect values) := by
  apply seqList_requires_preserves_forStep _ PositionedCellLoopClean
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepCellTapeCopies_requires_preserves_forStep tm tape current
      hcurrent.toCellLoopClean
      (by rw [hcurrent.position, hcurrent.limit]; omega)).1
  · intro routine hroutine current hcurrent
    simp only [List.mem_map] at hroutine
    obtain ⟨tape, _htape, rfl⟩ := hroutine
    exact (emitStepCellTapeCopies_requires_preserves_forStep tm tape current
      hcurrent.toCellLoopClean
      (by rw [hcurrent.position, hcurrent.limit]; omega)).2
  · exact hclean

theorem emitStepCellTapeCopies_requires_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (hle : values Work.position ≤ values Work.limit₁) :
    (emitStepCellTapeCopies tm tape).requires values :=
  (emitStepCellTapeCopies_requires_preserves_forStep tm tape values
    ⟨hclean, hlimit⟩ hle).1

private theorem emitStepPackedCopies_requires_preserves_forStep (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepPackedCopies tm).requires values ∧
      StepClean ((emitStepPackedCopies tm).effect values) := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let afterStates := (emitStepStateCopies tm).effect values
  have hstates := emitStepStateCopies_requires_preserves_forStep tm values hclean
  have hheadLimitRequires := setStepPositionLimit_requires_forStep 1 afterStates
    hstates.2.1.movedHeadClean.caseClean.copyCounter
  let afterHeadLimit := (setStepPositionLimit 1).effect afterStates
  have hheadLimitEffect := setStepPositionLimit_effect_forStep 1 afterStates
  have hheadStart : PositionedPackedHeadLoopClean afterHeadLimit := by
    dsimp only [afterHeadLimit]
    rw [hheadLimitEffect]
    exact
      { moved := MovedHeadFormulaClean.updateLimit₁_forStep afterStates
          hstates.2.1.movedHeadClean (afterStates Work.horizon + 1)
        limit := by simp [Work.limit₁, Work.horizon]
        position := by simpa [Work.limit₁, Work.position] using
          hstates.2.1.position }
  let afterHeads :=
    (BinaryRoutine.seqList (tapes.map (emitStepHeadTapeCopies tm))).effect
      afterHeadLimit
  have hheads := emitStepHeadTapeCopiesList_requires_preserves_forStep tm tapes
    afterHeadLimit hheadStart
  have hcellLimitRequires := setStepPositionLimit_requires_forStep 2 afterHeads
    hheads.2.moved.caseClean.copyCounter
  let afterCellLimit := (setStepPositionLimit 2).effect afterHeads
  have hcellLimitEffect := setStepPositionLimit_effect_forStep 2 afterHeads
  have hcellStart : PositionedCellLoopClean afterCellLimit := by
    dsimp only [afterCellLimit]
    rw [hcellLimitEffect]
    exact
      { moved := MovedHeadFormulaClean.updateLimit₁_forStep afterHeads
          hheads.2.moved (afterHeads Work.horizon + 2)
        limit := by simp [Work.limit₁, Work.horizon]
        position := by simpa [Work.limit₁, Work.position] using
          hheads.2.position }
  let afterCells :=
    (BinaryRoutine.seqList (tapes.map (emitStepCellTapeCopies tm))).effect
      afterCellLimit
  have hcells := emitStepCellTapeCopiesList_requires_preserves_forStep tm tapes
    afterCellLimit hcellStart
  have hfinal : StepClean
      ((BinaryRoutine.clear Work.limit₁).effect afterCells) :=
    { movedHeadClean := MovedHeadFormulaClean.updateLimit₁_forStep _
        hcells.2.moved 0
      position := by simpa [BinaryRoutine.clear, Work.limit₁,
        Work.position] using hcells.2.position
      limit₁ := by simp [BinaryRoutine.clear] }
  dsimp only [emitStepPackedCopies]
  simp only [seqList_append_requires_forStep,
    seqList_append_effect_forStep, BinaryRoutine.seqList,
    BinaryRoutine.seq, BinaryRoutine.identity, BinaryRoutine.emitBits,
    List.cons_append, List.nil_append]
  exact ⟨⟨hstates.1, hheadLimitRequires,
    ⟨⟨hheads.1, hcellLimitRequires, trivial⟩, hcells.1⟩,
      ⟨trivial, trivial⟩⟩, hfinal⟩

theorem emitStepPackedCopies_requires_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepPackedCopies tm).requires values :=
  (emitStepPackedCopies_requires_preserves_forStep tm values hclean).1

private theorem MovedHeadFormulaClean.updateOuter_forStep
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (idx : Fin WorkCount) (value : ℕ)
    (hidx : idx = Work.gateBound ∨ idx = Work.configBase ∨
      idx = Work.gateCount) :
    MovedHeadFormulaClean (Function.update values idx value) := by
  rcases hidx with rfl | rfl | rfl <;>
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
                Work.gateCount, Work.position]
              loop₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.loop₀] using
                  hclean.caseClean.loop₀
              limit₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.limit₀] using
                  hclean.caseClean.limit₀
              reference₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.reference₀] using
                  hclean.caseClean.reference₀
              reference₁ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.reference₁] using
                  hclean.caseClean.reference₁
              emitCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.emitCounter] using
                  hclean.caseClean.emitCounter
              copyCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.copyCounter] using
                  hclean.caseClean.copyCounter
              multiplyCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.multiplyCounter] using
                  hclean.caseClean.multiplyCounter
              addCounter := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.addCounter] using
                  hclean.caseClean.addCounter
              temporary₀ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.temporary₀] using
                  hclean.caseClean.temporary₀
              temporary₁ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.temporary₁] using
                  hclean.caseClean.temporary₁
              temporary₂ := by simpa [Work.gateBound, Work.configBase,
                Work.gateCount, Work.position, Work.temporary₂] using
                  hclean.caseClean.temporary₂ }
          loop₃ := by simpa [Work.gateBound, Work.configBase, Work.gateCount,
              Work.position, Work.loop₃] using hclean.caseClean.loop₃
          temporary₃ := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.position, Work.temporary₃] using
                hclean.caseClean.temporary₃
          polynomialScratch := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.position, Work.polynomialScratch] using
                hclean.caseClean.polynomialScratch
          tapeIndex := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.position, Work.tapeIndex] using
                hclean.caseClean.tapeIndex
          symbolIndex := by simpa [Work.gateBound, Work.configBase,
              Work.gateCount, Work.position, Work.symbolIndex] using
                hclean.caseClean.symbolIndex }
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.limit₂]
        using hclean.limit₂
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.loop₁]
        using hclean.loop₁
    | simpa [Work.gateBound, Work.configBase, Work.gateCount,
        Work.savedOutput] using hclean.savedOutput
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.direction]
        using hclean.direction
    | simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.atomKind]
        using hclean.atomKind

private theorem StepClean.updateOuter_forStep
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (idx : Fin WorkCount) (value : ℕ)
    (hidx : idx = Work.gateBound ∨ idx = Work.configBase ∨
      idx = Work.gateCount) :
    StepClean (Function.update values idx value) :=
  { movedHeadClean := hclean.movedHeadClean.updateOuter_forStep values idx value
      hidx
    position := by rcases hidx with rfl | rfl | rfl <;>
      simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.position]
        using hclean.position
    limit₁ := by rcases hidx with rfl | rfl | rfl <;>
      simpa [Work.gateBound, Work.configBase, Work.gateCount, Work.limit₁]
        using hclean.limit₁ }

theorem emitStep_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).requires values := by
  let afterBound := Function.update values Work.gateBound
    (values Work.available)
  have hboundCopy :
      (BinaryRoutine.binaryCopy Work.available Work.gateBound
        Work.copyCounter).requires values :=
    ⟨by decide, by decide, by decide,
      hclean.movedHeadClean.caseClean.copyCounter⟩
  have hcleanAfterBound : StepClean afterBound :=
    hclean.updateOuter_forStep values Work.gateBound (values Work.available)
      (Or.inl rfl)
  have hhorizonAfterBound : 0 < afterBound Work.horizon := by
    simpa [afterBound, Work.gateBound, Work.horizon] using hhorizon
  let afterFormulas := (emitStepFormulas tm.toNTM).effect afterBound
  have hformulas := emitStepFormulas_requires_preserves_forStep tm.toNTM
    afterBound hcleanAfterBound hhorizonAfterBound
  let afterBase := Function.update afterFormulas Work.configBase
    (afterFormulas Work.available)
  have hbaseCopy :
      (BinaryRoutine.binaryCopy Work.available Work.configBase
        Work.copyCounter).requires afterFormulas :=
    ⟨by decide, by decide, by decide,
      hformulas.2.movedHeadClean.caseClean.copyCounter⟩
  have hcleanAfterBase : StepClean afterBase :=
    hformulas.2.updateOuter_forStep afterFormulas Work.configBase
      (afterFormulas Work.available) (Or.inr (Or.inl rfl))
  let afterCount := Function.update afterBase Work.gateCount
    (afterBase Work.gateBound)
  have hcountCopy :
      (BinaryRoutine.binaryCopy Work.gateBound Work.gateCount
        Work.copyCounter).requires afterBase :=
    ⟨by decide, by decide, by decide,
      hcleanAfterBase.movedHeadClean.caseClean.copyCounter⟩
  have hcleanAfterCount : StepClean afterCount :=
    hcleanAfterBase.updateOuter_forStep afterBase Work.gateCount
      (afterBase Work.gateBound) (Or.inr (Or.inr rfl))
  have hpacked := emitStepPackedCopies_requires_preserves_forStep tm.toNTM
    afterCount hcleanAfterCount
  simp only [emitStep, BinaryRoutine.seqList, BinaryRoutine.seq,
    BinaryRoutine.binaryCopy, BinaryRoutine.clear]
  exact ⟨hboundCopy, hformulas.1, hbaseCopy, hcountCopy, hpacked.1,
    trivial, trivial, trivial⟩

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
