/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Effect

/-!
# Exact output of the direct packed-step generator

This file proves that the direct generator emits the canonical numeric step
schedule byte for byte.  The intermediate results identify each nested
enumeration with its contiguous slice of the global configuration-atom order.
-/


@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem StepClean.caseFormulaClean_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values) :
    CaseFormulaClean values := by
  have hupdate : Function.update values Work.position 0 = values := by
    funext i
    by_cases hi : i = Work.position
    · subst i
      simp [hclean.position]
    · simp [hi]
  simpa [hupdate] using hclean.movedHeadClean.caseClean

private theorem StepClean.movedHeadClean_atPosition_internal
    {values : BinaryValues WorkCount} (hclean : StepClean values)
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
    simpa [hupdate] using hclean.movedHeadClean.caseClean
  · simpa [Work.position, Work.limit₂] using hclean.movedHeadClean.limit₂
  · simpa [Work.position, Work.loop₁] using hclean.movedHeadClean.loop₁
  · simpa [Work.position, Work.savedOutput] using
      hclean.movedHeadClean.savedOutput
  · simpa [Work.position, Work.direction] using hclean.movedHeadClean.direction
  · simpa [Work.position, Work.atomKind] using hclean.movedHeadClean.atomKind

/-- The canonical formula-block size function specialized to one machine. -/
noncomputable def stepFormulaSizeAtSpecializedInternal (tm : NTM k)
    (T atomIndex : ℕ) : ℕ :=
  stepFormulaSizeAt (transitionCases tm).length (Fintype.card tm.Q) k T
    (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
    (effectCaseChoiceAt tm) atomIndex

/-- One canonical formula block specialized to one machine and choice wire zero. -/
noncomputable def stepFormulaBlockSpecializedInternal (tm : NTM k)
    (T configBase available atomIndex : ℕ) : CircuitCode.RawCircuit :=
  stepFormulaBlock (transitionCases tm).length (Fintype.card tm.Q) k T
    configBase 0 available (nextHaltStateIndex tm) (stepAtomKindAt tm T)
    (stepAtomStateIndexAt tm T) (stepAtomTapeIndexAt tm T)
    (stepAtomPositionAt tm T) (stepAtomSymbolIndexAt tm T)
    (stepAtomEffectSelectedAt tm T) (effectCaseChoiceAt tm)
    (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
    (effectCaseOutputSymbolIndexAt tm) (effectCaseWorkSymbolIndexAt tm)
    atomIndex

/-- One canonical delayed packed-copy gate specialized to one machine. -/
noncomputable def stepPackedCopySpecializedInternal (tm : NTM k)
    (T available atomIndex : ℕ) : CircuitCode.RawGate :=
  stepPackedCopyGate (transitionCases tm).length (Fintype.card tm.Q) k T
    available (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
    (effectCaseChoiceAt tm) atomIndex

private theorem stepConfigAtomAt_configIndex (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) :
    stepConfigAtomAt tm T (configIndex tm T atom) = atom := by
  unfold stepConfigAtomAt
  rw [dite_eq_left (configIndex_lt tm T atom)]
  have hindex :
      (⟨configIndex tm T atom, configIndex_lt tm T atom⟩ :
        Fin (configWidth tm T)) = configAtomEquiv tm T atom := by
    apply Fin.ext
    exact (configAtomEquiv_apply_val tm T atom).symm
  rw [hindex, Equiv.symm_apply_apply]

private theorem indexedGateBlocks_succ_last
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (count + 1) blockAt =
      indexedGateBlocks count blockAt ++ blockAt count := by
  induction count generalizing blockAt with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      change
        blockAt 0 ++ indexedGateBlocks (count + 1)
            (fun index => blockAt (index + 1)) =
          (blockAt 0 ++ indexedGateBlocks count
            (fun index => blockAt (index + 1))) ++ blockAt (count + 1)
      rw [ih (fun index => blockAt (index + 1))]
      simp [List.append_assoc]

private theorem indexedGateBlocks_add
    (firstCount secondCount : ℕ)
    (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (firstCount + secondCount) blockAt =
      indexedGateBlocks firstCount blockAt ++
        indexedGateBlocks secondCount
          (fun index => blockAt (firstCount + index)) := by
  induction secondCount with
  | zero => simp [indexedGateBlocks]
  | succ secondCount ih =>
      rw [show firstCount + (secondCount + 1) =
          (firstCount + secondCount) + 1 by omega,
        indexedGateBlocks_succ_last, ih,
        indexedGateBlocks_succ_last]
      simp [List.append_assoc]

private theorem indexedGateBlocks_group_four
    (count : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (4 * count) blockAt =
      indexedGateBlocks count fun position =>
        indexedGateBlocks 4 fun symbolIndex =>
          blockAt (4 * position + symbolIndex) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      calc
        indexedGateBlocks (4 * (count + 1)) blockAt =
            indexedGateBlocks (4 * count) blockAt ++
              indexedGateBlocks 4
                (fun index => blockAt (4 * count + index)) := by
              rw [show 4 * (count + 1) = 4 * count + 4 by omega,
                indexedGateBlocks_add]
        _ = (indexedGateBlocks count fun position =>
              indexedGateBlocks 4 fun symbolIndex =>
                blockAt (4 * position + symbolIndex)) ++
              indexedGateBlocks 4
                (fun index => blockAt (4 * count + index)) := by rw [ih]
        _ = indexedGateBlocks (count + 1) fun position =>
              indexedGateBlocks 4 fun symbolIndex =>
                blockAt (4 * position + symbolIndex) := by
              exact (indexedGateBlocks_succ_last count (fun position =>
                indexedGateBlocks 4 fun symbolIndex =>
                  blockAt (4 * position + symbolIndex))).symm

theorem indexedGateBlocks_group_internal (width count : ℕ)
    (blockAt : ℕ → CircuitCode.RawCircuit) :
    indexedGateBlocks (width * count) blockAt =
      indexedGateBlocks count fun group =>
        indexedGateBlocks width fun offset =>
          blockAt (width * group + offset) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      calc
        indexedGateBlocks (width * (count + 1)) blockAt =
            indexedGateBlocks (width * count) blockAt ++
              indexedGateBlocks width
                (fun offset => blockAt (width * count + offset)) := by
              rw [show width * (count + 1) = width * count + width by ring,
                indexedGateBlocks_add]
        _ = (indexedGateBlocks count fun group =>
              indexedGateBlocks width fun offset =>
                blockAt (width * group + offset)) ++
              indexedGateBlocks width
                (fun offset => blockAt (width * count + offset)) := by rw [ih]
        _ = _ := (indexedGateBlocks_succ_last count _).symm

private theorem list_ofFn_four (f : Fin 4 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
  rfl

private theorem binaryForValues_eq_trajectory
    (body : BinaryRoutine n) (counter : Fin n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index,
      BinaryRoutine.binaryForStep body counter (trajectory index) =
        trajectory (index + 1)) :
    ∀ count,
      BinaryRoutine.binaryForValues body counter initial count =
        trajectory count := by
  intro count
  induction count with
  | zero => exact hzero.symm
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues, ih, hstep]

private theorem binaryForEmitted_eq_indexedGateBlocks
    (body : BinaryRoutine n) (counter : Fin n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (blockAt : ℕ → CircuitCode.RawCircuit)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index,
      BinaryRoutine.binaryForStep body counter (trajectory index) =
        trajectory (index + 1))
    (hemitted : ∀ index,
      body.emitted (trajectory index) =
        (blockAt index).flatMap CircuitCode.RawGate.encode) :
    ∀ count,
      BinaryRoutine.binaryForEmitted body counter initial count =
        (indexedGateBlocks count blockAt).flatMap
          CircuitCode.RawGate.encode := by
  intro count
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted, ih,
        binaryForValues_eq_trajectory body counter initial trajectory hzero
          hstep count,
        hemitted, indexedGateBlocks_succ_last]
      simp [List.flatMap_append]

private theorem binaryForValues_eq_trajectory_bounded
    (body : BinaryRoutine n) (counter : Fin n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (count : ℕ) (hzero : trajectory 0 = initial)
    (hstep : ∀ index < count,
      BinaryRoutine.binaryForStep body counter (trajectory index) =
        trajectory (index + 1)) :
    BinaryRoutine.binaryForValues body counter initial count =
      trajectory count := by
  induction count with
  | zero => exact hzero.symm
  | succ count ih =>
      rw [BinaryRoutine.binaryForValues,
        ih (fun index hindex => hstep index (by omega)),
        hstep count (by omega)]

private theorem binaryForEmitted_eq_indexedGateBlocks_bounded
    (body : BinaryRoutine n) (counter : Fin n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (blockAt : ℕ → CircuitCode.RawCircuit) (count : ℕ)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index < count,
      BinaryRoutine.binaryForStep body counter (trajectory index) =
        trajectory (index + 1))
    (hemitted : ∀ index < count,
      body.emitted (trajectory index) =
        (blockAt index).flatMap CircuitCode.RawGate.encode) :
    BinaryRoutine.binaryForEmitted body counter initial count =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [BinaryRoutine.binaryForEmitted,
        ih (fun index hindex => hstep index (by omega))
          (fun index hindex => hemitted index (by omega)),
        binaryForValues_eq_trajectory_bounded body counter initial trajectory
          count hzero (fun index hindex => hstep index (by omega)),
        hemitted count (by omega), indexedGateBlocks_succ_last]
      simp [List.flatMap_append]

private theorem seqList_ofFn_effect_eq_trajectory
    (count : ℕ) (routineAt : Fin count → BinaryRoutine n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index : Fin count,
      (routineAt index).effect (trajectory index.val) =
        trajectory (index.val + 1)) :
    (BinaryRoutine.seqList (List.ofFn routineAt)).effect initial =
      trajectory count := by
  induction count generalizing initial trajectory with
  | zero => simpa [BinaryRoutine.seqList, BinaryRoutine.identity,
      BinaryRoutine.emitBits] using hzero.symm
  | succ count ih =>
      rw [← hzero, List.ofFn_succ]
      change
        (BinaryRoutine.seqList (List.ofFn fun index =>
          routineAt index.succ)).effect
            ((routineAt 0).effect (trajectory 0)) = trajectory (count + 1)
      have hstepZero := hstep 0
      simp only [Fin.val_zero] at hstepZero
      rw [hstepZero]
      apply ih (fun index => routineAt index.succ) (trajectory 1)
        (fun index => trajectory (index + 1))
      · rfl
      · intro index
        simpa [Nat.add_assoc] using hstep index.succ

private theorem seqList_ofFn_emitted_eq_indexedGateBlocks
    (count : ℕ) (routineAt : Fin count → BinaryRoutine n)
    (initial : BinaryValues n) (trajectory : ℕ → BinaryValues n)
    (blockAt : ℕ → CircuitCode.RawCircuit)
    (hzero : trajectory 0 = initial)
    (hstep : ∀ index : Fin count,
      (routineAt index).effect (trajectory index.val) =
        trajectory (index.val + 1))
    (hemitted : ∀ index : Fin count,
      (routineAt index).emitted (trajectory index.val) =
        (blockAt index.val).flatMap CircuitCode.RawGate.encode) :
    (BinaryRoutine.seqList (List.ofFn routineAt)).emitted initial =
      (indexedGateBlocks count blockAt).flatMap
        CircuitCode.RawGate.encode := by
  induction count generalizing initial trajectory blockAt with
  | zero => rfl
  | succ count ih =>
      rw [← hzero, List.ofFn_succ]
      change
        (routineAt 0).emitted (trajectory 0) ++
            (BinaryRoutine.seqList (List.ofFn fun index =>
              routineAt index.succ)).emitted
              ((routineAt 0).effect (trajectory 0)) =
          (indexedGateBlocks (count + 1) blockAt).flatMap
            CircuitCode.RawGate.encode
      have hstepZero := hstep 0
      have hemittedZero := hemitted 0
      simp only [Fin.val_zero] at hstepZero hemittedZero
      rw [hemittedZero, hstepZero]
      rw [ih (fun index => routineAt index.succ) (trajectory 1)
        (fun index => trajectory (index + 1))
        (fun index => blockAt (index + 1))]
      · simp [indexedGateBlocks, List.flatMap_append]
      · rfl
      · intro index
        simpa [Nat.add_assoc] using hstep index.succ
      · intro index
        simpa using hemitted index.succ

private theorem seqList_ofFn_emitted_congr
    (first second : Fin count → BinaryRoutine n)
    (heffect : ∀ index values,
      (first index).effect values = (second index).effect values)
    (hemitted : ∀ index values,
      (first index).emitted values = (second index).emitted values) :
    ∀ values,
      (BinaryRoutine.seqList (List.ofFn first)).emitted values =
        (BinaryRoutine.seqList (List.ofFn second)).emitted values := by
  intro values
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      change
        (first 0).emitted values ++
            (BinaryRoutine.seqList (List.ofFn fun index =>
              first index.succ)).emitted ((first 0).effect values) =
          (second 0).emitted values ++
            (BinaryRoutine.seqList (List.ofFn fun index =>
              second index.succ)).emitted ((second 0).effect values)
      rw [hemitted 0 values, heffect 0 values]
      congr 1
      apply ih
      · intro index current
        exact heffect index.succ current
      · intro index current
        exact hemitted index.succ current

private theorem seqList_ofFn_emitted_congr_of_invariant
    (first second : Fin count → BinaryRoutine n)
    (invariant : BinaryValues n → Prop) (values : BinaryValues n)
    (hinvariant : invariant values)
    (heffect : ∀ index current, invariant current →
      (first index).effect current = (second index).effect current)
    (hemitted : ∀ index current, invariant current →
      (first index).emitted current = (second index).emitted current)
    (hpreserve : ∀ index current, invariant current →
      invariant ((first index).effect current)) :
    (BinaryRoutine.seqList (List.ofFn first)).emitted values =
      (BinaryRoutine.seqList (List.ofFn second)).emitted values := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      change
        (first 0).emitted values ++
            (BinaryRoutine.seqList (List.ofFn fun index =>
              first index.succ)).emitted ((first 0).effect values) =
          (second 0).emitted values ++
            (BinaryRoutine.seqList (List.ofFn fun index =>
              second index.succ)).emitted ((second 0).effect values)
      rw [hemitted 0 values hinvariant]
      congr 1
      calc
        (BinaryRoutine.seqList (List.ofFn fun index =>
            first index.succ)).emitted ((first 0).effect values) =
            (BinaryRoutine.seqList (List.ofFn fun index =>
              second index.succ)).emitted ((first 0).effect values) := by
              apply ih (fun index => first index.succ)
                (fun index => second index.succ) ((first 0).effect values)
                (hpreserve 0 values hinvariant)
              · intro index current hcurrent
                exact heffect index.succ current hcurrent
              · intro index current hcurrent
                exact hemitted index.succ current hcurrent
              · intro index current hcurrent
                exact hpreserve index.succ current hcurrent
        _ = (BinaryRoutine.seqList (List.ofFn fun index =>
              second index.succ)).emitted ((second 0).effect values) := by
              rw [heffect 0 values hinvariant]

private theorem CaseFormulaClean.updateAvailable_emitted_internal
    {values : BinaryValues WorkCount} (hclean : CaseFormulaClean values)
    (value : ℕ) :
    CaseFormulaClean (Function.update values Work.available value) := by
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
    | simpa [Work.available, Work.position] using hclean.position
    | simpa [Work.available, Work.loop₀] using hclean.loop₀
    | simpa [Work.available, Work.limit₀] using hclean.limit₀
    | simpa [Work.available, Work.reference₀] using hclean.reference₀
    | simpa [Work.available, Work.reference₁] using hclean.reference₁
    | simpa [Work.available, Work.emitCounter] using hclean.emitCounter
    | simpa [Work.available, Work.copyCounter] using hclean.copyCounter
    | simpa [Work.available, Work.multiplyCounter] using hclean.multiplyCounter
    | simpa [Work.available, Work.addCounter] using hclean.addCounter
    | simpa [Work.available, Work.temporary₀] using hclean.temporary₀
    | simpa [Work.available, Work.temporary₁] using hclean.temporary₁
    | simpa [Work.available, Work.temporary₂] using hclean.temporary₂
    | simpa [Work.available, Work.loop₃] using hclean.loop₃
    | simpa [Work.available, Work.temporary₃] using hclean.temporary₃
    | simpa [Work.available, Work.polynomialScratch] using
        hclean.polynomialScratch
    | simpa [Work.available, Work.tapeIndex] using hclean.tapeIndex
    | simpa [Work.available, Work.symbolIndex] using hclean.symbolIndex

theorem MovedHeadFormulaClean.updateAvailable_emitted_internal
    {values : BinaryValues WorkCount}
    (hclean : MovedHeadFormulaClean values) (value : ℕ) :
    MovedHeadFormulaClean
      (Function.update values Work.available value) := by
  refine
    { caseClean := ?_
      limit₂ := ?_
      loop₁ := ?_
      savedOutput := ?_
      direction := ?_
      atomKind := ?_ }
  · have hcommute :
        Function.update (Function.update values Work.available value)
            Work.position 0 =
          Function.update (Function.update values Work.position 0)
            Work.available value := by
      funext i
      by_cases hposition : i = Work.position
      · subst i
        simp [Work.position, Work.available]
      · by_cases havailable : i = Work.available
        · subst i
          simp [Work.position, Work.available] at hposition ⊢
        · simp [hposition, havailable]
    rw [hcommute]
    exact hclean.caseClean.updateAvailable_emitted_internal value
  all_goals
    first
    | simpa [Work.available, Work.limit₂] using hclean.limit₂
    | simpa [Work.available, Work.loop₁] using hclean.loop₁
    | simpa [Work.available, Work.savedOutput] using hclean.savedOutput
    | simpa [Work.available, Work.direction] using hclean.direction
    | simpa [Work.available, Work.atomKind] using hclean.atomKind

private theorem StepClean.movedHeadAtPositionAvailable_emitted
    {values : BinaryValues WorkCount} (hclean : StepClean values)
    (position available : ℕ) :
    MovedHeadFormulaClean
      (Function.update (Function.update values Work.position position)
        Work.available available) := by
  apply MovedHeadFormulaClean.updateAvailable_emitted_internal
  exact hclean.movedHeadClean_atPosition_internal position

private theorem MovedHeadFormulaClean.atPositionAvailable_emitted
    {values : BinaryValues WorkCount}
    (hclean : MovedHeadFormulaClean values) (position available : ℕ) :
    MovedHeadFormulaClean
      (Function.update (Function.update values Work.position position)
        Work.available available) := by
  apply MovedHeadFormulaClean.updateAvailable_emitted_internal
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

private theorem stateAtom_index (tm : NTM k)
    (index : Fin (Fintype.card tm.Q)) :
    configIndex tm T (.state ((Fintype.equivFin tm.Q).symm index)) =
      index.val := by
  unfold configIndex stateIndex
  exact congrArg Fin.val ((Fintype.equivFin tm.Q).apply_symm_apply index)

private theorem stepFormulaSizeAtSpecialized_internal_state (tm : NTM k) (T : ℕ)
    (index : Fin (Fintype.card tm.Q)) :
    stepFormulaSizeAtSpecializedInternal tm T index.val =
      nextStateFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState =
            (Fintype.equivFin tm.Q).symm index))
        (effectCaseChoiceAt tm) := by
  unfold stepFormulaSizeAtSpecializedInternal stepFormulaSizeAt
  rw [ite_eq_left]
  · unfold stepAtomKindAt stepAtomEffectSelectedAt
    rw [← stateAtom_index tm index,
      stepConfigAtomAt_configIndex tm T]
    rfl
  · unfold stepAtomCount
    omega

/-- The specialized numeric size oracle agrees with the state-formula
polynomial at every canonical state index. -/
theorem stepFormulaSizeAtSpecialized_state_forSpace_internal (tm : NTM k)
    (T : ℕ) (index : Fin (Fintype.card tm.Q)) :
    stepFormulaSizeAtSpecializedInternal tm T index.val =
      nextStateFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState =
            (Fintype.equivFin tm.Q).symm index))
        (effectCaseChoiceAt tm) :=
  stepFormulaSizeAtSpecialized_internal_state tm T index

private theorem stepFormulaBlockSpecialized_internal_state (tm : NTM k)
    (T configBase available : ℕ) (index : Fin (Fintype.card tm.Q)) :
    stepFormulaBlockSpecializedInternal tm T configBase available index.val =
      nextStateFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase 0
        (available + prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
          index.val)
        (stateIndex tm ((Fintype.equivFin tm.Q).symm index))
        (stateIndex tm tm.qhalt)
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState =
            (Fintype.equivFin tm.Q).symm index))
        (effectCaseChoiceAt tm) (effectCaseStateIndexAt tm)
        (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold stepFormulaBlockSpecializedInternal stepFormulaBlock stepFormulaAvailable
    nextHaltStateIndex stepAtomKindAt stepAtomStateIndexAt
    stepAtomTapeIndexAt stepAtomPositionAt stepAtomSymbolIndexAt
    stepAtomEffectSelectedAt
  rw [← stateAtom_index tm index,
    stepConfigAtomAt_configIndex tm T]
  rfl

/-- Exact encoded prefix for the state-atom formula subroutine. -/
theorem emitStepStateFormulas_emitted_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values) :
    (emitStepStateFormulas tm).emitted values =
      (indexedGateBlocks (Fintype.card tm.Q) fun atomIndex =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) (values Work.available) atomIndex).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update values Work.available
      (values Work.available + prefixSize sizeAt count)
  unfold emitStepStateFormulas
  apply seqList_ofFn_emitted_eq_indexedGateBlocks
    (Fintype.card tm.Q)
    (fun stateIndex =>
      emitNextStateFormula tm ((Fintype.equivFin tm.Q).symm stateIndex))
    values trajectory
    (fun atomIndex => stepFormulaBlockSpecializedInternal tm
      (values Work.horizon) (values Work.configBase)
      (values Work.available) atomIndex)
  · funext i
    simp [trajectory]
  · intro index
    have hcase := hclean.caseFormulaClean_internal.updateAvailable_emitted_internal
      (values Work.available + prefixSize sizeAt index.val)
    rw [emitNextStateFormula_effect tm
      ((Fintype.equivFin tm.Q).symm index) (trajectory index.val) hcase]
    have hhorizon :
        trajectory index.val Work.horizon = values Work.horizon := by
      simp [trajectory, Work.available, Work.horizon]
    funext i
    by_cases hi : i = Work.available
    · subst i
      simp [trajectory, sizeAt, hhorizon, prefixSize_succ,
        stepFormulaSizeAtSpecialized_internal_state tm (values Work.horizon) index]
      omega
    · simp [trajectory, hi]
  · intro index
    have hcase := hclean.caseFormulaClean_internal.updateAvailable_emitted_internal
      (values Work.available + prefixSize sizeAt index.val)
    rw [emitNextStateFormula_emitted tm
      ((Fintype.equivFin tm.Q).symm index) (trajectory index.val) hcase]
    rw [stepFormulaBlockSpecialized_internal_state]
    have href : values Work.reference₀ = 0 := by
      simpa [Work.position, Work.reference₀] using
        hclean.movedHeadClean.caseClean.reference₀
    have hrefTrajectory : trajectory index.val Work.reference₀ = 0 := by
      rw [show trajectory index.val Work.reference₀ =
          values Work.reference₀ by
        simp [trajectory, Work.available, Work.reference₀]]
      exact href
    rw [hrefTrajectory]
    simp [trajectory, sizeAt, Work.available, Work.horizon, Work.configBase]

private theorem stepFormulaSizeAtSpecialized_internal_head (tm : NTM k) (T : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 1)) :
    stepFormulaSizeAtSpecializedInternal tm T
        (configIndex tm T (.head tape position)) =
      nextHeadFormulaScheduleSize (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm) := by
  unfold stepFormulaSizeAtSpecializedInternal stepFormulaSizeAt
  rw [ite_eq_left (by simpa [stepAtomCount, configWidth]
    using! configIndex_lt tm T (.head tape position))]
  unfold stepAtomKindAt stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  rfl

private theorem stepFormulaBlockSpecialized_internal_head (tm : NTM k)
    (T configBase available : ℕ) (tape : TapeSlot k)
    (position : Fin (T + 1)) :
    stepFormulaBlockSpecializedInternal tm T configBase available
        (configIndex tm T (.head tape position)) =
      nextHeadFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase 0
        (available + prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
          (configIndex tm T (.head tape position)))
        tape.index position.val (stateIndex tm tm.qhalt)
        (movedHeadCaseSelectedAt tm tape) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold stepFormulaBlockSpecializedInternal stepFormulaBlock stepFormulaAvailable
    nextHaltStateIndex stepAtomKindAt stepAtomStateIndexAt
    stepAtomTapeIndexAt stepAtomPositionAt stepAtomSymbolIndexAt
    stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  rfl

private theorem stepFormulaSizeAtSpecialized_internal_cellCopy (tm : NTM k)
    (T : ℕ) (tape : TapeSlot k) (position : Fin (T + 2)) (symbol : Γ)
    (hcopy : tape = .input ∨ position.val = 0) :
    stepFormulaSizeAtSpecializedInternal tm T
        (configIndex tm T (.cell tape position symbol)) = 1 := by
  unfold stepFormulaSizeAtSpecializedInternal stepFormulaSizeAt
  rw [ite_eq_left (by simpa [stepAtomCount, configWidth]
    using! configIndex_lt tm T (.cell tape position symbol))]
  unfold stepAtomKindAt stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  rcases hcopy with rfl | hzero
  · rfl
  · cases tape <;> simp [nextAtomKind, hzero, nextStateAtomKind,
      nextHeadAtomKind, nextInputCellAtomKind, nextWritableMarkerAtomKind,
      nextWritableCellAtomKind, nextFormulaScheduleSize,
      nextCellCopyScheduleSize]

private theorem stepFormulaBlockSpecialized_internal_cellCopy (tm : NTM k)
    (T configBase available : ℕ) (tape : TapeSlot k)
    (position : Fin (T + 2)) (symbol : Γ)
    (hcopy : tape = .input ∨ position.val = 0) :
    stepFormulaBlockSpecializedInternal tm T configBase available
        (configIndex tm T (.cell tape position symbol)) =
      nextCellCopySchedule (Fintype.card tm.Q) (k + 2) T configBase
        tape.index position.val (CircuitUnrolling.symbolIndex symbol) := by
  unfold stepFormulaBlockSpecializedInternal stepFormulaBlock stepFormulaAvailable
    nextHaltStateIndex stepAtomKindAt stepAtomStateIndexAt
    stepAtomTapeIndexAt stepAtomPositionAt stepAtomSymbolIndexAt
    stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  rcases hcopy with rfl | hzero
  · rfl
  · cases tape <;> simp [nextFormulaSchedule, nextAtomKind, hzero,
      nextStateAtomKind, nextHeadAtomKind, nextInputCellAtomKind,
      nextWritableMarkerAtomKind, nextWritableCellAtomKind,
      nextAtomTapeIndex, nextAtomPosition, nextAtomSymbolIndex]

private theorem stepFormulaSizeAtSpecialized_internal_writtenCell (tm : NTM k)
    (T : ℕ) (tape : WritableSlot k) (position : Fin (T + 2))
    (symbol : Γ) (hpositive : 0 < position.val) :
    stepFormulaSizeAtSpecializedInternal tm T
        (configIndex tm T (.cell tape.toTapeSlot position symbol)) =
      nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape symbol)
        (effectCaseChoiceAt tm) := by
  unfold stepFormulaSizeAtSpecializedInternal stepFormulaSizeAt
  rw [ite_eq_left (by simpa [stepAtomCount, configWidth]
    using! configIndex_lt tm T (.cell tape.toTapeSlot position symbol))]
  unfold stepAtomKindAt stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  cases tape <;> simp [WritableSlot.toTapeSlot, nextAtomKind,
    nextStateAtomKind, nextHeadAtomKind, nextWritableCellAtomKind,
    nextFormulaScheduleSize, nextWrittenCellFormulaScheduleSize,
    nextAtomEffectSelectedAt, hpositive.ne']

private theorem stepFormulaBlockSpecialized_internal_writtenCell (tm : NTM k)
    (T configBase available : ℕ) (tape : WritableSlot k)
    (position : Fin (T + 2)) (symbol : Γ)
    (hpositive : 0 < position.val) :
    stepFormulaBlockSpecializedInternal tm T configBase available
        (configIndex tm T (.cell tape.toTapeSlot position symbol)) =
      nextWrittenCellFormulaSchedule (transitionCases tm).length
        (Fintype.card tm.Q) k T configBase 0
        (available + prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
          (configIndex tm T (.cell tape.toTapeSlot position symbol)))
        tape.toTapeSlot.index position.val
        (CircuitUnrolling.symbolIndex symbol) (stateIndex tm tm.qhalt)
        (writtenCellEffectSelectedAt tm tape symbol) (effectCaseChoiceAt tm)
        (effectCaseStateIndexAt tm) (effectCaseInputSymbolIndexAt tm)
        (effectCaseOutputSymbolIndexAt tm)
        (effectCaseWorkSymbolIndexAt tm) := by
  unfold stepFormulaBlockSpecializedInternal stepFormulaBlock stepFormulaAvailable
    nextHaltStateIndex stepAtomKindAt stepAtomStateIndexAt
    stepAtomTapeIndexAt stepAtomPositionAt stepAtomSymbolIndexAt
    stepAtomEffectSelectedAt
  rw [stepConfigAtomAt_configIndex]
  unfold stepFormulaSizeAtSpecializedInternal
  unfold stepAtomKindAt stepAtomEffectSelectedAt
  cases tape <;> simp [WritableSlot.toTapeSlot, nextFormulaSchedule,
    nextAtomKind, nextStateAtomKind, nextHeadAtomKind,
    nextInputCellAtomKind, nextWritableMarkerAtomKind,
    nextWritableCellAtomKind, nextAtomTapeIndex, nextAtomPosition,
    nextAtomSymbolIndex, nextAtomEffectSelectedAt, hpositive.ne']

/-- First flattened configuration index for the four symbols at a tape cell. -/
def stepCellStart (tm : NTM k) (T : ℕ) (tape : TapeSlot k)
    (position : ℕ) : ℕ :=
  Fintype.card tm.Q + (k + 2) * (T + 1) +
    (tape.index.val * (T + 2) + position) * 4

private theorem stepFormulaSizeAtSpecialized_internal_cellCopyIndex (tm : NTM k)
    (T : ℕ) (tape : TapeSlot k) (position : Fin (T + 2))
    (symbolIndex : Fin 4) (hcopy : tape = .input ∨ position.val = 0) :
    stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T tape position.val + symbolIndex.val) = 1 := by
  have hsymbolIndex := congrArg Fin.val
    (symbolEquiv.apply_symm_apply symbolIndex)
  change (CircuitUnrolling.symbolIndex
    (symbolEquiv.symm symbolIndex)).val = symbolIndex.val at hsymbolIndex
  have hindex :
      stepCellStart tm T tape position.val + symbolIndex.val =
        configIndex tm T
          (.cell tape position (symbolEquiv.symm symbolIndex)) := by
    simp [stepCellStart, configIndex, hsymbolIndex]
  rw [hindex]
  exact stepFormulaSizeAtSpecialized_internal_cellCopy tm T tape position
    (symbolEquiv.symm symbolIndex) hcopy

private theorem stepFormulaSizeAtSpecialized_internal_writtenCellIndex (tm : NTM k)
    (T : ℕ) (tape : WritableSlot k) (position : Fin (T + 2))
    (symbolIndex : Fin 4) (hpositive : 0 < position.val) :
    stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T tape.toTapeSlot position.val + symbolIndex.val) =
      nextWrittenCellFormulaScheduleSize (transitionCases tm).length k T
        (writtenCellEffectSelectedAt tm tape (symbolEquiv.symm symbolIndex))
        (effectCaseChoiceAt tm) := by
  have hsymbolIndex := congrArg Fin.val
    (symbolEquiv.apply_symm_apply symbolIndex)
  change (CircuitUnrolling.symbolIndex
    (symbolEquiv.symm symbolIndex)).val = symbolIndex.val at hsymbolIndex
  have hindex :
      stepCellStart tm T tape.toTapeSlot position.val + symbolIndex.val =
        configIndex tm T
          (.cell tape.toTapeSlot position (symbolEquiv.symm symbolIndex)) := by
    simp [stepCellStart, configIndex, hsymbolIndex]
  rw [hindex]
  exact stepFormulaSizeAtSpecialized_internal_writtenCell tm T tape position
    (symbolEquiv.symm symbolIndex) hpositive

private def fourSize (sizeAt : ℕ → ℕ) (start : ℕ) : ℕ :=
  sizeAt start + sizeAt (start + 1) + sizeAt (start + 2) +
    sizeAt (start + 3)

private theorem prefixSize_add_four (sizeAt : ℕ → ℕ) (start : ℕ) :
    prefixSize sizeAt (start + 4) =
      prefixSize sizeAt start + fourSize sizeAt start := by
  simp [fourSize, prefixSize_succ]
  omega

private noncomputable def stepCellPositionSizeEmitted (tm : NTM k)
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

private theorem stepCellPositionEffectSize_eq_fourSize (tm : NTM k)
    (tape : TapeSlot k) (T position : ℕ) (hposition : position < T + 2) :
    stepCellPositionSizeEmitted tm tape T position =
      fourSize (stepFormulaSizeAtSpecializedInternal tm T)
        (stepCellStart tm T tape position) := by
  let pos : Fin (T + 2) := ⟨position, hposition⟩
  cases tape with
  | input =>
      have h₀ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T .input pos
        (0 : Fin 4) (Or.inl rfl)
      have h₁ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T .input pos
        (1 : Fin 4) (Or.inl rfl)
      have h₂ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T .input pos
        (2 : Fin 4) (Or.inl rfl)
      have h₃ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T .input pos
        (3 : Fin 4) (Or.inl rfl)
      change stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T .input position + 0) = 1 at h₀
      change stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T .input position + 1) = 1 at h₁
      change stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T .input position + 2) = 1 at h₂
      change stepFormulaSizeAtSpecializedInternal tm T
        (stepCellStart tm T .input position + 3) = 1 at h₃
      simp only [Nat.add_zero] at h₀
      unfold stepCellPositionSizeEmitted fourSize
      rw [h₀, h₁, h₂, h₃]
  | work index =>
      by_cases hzero : position = 0
      · subst position
        have h₀ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          (.work index) pos (0 : Fin 4) (Or.inr (by simp [pos]))
        have h₁ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          (.work index) pos (1 : Fin 4) (Or.inr (by simp [pos]))
        have h₂ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          (.work index) pos (2 : Fin 4) (Or.inr (by simp [pos]))
        have h₃ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          (.work index) pos (3 : Fin 4) (Or.inr (by simp [pos]))
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) 0 + 0) = 1 at h₀
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) 0 + 1) = 1 at h₁
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) 0 + 2) = 1 at h₂
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) 0 + 3) = 1 at h₃
        simp only [Nat.add_zero] at h₀
        unfold stepCellPositionSizeEmitted fourSize
        rw [list_ofFn_four, h₀, h₁, h₂, h₃]
        rfl
      · have hpositive : 0 < pos.val := by simpa [pos] using Nat.pos_of_ne_zero hzero
        have h₀ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          (.work index) pos (0 : Fin 4) hpositive
        have h₁ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          (.work index) pos (1 : Fin 4) hpositive
        have h₂ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          (.work index) pos (2 : Fin 4) hpositive
        have h₃ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          (.work index) pos (3 : Fin 4) hpositive
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) position + 0) = _ at h₀
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) position + 1) = _ at h₁
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) position + 2) = _ at h₂
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T (.work index) position + 3) = _ at h₃
        simp only [Nat.add_zero] at h₀
        unfold stepCellPositionSizeEmitted fourSize
        simp only [ite_eq_right hzero]
        change (List.ofFn fun symbolIndex : Fin 4 =>
            nextWrittenCellFormulaScheduleSize
              (transitionCases tm).length k T
              (writtenCellEffectSelectedAt tm (.work index)
                (symbolEquiv.symm symbolIndex)) (effectCaseChoiceAt tm)).sum =
          stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T (.work index) position) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T (.work index) position + 1) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T (.work index) position + 2) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T (.work index) position + 3)
        rw [list_ofFn_four]
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [h₀, h₁, h₂, h₃]
        omega
  | output =>
      by_cases hzero : position = 0
      · subst position
        have h₀ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          .output pos (0 : Fin 4) (Or.inr (by simp [pos]))
        have h₁ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          .output pos (1 : Fin 4) (Or.inr (by simp [pos]))
        have h₂ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          .output pos (2 : Fin 4) (Or.inr (by simp [pos]))
        have h₃ := stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm T
          .output pos (3 : Fin 4) (Or.inr (by simp [pos]))
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output 0 + 0) = 1 at h₀
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output 0 + 1) = 1 at h₁
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output 0 + 2) = 1 at h₂
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output 0 + 3) = 1 at h₃
        simp only [Nat.add_zero] at h₀
        unfold stepCellPositionSizeEmitted fourSize
        rw [list_ofFn_four, h₀, h₁, h₂, h₃]
        rfl
      · have hpositive : 0 < pos.val := by simpa [pos] using Nat.pos_of_ne_zero hzero
        have h₀ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          .output pos (0 : Fin 4) hpositive
        have h₁ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          .output pos (1 : Fin 4) hpositive
        have h₂ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          .output pos (2 : Fin 4) hpositive
        have h₃ := stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm T
          .output pos (3 : Fin 4) hpositive
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output position + 0) = _ at h₀
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output position + 1) = _ at h₁
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output position + 2) = _ at h₂
        change stepFormulaSizeAtSpecializedInternal tm T
          (stepCellStart tm T .output position + 3) = _ at h₃
        simp only [Nat.add_zero] at h₀
        unfold stepCellPositionSizeEmitted fourSize
        simp only [ite_eq_right hzero]
        change (List.ofFn fun symbolIndex : Fin 4 =>
            nextWrittenCellFormulaScheduleSize
              (transitionCases tm).length k T
              (writtenCellEffectSelectedAt tm .output
                (symbolEquiv.symm symbolIndex)) (effectCaseChoiceAt tm)).sum =
          stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T .output position) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T .output position + 1) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T .output position + 2) +
            stepFormulaSizeAtSpecializedInternal tm T
                (stepCellStart tm T .output position + 3)
        rw [list_ofFn_four]
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
        rw [h₀, h₁, h₂, h₃]
        omega

/-- Exact global atom slice for one tape's head-formula loop. -/
theorem emitStepHeadTapeFormulas_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hhorizon : 0 < values Work.horizon)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + tape.index.val *
          (values Work.horizon + 1))) :
    (emitStepHeadTapeFormulas tm tape).emitted values =
      (indexedGateBlocks (values Work.horizon + 1) fun position =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + tape.index.val *
            (values Work.horizon + 1) + position)).flatMap
        CircuitCode.RawGate.encode := by
  let start := Fintype.card tm.Q + tape.index.val *
    (values Work.horizon + 1)
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update values Work.position count) Work.available
      (stepAvailable + prefixSize sizeAt (start + count))
  unfold emitStepHeadTapeFormulas
  change
    (BinaryRoutine.binaryFor (emitNextHeadFormula tm tape) Work.position
      Work.limit₁).emitted values ++ [] = _
  rw [List.append_nil]
  change BinaryRoutine.binaryForEmitted (emitNextHeadFormula tm tape)
    Work.position values (values Work.limit₁ - values Work.position) = _
  rw [hlimit, hposition, Nat.sub_zero]
  apply binaryForEmitted_eq_indexedGateBlocks_bounded
    (emitNextHeadFormula tm tape) Work.position values trajectory
    (fun position => stepFormulaBlockSpecializedInternal tm
      (values Work.horizon) (values Work.configBase) stepAvailable
      (start + position)) (values Work.horizon + 1)
  · funext i
    have hpositionUpdate :
        Function.update values Work.position 0 = values := by
      funext j
      by_cases hj : j = Work.position
      · subst j
        simp [hposition]
      · simp [hj]
    simp only [trajectory, Nat.add_zero, hpositionUpdate]
    rw [← havailable]
    simp
  · intro index hindex
    have htarget : index ≤ values Work.horizon := by omega
    have hmoved := hclean.atPositionAvailable_emitted index
      (stepAvailable + prefixSize sizeAt (start + index))
    unfold BinaryRoutine.binaryForStep
    rw [emitNextHeadFormula_effect tm tape (trajectory index) hmoved
      hhorizon]
    · funext i
      by_cases hpos : i = Work.position
      · subst i
        simp [trajectory, Work.position, Work.available]
      · by_cases havail : i = Work.available
        · subst i
          have hindexEq : start + index = configIndex tm
              (values Work.horizon) (.head tape ⟨index, by omega⟩) := by
            simp [start, configIndex]
          have hsize := stepFormulaSizeAtSpecialized_internal_head tm
            (values Work.horizon) tape ⟨index, by omega⟩
          rw [← hindexEq] at hsize
          change sizeAt (start + index) = _ at hsize
          change
            (stepAvailable + prefixSize sizeAt (start + index)) +
                nextHeadFormulaScheduleSize (transitionCases tm).length k
                  (values Work.horizon) (movedHeadCaseSelectedAt tm tape)
                  (effectCaseChoiceAt tm) =
              stepAvailable + prefixSize sizeAt (start + (index + 1))
          rw [show start + (index + 1) = (start + index) + 1 by omega,
            prefixSize_succ, hsize]
          omega
        · simp [trajectory, hpos, havail]
    · simpa [trajectory, Work.position, Work.available]
  · intro index hindex
    have htarget : index ≤ values Work.horizon := by omega
    have hmoved := hclean.atPositionAvailable_emitted index
      (stepAvailable + prefixSize sizeAt (start + index))
    rw [emitNextHeadFormula_emitted tm tape (trajectory index) hmoved]
    · have hindexEq : start + index = configIndex tm
          (values Work.horizon) (.head tape ⟨index, by omega⟩) := by
        simp [start, configIndex]
      rw [hindexEq, stepFormulaBlockSpecialized_internal_head]
      have href : values Work.reference₀ = 0 := by
        simpa [Work.position, Work.reference₀] using
          hclean.caseClean.reference₀
      simp only [show trajectory index Work.horizon = values Work.horizon by
          simp [trajectory, Work.position, Work.available, Work.horizon],
        show trajectory index Work.configBase = values Work.configBase by
          simp [trajectory, Work.position, Work.available, Work.configBase],
        show trajectory index Work.reference₀ = 0 by
          simpa [trajectory, Work.position, Work.available, Work.reference₀]
            using href,
        show trajectory index Work.available =
            stepAvailable + prefixSize sizeAt (start + index) by
          simp [trajectory, Work.position, Work.available],
        show trajectory index Work.position = index by
          simp [trajectory, Work.position, Work.available]]
      rfl
    · simpa [trajectory, Work.position, Work.available]
    · simpa [trajectory, Work.position, Work.available,
        Work.horizon] using htarget

/-- Exact four-atom slice for one immutable cell position. -/
theorem emitStepImmutableCellPosition_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position < values Work.horizon + 2)
    (hcopy : tape = .input ∨ values Work.position = 0)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
          (tape.index.val * (values Work.horizon + 2) +
            values Work.position) * 4)) :
    (emitStepImmutableCellPosition tm tape).emitted values =
      (indexedGateBlocks 4 fun symbolIndex =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
            (tape.index.val * (values Work.horizon + 2) +
              values Work.position) * 4 + symbolIndex)).flatMap
        CircuitCode.RawGate.encode := by
  let start := Fintype.card tm.Q + (k + 2) *
    (values Work.horizon + 1) +
      (tape.index.val * (values Work.horizon + 2) +
        values Work.position) * 4
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update values Work.available
      (stepAvailable + prefixSize sizeAt (start + count))
  unfold emitStepImmutableCellPosition
  apply seqList_ofFn_emitted_eq_indexedGateBlocks 4
    (fun symbolIndex => emitNextCellCopy (Fintype.card tm.Q) (k + 2)
      tape.index (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex)))
    values trajectory
    (fun symbolIndex => stepFormulaBlockSpecializedInternal tm
      (values Work.horizon) (values Work.configBase) stepAvailable
      (start + symbolIndex))
  · funext i
    simp only [trajectory, Nat.add_zero]
    rw [← havailable]
    simp
  · intro index
    have hmoved := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt (start + index.val))
    have htape : trajectory index.val Work.tapeIndex = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.tapeIndex] using
        hmoved.caseClean.tapeIndex
    have hsymbol : trajectory index.val Work.symbolIndex = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.symbolIndex] using
        hmoved.caseClean.symbolIndex
    have htemp₀ : trajectory index.val Work.temporary₀ = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.temporary₀] using
        hmoved.caseClean.temporary₀
    have htemp₁ : trajectory index.val Work.temporary₁ = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.temporary₁] using
        hmoved.caseClean.temporary₁
    have htemp₂ : trajectory index.val Work.temporary₂ = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.temporary₂] using
        hmoved.caseClean.temporary₂
    have href : trajectory index.val Work.reference₀ = 0 := by
      simpa [trajectory, Work.position, Work.available, Work.reference₀] using
        hmoved.caseClean.reference₀
    rw [emitNextCellCopy_effect _ _ _ _ (trajectory index.val) htape
      hsymbol htemp₀ htemp₁ htemp₂ href]
    funext i
    by_cases hi : i = Work.available
    · subst i
      have hindexEq : start + index.val = configIndex tm
          (values Work.horizon) (.cell tape
            ⟨values Work.position, hposition⟩
            (symbolEquiv.symm index)) := by
        simp only [start, configIndex]
        have hsymbolIndex := congrArg Fin.val
          (symbolEquiv.apply_symm_apply index)
        change (CircuitUnrolling.symbolIndex
          (symbolEquiv.symm index)).val = index.val at hsymbolIndex
        omega
      have hsize := stepFormulaSizeAtSpecialized_internal_cellCopy tm
        (values Work.horizon) tape ⟨values Work.position, hposition⟩
        (symbolEquiv.symm index) hcopy
      rw [← hindexEq] at hsize
      change sizeAt (start + index.val) = 1 at hsize
      change
        stepAvailable + prefixSize sizeAt (start + index.val) + 1 =
          stepAvailable + prefixSize sizeAt (start + (index.val + 1))
      rw [show start + (index.val + 1) = (start + index.val) + 1 by omega,
        prefixSize_succ, hsize]
      omega
    · simp [trajectory, hi]
  · intro index
    rw [emitNextCellCopy_emitted]
    have hindexEq : start + index.val = configIndex tm
        (values Work.horizon) (.cell tape
          ⟨values Work.position, hposition⟩
          (symbolEquiv.symm index)) := by
      simp only [start, configIndex]
      have hsymbolIndex := congrArg Fin.val
        (symbolEquiv.apply_symm_apply index)
      change (CircuitUnrolling.symbolIndex
        (symbolEquiv.symm index)).val = index.val at hsymbolIndex
      omega
    rw [hindexEq, stepFormulaBlockSpecialized_internal_cellCopy tm
      (values Work.horizon) (values Work.configBase) stepAvailable tape
      ⟨values Work.position, hposition⟩ (symbolEquiv.symm index) hcopy]
    simp [trajectory, Work.available, Work.horizon, Work.configBase,
      Work.position]

set_option maxHeartbeats 2000000 in
/-- Exact four-atom slice for one writable cell position. -/
theorem emitStepWritableCellPosition_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position < values Work.horizon + 2)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
          (tape.toTapeSlot.index.val * (values Work.horizon + 2) +
            values Work.position) * 4)) :
    (emitStepWritableCellPosition tm tape).emitted values =
      (indexedGateBlocks 4 fun symbolIndex =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
            (tape.toTapeSlot.index.val * (values Work.horizon + 2) +
              values Work.position) * 4 + symbolIndex)).flatMap
        CircuitCode.RawGate.encode := by
  let start := Fintype.card tm.Q + (k + 2) *
    (values Work.horizon + 1) +
      (tape.toTapeSlot.index.val * (values Work.horizon + 2) +
        values Work.position) * 4
  by_cases hzero : values Work.position = 0
  · let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
    let trajectory : ℕ → BinaryValues WorkCount := fun count =>
      Function.update values Work.available
        (stepAvailable + prefixSize sizeAt (start + count))
    let routineAt : Fin 4 → BinaryRoutine WorkCount := fun symbolIndex =>
      BinaryRoutine.branchZero Work.position
        (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index
          (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex)))
        (emitNextWrittenCellFormula tm tape (symbolEquiv.symm symbolIndex))
    let blockAt : ℕ → CircuitCode.RawCircuit := fun symbolIndex =>
      stepFormulaBlockSpecializedInternal tm (values Work.horizon)
        (values Work.configBase) stepAvailable (start + symbolIndex)
    rw [show emitStepWritableCellPosition tm tape =
        BinaryRoutine.seqList (List.ofFn routineAt) by rfl]
    change _ = (indexedGateBlocks 4 blockAt).flatMap
      CircuitCode.RawGate.encode
    apply seqList_ofFn_emitted_eq_indexedGateBlocks 4 routineAt values
      trajectory blockAt
    · funext i
      simp only [trajectory, Nat.add_zero]
      rw [← havailable]
      simp
    · intro index
      have hmoved := hclean.updateAvailable_emitted_internal
        (stepAvailable + prefixSize sizeAt (start + index.val))
      have htrajectoryZero : trajectory index.val Work.position = 0 := by
        simpa [trajectory, Work.available, Work.position] using hzero
      rw [show (BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)))
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index))).effect (trajectory index.val) =
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex
              (symbolEquiv.symm index))).effect (trajectory index.val) by
        simp [BinaryRoutine.branchZero, htrajectoryZero]]
      rw [emitNextCellCopy_effect]
      · funext i
        by_cases hi : i = Work.available
        · subst i
          have hindexEq : start + index.val = configIndex tm
              (values Work.horizon) (.cell tape.toTapeSlot
                ⟨values Work.position, hposition⟩
                (symbolEquiv.symm index)) := by
            simp only [start, configIndex]
            have hsymbolIndex := congrArg Fin.val
              (symbolEquiv.apply_symm_apply index)
            change (CircuitUnrolling.symbolIndex
              (symbolEquiv.symm index)).val = index.val at hsymbolIndex
            omega
          have hsize := stepFormulaSizeAtSpecialized_internal_cellCopy tm
            (values Work.horizon) tape.toTapeSlot
            ⟨values Work.position, hposition⟩ (symbolEquiv.symm index)
            (Or.inr hzero)
          rw [← hindexEq] at hsize
          change sizeAt (start + index.val) = 1 at hsize
          change
            stepAvailable + prefixSize sizeAt (start + index.val) + 1 =
              stepAvailable + prefixSize sizeAt (start + (index.val + 1))
          rw [show start + (index.val + 1) =
              (start + index.val) + 1 by omega, prefixSize_succ, hsize]
          omega
        · simp [trajectory, hi]
      all_goals
        first
        | simpa [trajectory, Work.position, Work.available,
            Work.tapeIndex] using hmoved.caseClean.tapeIndex
        | simpa [trajectory, Work.position, Work.available,
            Work.symbolIndex] using hmoved.caseClean.symbolIndex
        | simpa [trajectory, Work.position, Work.available,
            Work.temporary₀] using hmoved.caseClean.temporary₀
        | simpa [trajectory, Work.position, Work.available,
            Work.temporary₁] using hmoved.caseClean.temporary₁
        | simpa [trajectory, Work.position, Work.available,
            Work.temporary₂] using hmoved.caseClean.temporary₂
        | simpa [trajectory, Work.position, Work.available,
            Work.reference₀] using hmoved.caseClean.reference₀
    · intro index
      have htrajectoryZero : trajectory index.val Work.position = 0 := by
        simpa [trajectory, Work.available, Work.position] using hzero
      rw [show (BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)))
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index))).emitted (trajectory index.val) =
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex
              (symbolEquiv.symm index))).emitted (trajectory index.val) by
        simp [BinaryRoutine.branchZero, htrajectoryZero]]
      rw [emitNextCellCopy_emitted]
      have hindexEq : start + index.val = configIndex tm
          (values Work.horizon) (.cell tape.toTapeSlot
            ⟨values Work.position, hposition⟩
            (symbolEquiv.symm index)) := by
        simp only [start, configIndex]
        have hsymbolIndex := congrArg Fin.val
          (symbolEquiv.apply_symm_apply index)
        change (CircuitUnrolling.symbolIndex
          (symbolEquiv.symm index)).val = index.val at hsymbolIndex
        omega
      simp only [blockAt]
      rw [hindexEq, stepFormulaBlockSpecialized_internal_cellCopy tm
        (values Work.horizon) (values Work.configBase) stepAvailable
        tape.toTapeSlot ⟨values Work.position, hposition⟩
        (symbolEquiv.symm index) (Or.inr hzero)]
      simp [trajectory, Work.available, Work.horizon, Work.configBase,
        Work.position]
  · have hpositive : 0 < values Work.position := Nat.pos_of_ne_zero hzero
    let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
    let trajectory : ℕ → BinaryValues WorkCount := fun count =>
      Function.update values Work.available
        (stepAvailable + prefixSize sizeAt (start + count))
    let routineAt : Fin 4 → BinaryRoutine WorkCount := fun symbolIndex =>
      BinaryRoutine.branchZero Work.position
        (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
          tape.toTapeSlot.index
          (CircuitUnrolling.symbolIndex (symbolEquiv.symm symbolIndex)))
        (emitNextWrittenCellFormula tm tape (symbolEquiv.symm symbolIndex))
    let blockAt : ℕ → CircuitCode.RawCircuit := fun symbolIndex =>
      stepFormulaBlockSpecializedInternal tm (values Work.horizon)
        (values Work.configBase) stepAvailable (start + symbolIndex)
    rw [show emitStepWritableCellPosition tm tape =
        BinaryRoutine.seqList (List.ofFn routineAt) by rfl]
    change _ = (indexedGateBlocks 4 blockAt).flatMap
      CircuitCode.RawGate.encode
    apply seqList_ofFn_emitted_eq_indexedGateBlocks 4 routineAt values
      trajectory blockAt
    · funext i
      simp only [trajectory, Nat.add_zero]
      rw [← havailable]
      simp
    · intro index
      have hmoved := hclean.updateAvailable_emitted_internal
        (stepAvailable + prefixSize sizeAt (start + index.val))
      have hwritten : WrittenCellFormulaClean (trajectory index.val) :=
        { caseClean := hmoved.caseClean
          limit₂ := hmoved.limit₂
          savedOutput := hmoved.savedOutput }
      have htrajectoryPositive : trajectory index.val Work.position ≠ 0 := by
        simpa [trajectory, Work.available, Work.position] using hzero
      rw [show (BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)))
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index))).effect (trajectory index.val) =
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index)).effect (trajectory index.val) by
        simp [BinaryRoutine.branchZero, htrajectoryPositive]]
      rw [emitNextWrittenCellFormula_effect tm tape
        (symbolEquiv.symm index) (trajectory index.val) hwritten]
      funext i
      by_cases hi : i = Work.available
      · subst i
        have hindexEq : start + index.val = configIndex tm
            (values Work.horizon) (.cell tape.toTapeSlot
              ⟨values Work.position, hposition⟩
              (symbolEquiv.symm index)) := by
          simp only [start, configIndex]
          have hsymbolIndex := congrArg Fin.val
            (symbolEquiv.apply_symm_apply index)
          change (CircuitUnrolling.symbolIndex
            (symbolEquiv.symm index)).val = index.val at hsymbolIndex
          omega
        have hsize := stepFormulaSizeAtSpecialized_internal_writtenCell tm
          (values Work.horizon) tape ⟨values Work.position, hposition⟩
          (symbolEquiv.symm index) hpositive
        rw [← hindexEq] at hsize
        change sizeAt (start + index.val) = _ at hsize
        change
          stepAvailable + prefixSize sizeAt (start + index.val) +
              nextWrittenCellFormulaScheduleSize
                (transitionCases tm).length k (values Work.horizon)
                (writtenCellEffectSelectedAt tm tape
                  (symbolEquiv.symm index)) (effectCaseChoiceAt tm) =
            stepAvailable + prefixSize sizeAt (start + (index.val + 1))
        rw [show start + (index.val + 1) = (start + index.val) + 1 by omega,
          prefixSize_succ, hsize]
        omega
      · simp [trajectory, hi]
    · intro index
      have hmoved := hclean.updateAvailable_emitted_internal
        (stepAvailable + prefixSize sizeAt (start + index.val))
      have hwritten : WrittenCellFormulaClean (trajectory index.val) :=
        { caseClean := hmoved.caseClean
          limit₂ := hmoved.limit₂
          savedOutput := hmoved.savedOutput }
      have htrajectoryPositive : trajectory index.val Work.position ≠ 0 := by
        simpa [trajectory, Work.available, Work.position] using hzero
      rw [show (BinaryRoutine.branchZero Work.position
          (emitNextCellCopy (Fintype.card tm.Q) (k + 2)
            tape.toTapeSlot.index
            (CircuitUnrolling.symbolIndex (symbolEquiv.symm index)))
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index))).emitted (trajectory index.val) =
          (emitNextWrittenCellFormula tm tape
            (symbolEquiv.symm index)).emitted (trajectory index.val) by
        simp [BinaryRoutine.branchZero, htrajectoryPositive]]
      rw [emitNextWrittenCellFormula_emitted tm tape
        (symbolEquiv.symm index) (trajectory index.val) hwritten]
      · have hindexEq : start + index.val = configIndex tm
            (values Work.horizon) (.cell tape.toTapeSlot
              ⟨values Work.position, hposition⟩
              (symbolEquiv.symm index)) := by
          simp only [start, configIndex]
          have hsymbolIndex := congrArg Fin.val
            (symbolEquiv.apply_symm_apply index)
          change (CircuitUnrolling.symbolIndex
            (symbolEquiv.symm index)).val = index.val at hsymbolIndex
          omega
        simp only [blockAt]
        rw [hindexEq, stepFormulaBlockSpecialized_internal_writtenCell tm
          (values Work.horizon) (values Work.configBase) stepAvailable tape
          ⟨values Work.position, hposition⟩ (symbolEquiv.symm index)
          hpositive, ← hindexEq]
        have href : values Work.reference₀ = 0 := by
          simpa [Work.position, Work.reference₀] using
            hclean.caseClean.reference₀
        have hrefTrajectory : trajectory index.val Work.reference₀ = 0 := by
          rw [show trajectory index.val Work.reference₀ =
              values Work.reference₀ by
            simp [trajectory, Work.available, Work.reference₀]]
          exact href
        rw [hrefTrajectory]
        simp [trajectory, sizeAt, Work.available, Work.horizon,
          Work.configBase, Work.position]
      · simpa [trajectory, Work.available, Work.position,
          Work.horizon] using Nat.le_of_lt_succ hposition

/-- Exact packed-copy prefix for the state atoms. -/
theorem emitStepStateCopies_emitted_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (emitStepStateCopies tm).emitted values =
      (indexedGateBlocks (Fintype.card tm.Q) fun atomIndex =>
        [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
          atomIndex]).flatMap CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update values Work.gateCount
        (stepAvailable + prefixSize sizeAt count))
      Work.available (values Work.available + count)
  unfold emitStepStateCopies
  apply seqList_ofFn_emitted_eq_indexedGateBlocks (Fintype.card tm.Q)
    (fun stateIndex => emitPackedFormulaCopy
      (stateNextFormulaPolynomial tm
        ((Fintype.equivFin tm.Q).symm stateIndex))) values trajectory
    (fun atomIndex => [stepPackedCopySpecializedInternal tm
      (values Work.horizon) stepAvailable atomIndex])
  · funext i
    by_cases hgate : i = Work.gateCount
    · subst i
      change stepAvailable = values Work.gateCount
      exact hgateCount.symm
    · by_cases havailable : i = Work.available
      · subst i
        simp [trajectory, Work.gateCount, Work.available]
      · simp [trajectory, hgate, havailable]
  · intro index
    rw [emitPackedFormulaCopy_effect]
    have hsize := stepFormulaSizeAtSpecialized_internal_state tm
      (values Work.horizon) index
    rw [← stateNextFormulaPolynomial_eval] at hsize
    funext i
    by_cases hgate : i = Work.gateCount
    · subst i
      change stepAvailable + prefixSize sizeAt index.val +
          (stateNextFormulaPolynomial tm
            ((Fintype.equivFin tm.Q).symm index)).eval
              (values Work.horizon) =
        stepAvailable + prefixSize sizeAt (index.val + 1)
      change sizeAt index.val = _ at hsize
      rw [prefixSize_succ, hsize]
      omega
    · by_cases havailable : i = Work.available
      · subst i
        change values Work.available + index.val + 1 =
          values Work.available + (index.val + 1)
        omega
      · by_cases hreferenceIdx : i = Work.reference₀
        · subst i
          change 0 = values Work.reference₀
          exact hreference.symm
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            change 0 = values Work.temporary₃
            exact htemporary.symm
          · simp [trajectory, hgate, havailable, hreferenceIdx,
              htemporaryIdx]
  · intro index
    rw [emitPackedFormulaCopy_emitted]
    have hsize := stepFormulaSizeAtSpecialized_internal_state tm
      (values Work.horizon) index
    rw [← stateNextFormulaPolynomial_eval] at hsize
    unfold stepPackedCopySpecializedInternal stepPackedCopyGate stepFormulaOutputRef
    change sizeAt index.val = _ at hsize
    simp only [List.flatMap_singleton]
    change (CircuitCode.RawGate.copy
      (stepAvailable + prefixSize sizeAt index.val +
        (stateNextFormulaPolynomial tm
          ((Fintype.equivFin tm.Q).symm index)).eval
            (values Work.horizon) - 1)).encode = _
    rw [← hsize]
    change (CircuitCode.RawGate.copy
        (stepAvailable + prefixSize sizeAt index.val + sizeAt index.val - 1)).encode =
      (CircuitCode.RawGate.copy
        (stepAvailable + prefixSize sizeAt (index.val + 1) - 1)).encode
    rw [prefixSize_succ]
    simp [Nat.add_assoc]

private theorem seqListPackedCopies_emitted
    (polynomialAt : Fin count → Polynomial ℕ)
    (values : BinaryValues WorkCount) (sizeAt : ℕ → ℕ)
    (start stepAvailable : ℕ)
    (hgateCount : values Work.gateCount =
      stepAvailable + prefixSize sizeAt start)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0)
    (hsize : ∀ index : Fin count,
      (polynomialAt index).eval (values Work.horizon) =
        sizeAt (start + index.val)) :
    (BinaryRoutine.seqList
      (List.ofFn fun index => emitPackedFormulaCopy (polynomialAt index))).emitted
        values =
      (indexedGateBlocks count fun index =>
        [CircuitCode.RawGate.copy
          (stepAvailable + prefixSize sizeAt (start + index + 1) - 1)]).flatMap
        CircuitCode.RawGate.encode := by
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update
      (Function.update values Work.gateCount
        (stepAvailable + prefixSize sizeAt (start + index)))
      Work.available (values Work.available + index)
  apply seqList_ofFn_emitted_eq_indexedGateBlocks count
    (fun index => emitPackedFormulaCopy (polynomialAt index)) values trajectory
    (fun index => [CircuitCode.RawGate.copy
      (stepAvailable + prefixSize sizeAt (start + index + 1) - 1)])
  · funext i
    by_cases hgate : i = Work.gateCount
    · subst i
      change stepAvailable + prefixSize sizeAt (start + 0) =
        values Work.gateCount
      simpa using hgateCount.symm
    · by_cases havailable : i = Work.available
      · subst i
        simp [trajectory, Work.gateCount, Work.available]
      · simp [trajectory, hgate, havailable]
  · intro index
    rw [emitPackedFormulaCopy_effect]
    funext i
    by_cases hgate : i = Work.gateCount
    · subst i
      change stepAvailable + prefixSize sizeAt (start + index.val) +
          (polynomialAt index).eval (values Work.horizon) =
        stepAvailable + prefixSize sizeAt (start + (index.val + 1))
      rw [hsize index, show start + (index.val + 1) =
          (start + index.val) + 1 by omega, prefixSize_succ]
      omega
    · by_cases havailable : i = Work.available
      · subst i
        change values Work.available + index.val + 1 =
          values Work.available + (index.val + 1)
        omega
      · by_cases hreferenceIdx : i = Work.reference₀
        · subst i
          change 0 = values Work.reference₀
          exact hreference.symm
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            change 0 = values Work.temporary₃
            exact htemporary.symm
          · simp [trajectory, hgate, havailable, hreferenceIdx,
              htemporaryIdx]
  · intro index
    rw [emitPackedFormulaCopy_emitted]
    simp only [List.flatMap_singleton]
    change (CircuitCode.RawGate.copy
        (stepAvailable + prefixSize sizeAt (start + index.val) +
          (polynomialAt index).eval (values Work.horizon) - 1)).encode = _
    rw [hsize index, show start + index.val + 1 =
      (start + index.val) + 1 by omega, prefixSize_succ]
    simp [Nat.add_assoc]

/-- Four fixed one-gate delayed copies traverse four consecutive formulas. -/
theorem emitStepImmutableCellCopies_emitted_internal
    (values : BinaryValues WorkCount) (sizeAt : ℕ → ℕ)
    (start stepAvailable : ℕ)
    (hgateCount : values Work.gateCount =
      stepAvailable + prefixSize sizeAt start)
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0)
    (hsize : ∀ index : Fin 4, sizeAt (start + index.val) = 1) :
    emitStepImmutableCellCopies.emitted values =
      (indexedGateBlocks 4 fun index =>
        [CircuitCode.RawGate.copy
          (stepAvailable + prefixSize sizeAt (start + index + 1) - 1)]).flatMap
        CircuitCode.RawGate.encode := by
  unfold emitStepImmutableCellCopies BinaryRoutine.repeatRoutine
  rw [show List.replicate 4 (emitPackedFormulaCopy (Polynomial.C 1)) =
      List.ofFn fun _index : Fin 4 =>
        emitPackedFormulaCopy (Polynomial.C 1) by simp]
  apply seqListPackedCopies_emitted
    (fun _index : Fin 4 => Polynomial.C 1) values sizeAt start stepAvailable
    hgateCount hreference htemporary
  intro index
  simpa using (hsize index).symm

private theorem seqList_writableCopies_emitted_eq_packed
    (tm : NTM k) (tape : WritableSlot k) (symbols : List Γ)
    (values : BinaryValues WorkCount) :
    (BinaryRoutine.seqList (symbols.map fun symbol =>
      BinaryRoutine.branchZero Work.position
        (emitPackedFormulaCopy (Polynomial.C 1))
        (emitPackedFormulaCopy
          (writtenNextFormulaPolynomial tm tape symbol)))).emitted values =
      (BinaryRoutine.seqList ((symbols.map fun symbol =>
        if values Work.position = 0 then Polynomial.C 1 else
          writtenNextFormulaPolynomial tm tape symbol).map
            emitPackedFormulaCopy)).emitted values := by
  induction symbols generalizing values with
  | nil => rfl
  | cons symbol symbols ih =>
      simp only [List.map_cons, BinaryRoutine.seqList, BinaryRoutine.seq]
      by_cases hposition : values Work.position = 0
      · rw [show (BinaryRoutine.branchZero Work.position
            (emitPackedFormulaCopy (Polynomial.C 1))
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol))).emitted values =
            (emitPackedFormulaCopy (Polynomial.C 1)).emitted values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [show (BinaryRoutine.branchZero Work.position
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
              (writtenNextFormulaPolynomial tm tape symbol))).emitted values =
            (emitPackedFormulaCopy
              (writtenNextFormulaPolynomial tm tape symbol)).emitted values by
          simp [BinaryRoutine.branchZero, hposition]]
        rw [show (BinaryRoutine.branchZero Work.position
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

set_option maxHeartbeats 1000000 in
/-- Exact four-copy slice for one writable cell position. -/
theorem emitStepWritableCellCopies_emitted_internal (tm : NTM k)
    (tape : WritableSlot k) (values : BinaryValues WorkCount)
    (hposition : values Work.position < values Work.horizon + 2)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (stepCellStart tm (values Work.horizon) tape.toTapeSlot
          (values Work.position)))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (emitStepWritableCellCopies tm tape).emitted values =
      (indexedGateBlocks 4 fun index =>
        [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
          (stepCellStart tm (values Work.horizon) tape.toTapeSlot
            (values Work.position) + index)]).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let start := stepCellStart tm (values Work.horizon) tape.toTapeSlot
    (values Work.position)
  let polynomialAt : Fin 4 → Polynomial ℕ := fun symbolIndex =>
    if values Work.position = 0 then Polynomial.C 1
    else writtenNextFormulaPolynomial tm tape (symbolEquiv.symm symbolIndex)
  have hroutines :
      (emitStepWritableCellCopies tm tape).emitted values =
        (BinaryRoutine.seqList (List.ofFn fun index =>
          emitPackedFormulaCopy (polynomialAt index))).emitted values := by
    simpa [emitStepWritableCellCopies, polynomialAt] using
      seqList_writableCopies_emitted_eq_packed tm tape
        (List.ofFn symbolEquiv.symm) values
  rw [hroutines]
  have hemitted := seqListPackedCopies_emitted polynomialAt values sizeAt
    start stepAvailable hgateCount hreference htemporary
  apply hemitted
  intro index
  by_cases hzero : values Work.position = 0
  · rw [show polynomialAt index = Polynomial.C 1 by
      simp [polynomialAt, hzero]]
    simp only [Polynomial.eval_C]
    exact (stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm
      (values Work.horizon) tape.toTapeSlot
      ⟨values Work.position, hposition⟩ index (Or.inr hzero)).symm
  · rw [show polynomialAt index = writtenNextFormulaPolynomial tm tape
        (symbolEquiv.symm index) by simp [polynomialAt, hzero],
      writtenNextFormulaPolynomial_eval]
    exact (stepFormulaSizeAtSpecialized_internal_writtenCellIndex tm
      (values Work.horizon) tape ⟨values Work.position, hposition⟩ index
      (Nat.pos_of_ne_zero hzero)).symm

set_option maxHeartbeats 2000000 in
/-- Exact global atom slice for one tape's cell-formula loop. -/
theorem emitStepCellTapeFormulas_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hclean : MovedHeadFormulaClean values)
    (hpositionZero : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
          tape.index.val * (values Work.horizon + 2) * 4)) :
    (emitStepCellTapeFormulas tm tape).emitted values =
      (indexedGateBlocks (4 * (values Work.horizon + 2)) fun offset =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
            tape.index.val * (values Work.horizon + 2) * 4 + offset)).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let tapeStart := Fintype.card tm.Q + (k + 2) *
    (values Work.horizon + 1) +
      tape.index.val * (values Work.horizon + 2) * 4
  let body : BinaryRoutine WorkCount := match tape with
    | .input => emitStepImmutableCellPosition tm .input
    | .work index => emitStepWritableCellPosition tm (.work index)
    | .output => emitStepWritableCellPosition tm .output
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update values Work.position count) Work.available
      (stepAvailable + prefixSize sizeAt (tapeStart + 4 * count))
  have hstartAt (index : ℕ) :
      stepCellStart tm (values Work.horizon) tape index =
        tapeStart + 4 * index := by
    simp [stepCellStart, tapeStart]
    ring
  have hstep : ∀ index < values Work.horizon + 2,
      BinaryRoutine.binaryForStep body Work.position (trajectory index) =
        trajectory (index + 1) := by
    intro index hindex
    have hmoved := hclean.atPositionAvailable_emitted index
      (stepAvailable + prefixSize sizeAt (tapeStart + 4 * index))
    unfold BinaryRoutine.binaryForStep
    have heffect : body.effect (trajectory index) =
        Function.update (trajectory index) Work.available
          ((trajectory index) Work.available +
            stepCellPositionEffectSizeInternal tm tape (values Work.horizon) index) := by
      cases tape with
      | input =>
          simpa [body, trajectory, Work.position, Work.available,
            stepCellPositionEffectSizeInternal] using
            emitStepImmutableCellPosition_effect_internal tm .input
              (trajectory index) hmoved
      | work tapeIndex =>
          simpa [body, trajectory, Work.position, Work.available,
            Work.horizon] using! emitStepWritableCellPosition_effect_internal tm (.work tapeIndex)
              (trajectory index) hmoved
      | output =>
          simpa [body, trajectory, Work.position, Work.available,
            Work.horizon] using! emitStepWritableCellPosition_effect_internal tm .output
              (trajectory index) hmoved
    rw [heffect]
    have hsize := stepCellPositionEffectSize_eq_fourSize tm tape
      (values Work.horizon) index hindex
    funext i
    by_cases hpositionIdx : i = Work.position
    · subst i
      simp [trajectory, Work.position, Work.available]
    · by_cases havailableIdx : i = Work.available
      · subst i
        simp [trajectory, Work.position, Work.available] at hpositionIdx ⊢
        have heffectSize :
            stepCellPositionEffectSizeInternal tm tape (values Work.horizon) index =
              stepCellPositionSizeEmitted tm tape (values Work.horizon) index := by
          cases tape <;> rfl
        rw [heffectSize, hsize]
        change stepAvailable + prefixSize sizeAt (tapeStart + 4 * index) +
            fourSize sizeAt (stepCellStart tm (values Work.horizon) tape index) =
          stepAvailable + prefixSize sizeAt (tapeStart + 4 * (index + 1))
        rw [hstartAt, show tapeStart + 4 * (index + 1) =
          (tapeStart + 4 * index) + 4 by omega, prefixSize_add_four]
        omega
      · simp [trajectory, hpositionIdx, havailableIdx]
  have hemitted : ∀ index < values Work.horizon + 2,
      body.emitted (trajectory index) =
        (indexedGateBlocks 4 fun symbolIndex =>
          stepFormulaBlockSpecializedInternal tm (values Work.horizon)
            (values Work.configBase) stepAvailable
            (stepCellStart tm (values Work.horizon) tape index +
              symbolIndex)).flatMap
          CircuitCode.RawGate.encode := by
    intro index hindex
    have hmoved := hclean.atPositionAvailable_emitted index
      (stepAvailable + prefixSize sizeAt (tapeStart + 4 * index))
    have havailableAt : trajectory index Work.available = stepAvailable +
        prefixSize sizeAt
          (stepCellStart tm (values Work.horizon) tape index) := by
      change stepAvailable + prefixSize sizeAt (tapeStart + 4 * index) = _
      rw [hstartAt index]
    cases tape with
    | input =>
        simpa [body, trajectory, stepCellStart, Work.position, Work.horizon,
          Work.configBase] using! emitStepImmutableCellPosition_emitted_internal tm .input
            (trajectory index) hmoved (by simpa [trajectory, Work.position,
              Work.available, Work.horizon]) (Or.inl rfl) stepAvailable
            havailableAt
    | work tapeIndex =>
        simpa [body, trajectory, stepCellStart, Work.position, Work.horizon,
          Work.configBase] using! emitStepWritableCellPosition_emitted_internal tm (.work tapeIndex)
            (trajectory index) hmoved (by simpa [trajectory, Work.position,
              Work.available, Work.horizon]) stepAvailable havailableAt
    | output =>
        simpa [body, trajectory, stepCellStart, Work.position, Work.horizon,
          Work.configBase] using! emitStepWritableCellPosition_emitted_internal tm .output
            (trajectory index) hmoved (by simpa [trajectory, Work.position,
              Work.available, Work.horizon]) stepAvailable havailableAt
  have hemittedGlobal : ∀ index < values Work.horizon + 2,
      body.emitted (trajectory index) =
        (indexedGateBlocks 4 fun symbolIndex =>
          stepFormulaBlockSpecializedInternal tm (values Work.horizon)
            (values Work.configBase) stepAvailable
            (tapeStart + 4 * index + symbolIndex)).flatMap
          CircuitCode.RawGate.encode := by
    intro index hindex
    simpa only [hstartAt index] using hemitted index hindex
  have hglobalIndex (position symbolIndex : ℕ) :
      tapeStart + 4 * position + symbolIndex =
        Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
          tape.index.val * (values Work.horizon + 2) * 4 +
            (4 * position + symbolIndex) := by
    dsimp only [tapeStart]
    omega
  cases tape <;>
    unfold emitStepCellTapeFormulas <;>
    change BinaryRoutine.binaryForEmitted body Work.position values
        (values Work.limit₁ - values Work.position) ++ [] = _ <;>
    rw [List.append_nil, hlimit, hpositionZero, Nat.sub_zero,
      binaryForEmitted_eq_indexedGateBlocks_bounded body Work.position values
        trajectory (fun position => indexedGateBlocks 4 fun symbolIndex =>
          stepFormulaBlockSpecializedInternal tm (values Work.horizon)
            (values Work.configBase) stepAvailable
            (tapeStart + 4 * position + symbolIndex))
        (values Work.horizon + 2)
        (by
          funext i
          by_cases hpositionIdx : i = Work.position
          · subst i
            simpa [trajectory, Work.position, Work.available] using
              hpositionZero.symm
          · by_cases havailableIdx : i = Work.available
            · subst i
              simpa [trajectory, sizeAt, tapeStart, Work.position,
                Work.available] using havailable.symm
            · simp [trajectory, hpositionIdx, havailableIdx])
        hstep hemittedGlobal] <;>
    rw [indexedGateBlocks_group_four] <;>
    simp_rw [hglobalIndex]

/-- Exact delayed-copy slice for one tape's head atoms. -/
theorem emitStepHeadTapeCopies_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + tape.index.val *
          (values Work.horizon + 1)))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (emitStepHeadTapeCopies tm tape).emitted values =
      (indexedGateBlocks (values Work.horizon + 1) fun position =>
        [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
          (Fintype.card tm.Q + tape.index.val *
            (values Work.horizon + 1) + position)]).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let start := Fintype.card tm.Q + tape.index.val *
    (values Work.horizon + 1)
  let polynomial := headNextFormulaPolynomial tm tape
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update values Work.position count) Work.gateCount
              (stepAvailable + prefixSize sizeAt (start + count)))
            Work.available (values Work.available + count))
          Work.reference₀ 0) Work.temporary₃ 0
  have hsizeAt (index : ℕ) (hindex : index < values Work.horizon + 1) :
      polynomial.eval (values Work.horizon) = sizeAt (start + index) := by
    rw [headNextFormulaPolynomial_eval]
    have hindexEq : start + index = configIndex tm (values Work.horizon)
        (.head tape ⟨index, hindex⟩) := by
      simp [start, configIndex]
    rw [hindexEq]
    exact (stepFormulaSizeAtSpecialized_internal_head tm
      (values Work.horizon) tape ⟨index, hindex⟩).symm
  have hstep : ∀ index < values Work.horizon + 1,
      BinaryRoutine.binaryForStep (emitPackedFormulaCopy polynomial)
          Work.position (trajectory index) = trajectory (index + 1) := by
    intro index hindex
    unfold BinaryRoutine.binaryForStep
    rw [emitPackedFormulaCopy_effect]
    have hhorizon : trajectory index Work.horizon =
        values Work.horizon := by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃, Work.horizon]
    rw [hhorizon]
    funext i
    by_cases hpositionIdx : i = Work.position
    · subst i
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
    · by_cases hgateIdx : i = Work.gateCount
      · subst i
        simp [trajectory, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃]
        rw [hsizeAt index hindex]
        rw [show start + (index + 1) = (start + index) + 1 by omega,
          prefixSize_succ]
        omega
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.position, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃]
          omega
        · by_cases hreferenceIdx : i = Work.reference₀
          · subst i
            simp [trajectory, Work.position, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · by_cases htemporaryIdx : i = Work.temporary₃
            · subst i
              simp [trajectory, Work.position, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃]
            · simp [trajectory, hpositionIdx, hgateIdx, havailableIdx,
                hreferenceIdx, htemporaryIdx]
  unfold emitStepHeadTapeCopies
  change BinaryRoutine.binaryForEmitted (emitPackedFormulaCopy polynomial)
      Work.position values (values Work.limit₁ - values Work.position) ++
        [] = _
  rw [List.append_nil, hlimit, hposition, Nat.sub_zero]
  apply binaryForEmitted_eq_indexedGateBlocks_bounded
    (emitPackedFormulaCopy polynomial) Work.position values trajectory
    (fun position => [stepPackedCopySpecializedInternal tm
      (values Work.horizon) stepAvailable (start + position)])
    (values Work.horizon + 1)
  · funext i
    by_cases hpositionIdx : i = Work.position
    · subst i
      simpa [trajectory, Work.position, Work.gateCount, Work.available] using! hposition.symm
    · by_cases hgateIdx : i = Work.gateCount
      · subst i
        simpa [trajectory, sizeAt, start, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃] using
          hgateCount.symm
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.position, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃]
        · by_cases hreferenceIdx : i = Work.reference₀
          · subst i
            simpa [trajectory, Work.position, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using hreference.symm
          · by_cases htemporaryIdx : i = Work.temporary₃
            · subst i
              simpa [trajectory, Work.position, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃] using htemporary.symm
            · simp [trajectory, hpositionIdx, hgateIdx, havailableIdx,
                hreferenceIdx, htemporaryIdx]
  · exact hstep
  · intro index hindex
    rw [emitPackedFormulaCopy_emitted]
    unfold stepPackedCopySpecializedInternal stepPackedCopyGate stepFormulaOutputRef
    simp only [List.flatMap_singleton]
    change (CircuitCode.RawGate.copy
        (stepAvailable + prefixSize sizeAt (start + index) +
          polynomial.eval (values Work.horizon) - 1)).encode =
      (CircuitCode.RawGate.copy
        (stepAvailable + prefixSize sizeAt (start + index + 1) - 1)).encode
    rw [hsizeAt index hindex,
      show start + index + 1 = (start + index) + 1 by omega,
      prefixSize_succ]
    simp only [Nat.add_assoc]

set_option maxHeartbeats 2000000 in
/-- Exact delayed-copy slice for one tape's cell atoms. -/
theorem emitStepCellTapeCopies_emitted_internal (tm : NTM k)
    (tape : TapeSlot k) (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
          tape.index.val * (values Work.horizon + 2) * 4))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (emitStepCellTapeCopies tm tape).emitted values =
      (indexedGateBlocks (4 * (values Work.horizon + 2)) fun offset =>
        [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
          (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
            tape.index.val * (values Work.horizon + 2) * 4 + offset)]).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm (values Work.horizon)
  let start := Fintype.card tm.Q + (k + 2) *
    (values Work.horizon + 1) +
      tape.index.val * (values Work.horizon + 2) * 4
  let body : BinaryRoutine WorkCount := match tape with
    | .input => emitStepImmutableCellCopies
    | .work index => emitStepWritableCellCopies tm (.work index)
    | .output => emitStepWritableCellCopies tm .output
  let trajectory : ℕ → BinaryValues WorkCount := fun count =>
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update values Work.position count) Work.gateCount
              (stepAvailable + prefixSize sizeAt (start + 4 * count)))
            Work.available (values Work.available + 4 * count))
          Work.reference₀ 0) Work.temporary₃ 0
  have hstep : ∀ index < values Work.horizon + 2,
      BinaryRoutine.binaryForStep body Work.position (trajectory index) =
        trajectory (index + 1) := by
    intro index hindex
    unfold BinaryRoutine.binaryForStep
    have heffect : body.effect (trajectory index) =
        Function.update
          (Function.update
            (Function.update
              (Function.update (trajectory index) Work.gateCount
                ((trajectory index) Work.gateCount +
                  stepCellPositionEffectSizeInternal tm tape
                    (values Work.horizon) index))
              Work.available ((trajectory index) Work.available + 4))
            Work.reference₀ 0) Work.temporary₃ 0 := by
      cases tape with
      | input =>
          simpa [body, trajectory, stepCellPositionEffectSizeInternal, Work.position,
            Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃] using
            emitStepImmutableCellCopies_effect_internal (trajectory index)
      | work tapeIndex =>
          simpa [body, trajectory, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃,
            Work.horizon] using! emitStepWritableCellCopies_effect_internal tm (.work tapeIndex)
              (trajectory index)
      | output =>
          simpa [body, trajectory, Work.position, Work.gateCount,
            Work.available, Work.reference₀, Work.temporary₃,
            Work.horizon] using! emitStepWritableCellCopies_effect_internal tm .output
              (trajectory index)
    rw [heffect]
    have heffectSize : stepCellPositionEffectSizeInternal tm tape
        (values Work.horizon) index =
          stepCellPositionSizeEmitted tm tape (values Work.horizon) index := by
      cases tape <;> rfl
    have hfour := stepCellPositionEffectSize_eq_fourSize tm tape
      (values Work.horizon) index hindex
    have hstart : stepCellStart tm (values Work.horizon) tape index =
        start + 4 * index := by simp [stepCellStart, start]; ring
    have hdelta : stepCellPositionEffectSizeInternal tm tape
        (values Work.horizon) index = fourSize sizeAt (start + 4 * index) := by
      rw [heffectSize, hfour, hstart]
    funext i
    by_cases hpositionIdx : i = Work.position
    · subst i
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
    · by_cases hgateIdx : i = Work.gateCount
      · subst i
        simp [trajectory, Work.position, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃]
        rw [hdelta, show start + 4 * (index + 1) =
          (start + 4 * index) + 4 by omega, prefixSize_add_four]
        omega
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.position, Work.gateCount, Work.available,
            Work.reference₀, Work.temporary₃]
          ring
        · by_cases hreferenceIdx : i = Work.reference₀
          · subst i
            simp [trajectory, Work.position, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · by_cases htemporaryIdx : i = Work.temporary₃
            · subst i
              simp [trajectory, Work.position, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃]
            · simp [trajectory, hpositionIdx, hgateIdx, havailableIdx,
                hreferenceIdx, htemporaryIdx]
  have hemitted : ∀ index < values Work.horizon + 2,
      body.emitted (trajectory index) =
        (indexedGateBlocks 4 fun symbolIndex =>
          [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
            (stepCellStart tm (values Work.horizon) tape index +
              symbolIndex)]).flatMap
          CircuitCode.RawGate.encode := by
    intro index hindex
    have hgateAt : trajectory index Work.gateCount = stepAvailable +
        prefixSize sizeAt
          (stepCellStart tm (values Work.horizon) tape index) := by
      change stepAvailable + prefixSize sizeAt (start + 4 * index) = _
      congr 2
      simp [stepCellStart, start]
      ring
    have hrefAt : trajectory index Work.reference₀ = 0 := by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
    have htempAt : trajectory index Work.temporary₃ = 0 := by
      simp [trajectory, Work.position, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃]
    cases tape with
    | input =>
        simpa [body, stepPackedCopySpecializedInternal, stepPackedCopyGate,
          stepFormulaOutputRef, sizeAt, Work.horizon, Work.position]
            using! emitStepImmutableCellCopies_emitted_internal (trajectory index)
            sizeAt (stepCellStart tm (values Work.horizon) .input index)
            stepAvailable hgateAt hrefAt htempAt (fun symbolIndex =>
              stepFormulaSizeAtSpecialized_internal_cellCopyIndex tm
                (values Work.horizon) .input ⟨index, hindex⟩ symbolIndex
                (Or.inl rfl))
    | work tapeIndex =>
        simpa [body, Work.horizon, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃]
            using! emitStepWritableCellCopies_emitted_internal tm (.work tapeIndex)
            (trajectory index) (by simpa [trajectory, Work.position,
              Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃, Work.horizon]) stepAvailable hgateAt hrefAt
            htempAt
    | output =>
        simpa [body, Work.horizon, Work.position, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃]
            using! emitStepWritableCellCopies_emitted_internal tm .output
            (trajectory index) (by simpa [trajectory, Work.position,
              Work.gateCount, Work.available, Work.reference₀,
              Work.temporary₃, Work.horizon]) stepAvailable hgateAt hrefAt
            htempAt
  have hemittedGlobal : ∀ index < values Work.horizon + 2,
      body.emitted (trajectory index) =
        (indexedGateBlocks 4 fun symbolIndex =>
          [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
            (start + 4 * index + symbolIndex)]).flatMap
          CircuitCode.RawGate.encode := by
    intro index hindex
    have hstart : stepCellStart tm (values Work.horizon) tape index =
        start + 4 * index := by simp [stepCellStart, start]; ring
    simpa only [hstart] using hemitted index hindex
  cases tape <;>
    unfold emitStepCellTapeCopies <;>
    change BinaryRoutine.binaryForEmitted body Work.position values
        (values Work.limit₁ - values Work.position) ++ [] = _ <;>
    rw [List.append_nil, hlimit, hposition, Nat.sub_zero,
      binaryForEmitted_eq_indexedGateBlocks_bounded body Work.position values
        trajectory (fun position => indexedGateBlocks 4 fun symbolIndex =>
          [stepPackedCopySpecializedInternal tm (values Work.horizon) stepAvailable
            (start + 4 * position + symbolIndex)])
        (values Work.horizon + 2)
        (by
          funext i
          by_cases hpositionIdx : i = Work.position
          · subst i
            simpa [trajectory, Work.position, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using hposition.symm
          · by_cases hgateIdx : i = Work.gateCount
            · subst i
              simpa [trajectory, sizeAt, start, Work.position, Work.gateCount,
                Work.available, Work.reference₀, Work.temporary₃] using
                hgateCount.symm
            · by_cases hreferenceIdx : i = Work.reference₀
              · subst i
                simpa [trajectory, Work.position, Work.gateCount,
                  Work.available, Work.reference₀, Work.temporary₃] using
                  hreference.symm
              · by_cases htemporaryIdx : i = Work.temporary₃
                · subst i
                  simpa [trajectory, Work.position, Work.gateCount,
                    Work.available, Work.reference₀, Work.temporary₃] using
                    htemporary.symm
                · by_cases havailableIdx : i = Work.available
                  · subst i
                    simp [trajectory, Work.position, Work.gateCount,
                      Work.available, Work.reference₀, Work.temporary₃]
                  · simp [trajectory, hpositionIdx, hgateIdx, havailableIdx,
                      hreferenceIdx, htemporaryIdx]) hstep hemittedGlobal] <;>
    rw [indexedGateBlocks_group_four] <;>
    simp [start, Nat.add_assoc]

private theorem prefixSize_eq_sum_ofFn (sizeAt : ℕ → ℕ) (count : ℕ) :
    prefixSize sizeAt count = (List.ofFn fun index : Fin count =>
      sizeAt index.val).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixSize_succ, List.ofFn_succ_last, List.sum_append, ih]
      simp

theorem tapeSlotEquiv_symm_index_internal (index : Fin (k + 2)) :
    ((tapeSlotEquiv k).symm index).index.val = index.val := by
  have h := congrArg Fin.val ((tapeSlotEquiv k).apply_symm_apply index)
  exact h

private theorem prefixSize_constBlock (sizeAt : ℕ → ℕ)
    (start blockSize count : ℕ)
    (hsize : ∀ index < count, sizeAt (start + index) = blockSize) :
    prefixSize sizeAt (start + count) =
      prefixSize sizeAt start + count * blockSize := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        prefixSize_succ, hsize count (by omega),
        ih (fun index hindex => hsize index (by omega))]
      ring

private theorem prefixSize_fourBlocks (sizeAt blockSize : ℕ → ℕ)
    (start count : ℕ)
    (hsize : ∀ index < count,
      blockSize index = fourSize sizeAt (start + 4 * index)) :
    prefixSize sizeAt (start + 4 * count) =
      prefixSize sizeAt start + prefixSize blockSize count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + 4 * (count + 1) = (start + 4 * count) + 4 by omega,
        prefixSize_add_four, prefixSize_succ, ← hsize count (by omega),
        ih (fun index hindex => hsize index (by omega))]
      omega

private theorem prefixSize_indexedBlocks (sizeAt blockSize : ℕ → ℕ)
    (start width count : ℕ)
    (hblock : ∀ index < count,
      prefixSize sizeAt (start + index * width + width) =
        prefixSize sizeAt (start + index * width) + blockSize index) :
    prefixSize sizeAt (start + count * width) =
      prefixSize sizeAt start +
        (List.ofFn fun index : Fin count => blockSize index.val).sum := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + (count + 1) * width =
          start + count * width + width by ring,
        hblock count (by omega),
        ih (fun index hindex => hblock index (by omega)),
        List.ofFn_succ_last, List.sum_append]
      simp
      omega

theorem headPrefixBlock_internal (tm : NTM k) (T : ℕ)
    (tape : TapeSlot k) :
    prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
        (Fintype.card tm.Q + tape.index.val * (T + 1) + (T + 1)) =
      prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
          (Fintype.card tm.Q + tape.index.val * (T + 1)) +
        (T + 1) * nextHeadFormulaScheduleSize
          (transitionCases tm).length k T (movedHeadCaseSelectedAt tm tape)
          (effectCaseChoiceAt tm) := by
  let start := Fintype.card tm.Q + tape.index.val * (T + 1)
  let blockSize := nextHeadFormulaScheduleSize
    (transitionCases tm).length k T (movedHeadCaseSelectedAt tm tape)
    (effectCaseChoiceAt tm)
  have hsize : ∀ index < T + 1,
      stepFormulaSizeAtSpecializedInternal tm T (start + index) = blockSize := by
    intro index hindex
    have hindexEq : start + index = configIndex tm T
        (.head tape ⟨index, hindex⟩) := by simp [start, configIndex]
    rw [hindexEq]
    exact stepFormulaSizeAtSpecialized_internal_head tm T tape ⟨index, hindex⟩
  exact prefixSize_constBlock _ start blockSize (T + 1) hsize

theorem cellPrefixBlock_internal (tm : NTM k) (T : ℕ)
    (tape : TapeSlot k) :
    prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
        (Fintype.card tm.Q + (k + 2) * (T + 1) +
          tape.index.val * (T + 2) * 4 + 4 * (T + 2)) =
      prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
          (Fintype.card tm.Q + (k + 2) * (T + 1) +
            tape.index.val * (T + 2) * 4) +
        prefixSize (stepCellPositionEffectSizeInternal tm tape T) (T + 2) := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let start := Fintype.card tm.Q + (k + 2) * (T + 1) +
    tape.index.val * (T + 2) * 4
  apply prefixSize_fourBlocks sizeAt
    (stepCellPositionEffectSizeInternal tm tape T) start (T + 2)
  intro position hposition
  have heffectSize : stepCellPositionEffectSizeInternal tm tape T position =
      stepCellPositionSizeEmitted tm tape T position := by cases tape <;> rfl
  rw [heffectSize, stepCellPositionEffectSize_eq_fourSize tm tape T position
    hposition]
  congr 1
  simp [stepCellStart, start]
  ring

set_option maxHeartbeats 2000000 in
/-- The explicit state-phase count is its canonical numeric prefix. -/
theorem stepStateFormulasEffectSize_eq_prefixSize_internal
    (tm : NTM k) (T : ℕ) :
    stepStateFormulasEffectSizeInternal tm T =
      prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
        (Fintype.card tm.Q) := by
  rw [prefixSize_eq_sum_ofFn]
  unfold stepStateFormulasEffectSizeInternal
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp only [List.getElem_ofFn]
    have hsize := stepFormulaSizeAtSpecialized_internal_state tm T
      ⟨i, by simpa using hright⟩
    simpa using hsize.symm

set_option maxHeartbeats 2000000 in
/-- The explicit effect count is the canonical numeric formula prefix. -/
theorem stepFormulasEffectSize_eq_prefixSize_internal (tm : NTM k) (T : ℕ) :
    stepFormulasEffectSizeInternal tm T =
      prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
        (stepAtomCount (Fintype.card tm.Q) k T) := by
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let stateCount := Fintype.card tm.Q
  let tapeCount := k + 2
  let tapeAt : ℕ → TapeSlot k := fun index =>
    if hindex : index < tapeCount then
      (tapeSlotEquiv k).symm ⟨index, hindex⟩ else .input
  have hstate : prefixSize sizeAt stateCount =
      stepStateFormulasEffectSizeInternal tm T := by
    rw [prefixSize_eq_sum_ofFn]
    unfold stepStateFormulasEffectSizeInternal
    apply congrArg List.sum
    apply List.ext_getElem
    · simp [stateCount]
    · intro i hleft hright
      simp only [List.getElem_ofFn]
      have hsize := stepFormulaSizeAtSpecialized_internal_state tm T
        ⟨i, by simpa using hleft⟩
      simpa [sizeAt] using hsize
  have hheads : prefixSize sizeAt
        (stateCount + tapeCount * (T + 1)) =
      prefixSize sizeAt stateCount + stepHeadFormulasEffectSizeInternal tm T := by
    have h := prefixSize_indexedBlocks sizeAt
      (fun index => (T + 1) * nextHeadFormulaScheduleSize
        (transitionCases tm).length k T
        (movedHeadCaseSelectedAt tm (tapeAt index)) (effectCaseChoiceAt tm))
      stateCount (T + 1) tapeCount
    rw [h]
    · unfold stepHeadFormulasEffectSizeInternal
      congr 2
      rw [List.map_ofFn]
      congr 1
      funext index
      simp [tapeAt, tapeCount]
    · intro index hindex
      dsimp [tapeAt]
      rw [dite_eq_left hindex]
      have hprefix := headPrefixBlock_internal tm T
        ((tapeSlotEquiv k).symm ⟨index, hindex⟩)
      have hidx := tapeSlotEquiv_symm_index_internal (⟨index, hindex⟩ :
        Fin (k + 2))
      dsimp [sizeAt, stateCount] at hprefix ⊢
      rw [hidx] at hprefix
      exact hprefix
  have hcells : prefixSize sizeAt
        (stateCount + tapeCount * (T + 1) + tapeCount * (4 * (T + 2))) =
      prefixSize sizeAt (stateCount + tapeCount * (T + 1)) +
        stepCellFormulasEffectSizeInternal tm T := by
    have h := prefixSize_indexedBlocks sizeAt
      (fun index => prefixSize (stepCellPositionEffectSizeInternal tm
        (tapeAt index) T) (T + 2))
      (stateCount + tapeCount * (T + 1)) (4 * (T + 2)) tapeCount
    rw [h]
    · unfold stepCellFormulasEffectSizeInternal
      congr 2
      rw [List.map_ofFn]
      congr 1
      funext index
      simp [tapeAt, tapeCount]
    · intro index hindex
      dsimp [tapeAt]
      rw [dite_eq_left hindex]
      have hprefix := cellPrefixBlock_internal tm T
        ((tapeSlotEquiv k).symm ⟨index, hindex⟩)
      have hidx := tapeSlotEquiv_symm_index_internal (⟨index, hindex⟩ :
        Fin (k + 2))
      dsimp [sizeAt, stateCount, tapeCount] at hprefix ⊢
      rw [hidx] at hprefix
      convert hprefix using 1
      · ring_nf
      · ring_nf
  unfold stepFormulasEffectSizeInternal
  rw [← hstate, ← hheads, ← hcells]
  dsimp [sizeAt, stateCount, tapeCount]
  congr 1
  unfold stepAtomCount
  ring

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
