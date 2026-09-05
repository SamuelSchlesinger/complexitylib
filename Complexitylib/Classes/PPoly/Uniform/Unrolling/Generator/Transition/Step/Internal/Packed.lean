/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Emitted

/-!
# Exact packed-copy output of the direct step generator

This module composes the per-region delayed-copy contracts into the canonical
numeric packed-copy suffix. Formula emission and the outer deterministic step
are intentionally handled by separate modules.
-/


public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem seqList_ofFn_effect_eq_trajectory_packed
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

private theorem seqList_ofFn_emitted_eq_indexedGateBlocks_packed
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

private theorem indexedGateBlocks_succ_last_packed
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

private theorem indexedGateBlocks_add_packed
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
        indexedGateBlocks_succ_last_packed, ih,
        indexedGateBlocks_succ_last_packed]
      simp [List.append_assoc]

private theorem indexedGateBlocks_singleton_packed
    (count : ℕ) (gateAt : ℕ → CircuitCode.RawGate) :
    indexedGateBlocks count (fun index => [gateAt index]) =
      (List.range count).map gateAt := by
  induction count with
  | zero => simp [indexedGateBlocks]
  | succ count ih =>
      rw [indexedGateBlocks_succ_last_packed, List.range_succ,
        List.map_append, ih]
      rfl

private theorem seqList_append_emitted_packed
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).emitted values =
      (BinaryRoutine.seqList first).emitted values ++
        (BinaryRoutine.seqList second).emitted
          ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil => rfl
  | cons routine routines ih =>
      rw [List.cons_append, BinaryRoutine.seqList, BinaryRoutine.seq]
      change routine.emitted values ++
          (BinaryRoutine.seqList (routines ++ second)).emitted
            (routine.effect values) = _
      rw [ih]
      simp only [BinaryRoutine.seqList, BinaryRoutine.seq, List.append_assoc]

private theorem stepConfigAtomAt_configIndex_packed (tm : NTM k) (T : ℕ)
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

private theorem stateAtom_index_packed (tm : NTM k)
    (index : Fin (Fintype.card tm.Q)) :
    configIndex tm T (.state ((Fintype.equivFin tm.Q).symm index)) =
      index.val := by
  unfold configIndex stateIndex
  exact congrArg Fin.val ((Fintype.equivFin tm.Q).apply_symm_apply index)

private theorem stepFormulaSizeAtSpecialized_state_packed (tm : NTM k)
    (T : ℕ) (index : Fin (Fintype.card tm.Q)) :
    stepFormulaSizeAtSpecializedInternal tm T index.val =
      nextStateFormulaScheduleSize (transitionCases tm).length k T
        (effectCaseSelectedAt tm fun effect =>
          decide (effect.nextState =
            (Fintype.equivFin tm.Q).symm index))
        (effectCaseChoiceAt tm) := by
  unfold stepFormulaSizeAtSpecializedInternal stepFormulaSizeAt
  rw [ite_eq_left]
  · unfold stepAtomKindAt stepAtomEffectSelectedAt
    rw [← stateAtom_index_packed tm index,
      stepConfigAtomAt_configIndex_packed tm T]
    rfl
  · unfold stepAtomCount
    omega

private theorem prefixSize_eq_sum_ofFn_packed (sizeAt : ℕ → ℕ)
    (count : ℕ) :
    prefixSize sizeAt count =
      (List.ofFn fun index : Fin count => sizeAt index.val).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prefixSize_succ, List.ofFn_succ_last, List.sum_append, ih]
      simp

private theorem statePrefix_eq_effectSize_packed (tm : NTM k) (T : ℕ) :
    prefixSize (stepFormulaSizeAtSpecializedInternal tm T)
        (Fintype.card tm.Q) = stepStateFormulasEffectSizeInternal tm T := by
  rw [prefixSize_eq_sum_ofFn_packed]
  unfold stepStateFormulasEffectSizeInternal
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    simp only [List.getElem_ofFn]
    exact stepFormulaSizeAtSpecialized_state_packed tm T
      ⟨i, by simpa using hleft⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 3000 in
private theorem headTapeCopiesSequence_effect_packed (tm : NTM k)
    (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon)) (Fintype.card tm.Q))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeCopies tm))).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.gateCount
              (stepAvailable + prefixSize
                (stepFormulaSizeAtSpecializedInternal tm
                  (values Work.horizon))
                (Fintype.card tm.Q + (k + 2) *
                  (values Work.horizon + 1))))
            Work.available
              (values Work.available + (k + 2) *
                (values Work.horizon + 1)))
          Work.reference₀ 0) Work.temporary₃ 0 := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update
      (Function.update
        (Function.update
          (Function.update values Work.gateCount
            (stepAvailable + prefixSize sizeAt
              (Fintype.card tm.Q + index * (T + 1))))
          Work.available (values Work.available + index * (T + 1)))
        Work.reference₀ 0) Work.temporary₃ 0
  have hhorizonAt (index : ℕ) :
      trajectory index Work.horizon = values Work.horizon := by
    simp [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  rw [List.map_ofFn]
  apply seqList_ofFn_effect_eq_trajectory_packed (k + 2)
    (fun index => emitStepHeadTapeCopies tm (tapeAt index)) values trajectory
  · funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simpa [trajectory, T, sizeAt, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃] using hgateCount.symm
    · by_cases hreferenceIdx : i = Work.reference₀
      · subst i
        simpa [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃] using hreference.symm
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simpa [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using htemporary.symm
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]
  · intro index
    rw [emitStepHeadTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val) (by simpa [trajectory, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.position]
        using hposition) (by rw [hhorizonAt]; simpa [trajectory,
          Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
          Work.limit₁, Work.horizon] using hlimit)]
    rw [hhorizonAt]
    have hprefix := headPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simp [trajectory, T, sizeAt, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃, Work.horizon]
      rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
      dsimp [T, sizeAt] at hprefix ⊢
      ring_nf at hprefix ⊢
      omega
    · by_cases havailableIdx : i = Work.available
      · subst i
        simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃, Work.horizon]
        rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
        dsimp [T]
        ring_nf
      · by_cases hreferenceIdx : i = Work.reference₀
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simp [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 3000 in
private theorem headTapeCopiesSequence_emitted_packed (tm : NTM k)
    (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon)) (Fintype.card tm.Q))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeCopies tm))).emitted values =
      (indexedGateBlocks ((k + 2) * (values Work.horizon + 1)) fun offset =>
        [stepPackedCopySpecializedInternal tm (values Work.horizon)
          stepAvailable (Fintype.card tm.Q + offset)]).flatMap
        CircuitCode.RawGate.encode := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update
      (Function.update
        (Function.update
          (Function.update values Work.gateCount
            (stepAvailable + prefixSize sizeAt
              (Fintype.card tm.Q + index * (T + 1))))
          Work.available (values Work.available + index * (T + 1)))
        Work.reference₀ 0) Work.temporary₃ 0
  have hhorizonAt (index : ℕ) :
      trajectory index Work.horizon = values Work.horizon := by
    simp [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  rw [List.map_ofFn]
  change (BinaryRoutine.seqList (List.ofFn fun index =>
    emitStepHeadTapeCopies tm (tapeAt index))).emitted values = _
  rw [seqList_ofFn_emitted_eq_indexedGateBlocks_packed (k + 2)
    (fun index => emitStepHeadTapeCopies tm (tapeAt index)) values trajectory
    (fun tapeIndex => indexedGateBlocks (T + 1) fun position =>
      [stepPackedCopySpecializedInternal tm T stepAvailable
        (Fintype.card tm.Q + (T + 1) * tapeIndex + position)])]
  · congr 1
    simpa [T, Nat.add_assoc, Nat.mul_comm] using
      (indexedGateBlocks_group_internal (T + 1) (k + 2)
        (fun offset =>
          [stepPackedCopySpecializedInternal tm T stepAvailable
            (Fintype.card tm.Q + offset)])).symm
  · funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simpa [trajectory, T, sizeAt, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃] using hgateCount.symm
    · by_cases hreferenceIdx : i = Work.reference₀
      · subst i
        simpa [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃] using hreference.symm
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simpa [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using htemporary.symm
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]
  · intro index
    rw [emitStepHeadTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val) (by simpa [trajectory, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.position]
        using hposition) (by rw [hhorizonAt]; simpa [trajectory,
          Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
          Work.limit₁, Work.horizon] using hlimit)]
    rw [hhorizonAt]
    have hprefix := headPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simp [trajectory, T, sizeAt, Work.gateCount, Work.available,
        Work.reference₀, Work.temporary₃, Work.horizon]
      rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
      dsimp [T, sizeAt] at hprefix ⊢
      ring_nf at hprefix ⊢
      omega
    · by_cases havailableIdx : i = Work.available
      · subst i
        simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃, Work.horizon]
        rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
        dsimp [T]
        ring_nf
      · by_cases hreferenceIdx : i = Work.reference₀
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simp [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]
  · intro index
    have hidx := tapeSlotEquiv_symm_index_internal index
    have hemitted := emitStepHeadTapeCopies_emitted_internal tm (tapeAt index)
        (trajectory index.val) (by simpa [trajectory, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.position]
          using hposition) (by rw [hhorizonAt]; simpa [trajectory,
            Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
            Work.limit₁, Work.horizon] using hlimit) stepAvailable (by
              rw [hhorizonAt]
              simp [trajectory, sizeAt, T, Work.gateCount,
                Work.available, Work.reference₀, Work.temporary₃]
              rw [hidx]) (by
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃]) (by
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃])
    simpa [hhorizonAt, T, tapeAt, hidx, Nat.mul_comm] using hemitted

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 3000 in
private theorem cellTapeCopiesSequence_emitted_packed (tm : NTM k)
    (values : BinaryValues WorkCount)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1)))
    (hreference : values Work.reference₀ = 0)
    (htemporary : values Work.temporary₃ = 0) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepCellTapeCopies tm))).emitted values =
      (indexedGateBlocks ((k + 2) * (4 * (values Work.horizon + 2)))
        fun offset =>
          [stepPackedCopySpecializedInternal tm (values Work.horizon)
            stepAvailable
            (Fintype.card tm.Q + (k + 2) *
              (values Work.horizon + 1) + offset)]).flatMap
        CircuitCode.RawGate.encode := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let base := Fintype.card tm.Q + (k + 2) * (T + 1)
  let width := 4 * (T + 2)
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update
      (Function.update
        (Function.update
          (Function.update values Work.gateCount
            (stepAvailable + prefixSize sizeAt (base + index * width)))
          Work.available (values Work.available + index * width))
        Work.reference₀ 0) Work.temporary₃ 0
  have hhorizonAt (index : ℕ) :
      trajectory index Work.horizon = values Work.horizon := by
    simp [trajectory, Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  rw [List.map_ofFn]
  change (BinaryRoutine.seqList (List.ofFn fun index =>
    emitStepCellTapeCopies tm (tapeAt index))).emitted values = _
  rw [seqList_ofFn_emitted_eq_indexedGateBlocks_packed (k + 2)
    (fun index => emitStepCellTapeCopies tm (tapeAt index)) values trajectory
    (fun tapeIndex => indexedGateBlocks width fun offset =>
      [stepPackedCopySpecializedInternal tm T stepAvailable
        (base + width * tapeIndex + offset)])]
  · congr 1
    simpa [base, width, T, Nat.add_assoc, Nat.mul_comm] using
      (indexedGateBlocks_group_internal width (k + 2)
        (fun offset =>
          [stepPackedCopySpecializedInternal tm T stepAvailable
            (base + offset)])).symm
  · funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simpa [trajectory, base, width, T, sizeAt, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃] using
        hgateCount.symm
    · by_cases hreferenceIdx : i = Work.reference₀
      · subst i
        simpa [trajectory, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃] using hreference.symm
      · by_cases havailableIdx : i = Work.available
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simpa [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃] using htemporary.symm
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]
  · intro index
    rw [emitStepCellTapeCopies_effect_internal tm (tapeAt index)
      (trajectory index.val) (by simpa [trajectory, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.position]
        using hposition) (by rw [hhorizonAt]; simpa [trajectory,
          Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
          Work.limit₁, Work.horizon] using hlimit)]
    rw [hhorizonAt]
    have hprefix := cellPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases hgateIdx : i = Work.gateCount
    · subst i
      simp [trajectory, base, width, T, sizeAt, Work.gateCount,
        Work.available, Work.reference₀, Work.temporary₃, Work.horizon]
      rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
      have hcellPrefix :
          prefixSize (stepCellPositionEffectSizeInternal tm (tapeAt index) T)
              (T + 2) =
            prefixSize (stepCellPositionEffectSizeInternal tm (tapeAt index) T) T +
              stepCellPositionEffectSizeInternal tm (tapeAt index) T T +
              stepCellPositionEffectSizeInternal tm (tapeAt index) T (T + 1) := by
        rw [show T + 2 = (T + 1) + 1 by omega, prefixSize_succ,
          prefixSize_succ]
      rw [hcellPrefix] at hprefix
      dsimp [T, sizeAt] at hprefix ⊢
      ring_nf at hprefix ⊢
      omega
    · by_cases havailableIdx : i = Work.available
      · subst i
        simp [trajectory, width, Work.gateCount, Work.available,
          Work.reference₀, Work.temporary₃, Work.horizon]
        rw [show values (1 : Fin WorkCount) = values Work.horizon by rfl]
        dsimp [T, width]
        ring_nf
      · by_cases hreferenceIdx : i = Work.reference₀
        · subst i
          simp [trajectory, Work.gateCount, Work.available, Work.reference₀,
            Work.temporary₃]
        · by_cases htemporaryIdx : i = Work.temporary₃
          · subst i
            simp [trajectory, Work.gateCount, Work.available,
              Work.reference₀, Work.temporary₃]
          · simp [trajectory, hgateIdx, havailableIdx, hreferenceIdx,
              htemporaryIdx]
  · intro index
    have hidx := tapeSlotEquiv_symm_index_internal index
    have hemitted := emitStepCellTapeCopies_emitted_internal tm (tapeAt index)
        (trajectory index.val) (by simpa [trajectory, Work.gateCount,
          Work.available, Work.reference₀, Work.temporary₃, Work.position]
          using hposition) (by rw [hhorizonAt]; simpa [trajectory,
            Work.gateCount, Work.available, Work.reference₀, Work.temporary₃,
            Work.limit₁, Work.horizon] using hlimit) stepAvailable (by
              rw [hhorizonAt]
              simp [trajectory, base, width, sizeAt, T, Work.gateCount,
                Work.available, Work.reference₀, Work.temporary₃]
              rw [hidx]
              ring_nf) (by
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃]) (by
              simp [trajectory, Work.gateCount, Work.available,
                Work.reference₀, Work.temporary₃])
    simpa [hhorizonAt, T, tapeAt, base, width, hidx, Nat.mul_assoc,
      Nat.mul_comm] using hemitted

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
/-- The complete delayed-copy phase emits exactly the canonical packed-copy
suffix in global configuration-atom order. -/
theorem emitStepPackedCopies_emitted_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (stepAvailable : ℕ)
    (hgateCount : values Work.gateCount = stepAvailable) :
    (emitStepPackedCopies tm).emitted values =
      (stepPackedCopies (transitionCases tm).length (Fintype.card tm.Q) k
        (values Work.horizon) stepAvailable
        (stepAtomKindAt tm (values Work.horizon))
        (stepAtomEffectSelectedAt tm (values Work.horizon))
        (effectCaseChoiceAt tm)).flatMap CircuitCode.RawGate.encode := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  let stateCount := Fintype.card tm.Q
  let headCount := (k + 2) * (T + 1)
  let cellCount := (k + 2) * (4 * (T + 2))
  have hreference : values Work.reference₀ = 0 := by
    simpa [Work.position, Work.reference₀] using
      hclean.movedHeadClean.caseClean.reference₀
  have htemporary : values Work.temporary₃ = 0 := by
    simpa [Work.position, Work.temporary₃] using
      hclean.movedHeadClean.caseClean.temporary₃
  let afterState := Function.update
    (Function.update
      (Function.update
        (Function.update values Work.gateCount
          (values Work.gateCount + stepStateFormulasEffectSizeInternal tm T))
        Work.available (values Work.available + stateCount))
      Work.reference₀ 0) Work.temporary₃ 0
  have hstateEffect : (emitStepStateCopies tm).effect values = afterState := by
    simpa [afterState, T, stateCount] using
      emitStepStateCopies_effect_internal tm values
  have hstatePrefix :
      prefixSize sizeAt stateCount = stepStateFormulasEffectSizeInternal tm T := by
    exact statePrefix_eq_effectSize_packed tm T
  have hstateGate : afterState Work.gateCount =
      stepAvailable + prefixSize sizeAt stateCount := by
    calc
      afterState Work.gateCount =
          values Work.gateCount + stepStateFormulasEffectSizeInternal tm T := by
        simp [afterState, Work.gateCount, Work.available, Work.reference₀,
          Work.temporary₃]
      _ = stepAvailable + prefixSize sizeAt stateCount := by
        rw [hgateCount, hstatePrefix]
  let afterLimit₁ := Function.update afterState Work.limit₁
    (afterState Work.horizon + 1)
  have hlimit₁Effect : (setStepPositionLimit 1).effect afterState =
      afterLimit₁ := by
    simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, afterLimit₁]
  have hheadPosition : afterLimit₁ Work.position = 0 := by
    simpa [afterLimit₁, afterState, Work.limit₁, Work.position,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
      using hclean.position
  have hheadLimit : afterLimit₁ Work.limit₁ =
      afterLimit₁ Work.horizon + 1 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.horizon,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
  have hheadHorizon : afterLimit₁ Work.horizon = values Work.horizon := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.horizon,
      Work.gateCount, Work.available, Work.reference₀, Work.temporary₃]
  have hheadGate : afterLimit₁ Work.gateCount =
      stepAvailable + prefixSize
        (stepFormulaSizeAtSpecializedInternal tm
          (afterLimit₁ Work.horizon)) (Fintype.card tm.Q) := by
    simpa [afterLimit₁, afterState, sizeAt, T, stateCount, Work.limit₁,
      Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃] using hstateGate
  have hheadReference : afterLimit₁ Work.reference₀ = 0 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  have hheadTemporary : afterLimit₁ Work.temporary₃ = 0 := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  let afterHeads := Function.update
    (Function.update
      (Function.update
        (Function.update afterLimit₁ Work.gateCount
          (stepAvailable + prefixSize
            (stepFormulaSizeAtSpecializedInternal tm
              (afterLimit₁ Work.horizon))
            (Fintype.card tm.Q + (k + 2) *
              (afterLimit₁ Work.horizon + 1))))
        Work.available
          (afterLimit₁ Work.available + (k + 2) *
            (afterLimit₁ Work.horizon + 1)))
      Work.reference₀ 0) Work.temporary₃ 0
  have hheadsEffect :
      (BinaryRoutine.seqList (tapes.map
        (emitStepHeadTapeCopies tm))).effect afterLimit₁ = afterHeads := by
    simpa [tapes, afterHeads] using
      headTapeCopiesSequence_effect_packed tm afterLimit₁ hheadPosition
        hheadLimit stepAvailable hheadGate hheadReference hheadTemporary
  have hfirstGroupEffect :
      (BinaryRoutine.seqList
        ([emitStepStateCopies tm, setStepPositionLimit 1] ++
          tapes.map (emitStepHeadTapeCopies tm))).effect values =
        afterHeads := by
    change (BinaryRoutine.seqList
      (tapes.map (emitStepHeadTapeCopies tm))).effect
        ((setStepPositionLimit 1).effect
          ((emitStepStateCopies tm).effect values)) = afterHeads
    rw [hstateEffect, hlimit₁Effect, hheadsEffect]
  let afterLimit₂ := Function.update afterHeads Work.limit₁
    (afterHeads Work.horizon + 2)
  have hlimit₂Effect : (setStepPositionLimit 2).effect afterHeads =
      afterLimit₂ := by
    simp [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
      BinaryRoutine.addConst, afterLimit₂]
  have hcellPosition : afterLimit₂ Work.position = 0 := by
    simpa [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.position, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃] using hclean.position
  have hcellLimit : afterLimit₂ Work.limit₁ =
      afterLimit₂ Work.horizon + 2 := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.horizon, Work.gateCount, Work.available,
      Work.reference₀, Work.temporary₃]
  have hcellHorizon : afterLimit₂ Work.horizon = values Work.horizon := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hcellGate : afterLimit₂ Work.gateCount =
      stepAvailable + prefixSize
        (stepFormulaSizeAtSpecializedInternal tm
          (afterLimit₂ Work.horizon))
        (Fintype.card tm.Q + (k + 2) *
          (afterLimit₂ Work.horizon + 1)) := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.horizon, Work.gateCount, Work.available, Work.reference₀,
      Work.temporary₃]
  have hcellReference : afterLimit₂ Work.reference₀ = 0 := by
    simp [afterLimit₂, afterHeads, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  have hcellTemporary : afterLimit₂ Work.temporary₃ = 0 := by
    simp [afterLimit₂, afterHeads, Work.limit₁, Work.reference₀,
      Work.temporary₃]
  have hstateEmitted := emitStepStateCopies_emitted_internal tm values
    stepAvailable hgateCount hreference htemporary
  have hheadsEmitted := headTapeCopiesSequence_emitted_packed tm afterLimit₁
    hheadPosition hheadLimit stepAvailable hheadGate hheadReference
    hheadTemporary
  have hcellsEmitted := cellTapeCopiesSequence_emitted_packed tm afterLimit₂
    hcellPosition hcellLimit stepAvailable hcellGate hcellReference
    hcellTemporary
  simp only [hheadHorizon] at hheadsEmitted
  simp only [hcellHorizon] at hcellsEmitted
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
      [BinaryRoutine.clear Work.limit₁])).emitted values = _
  rw [hschedule]
  rw [seqList_append_emitted_packed,
    seqList_append_emitted_packed
      ([emitStepStateCopies tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeCopies tm)),
    seqList_append_emitted_packed
      [emitStepStateCopies tm, setStepPositionLimit 1],
    seqList_append_emitted_packed [setStepPositionLimit 2]]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq]
  rw [hstateEffect, hlimit₁Effect, hfirstGroupEffect, hlimit₂Effect]
  simp only [BinaryRoutine.identity, BinaryRoutine.emitBits, id_eq,
    setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, BinaryRoutine.clear, List.nil_append,
    List.append_nil]
  rw [hstateEmitted, hheadsEmitted, hcellsEmitted]
  rw [← List.flatMap_append, ← List.flatMap_append]
  unfold stepPackedCopies indexedBatchCopies
  rw [← indexedGateBlocks_singleton_packed]
  unfold stepPackedCopySpecializedInternal stepPackedCopyGate
    stepFormulaOutputRef indexedBatchCopy
  congr 1
  rw [← indexedGateBlocks_add_packed stateCount headCount]
  rw [← indexedGateBlocks_add_packed (stateCount + headCount) cellCount]
  · congr 1
    unfold stepAtomCount
    simp [stateCount, headCount, cellCount, T]
    ring_nf

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
