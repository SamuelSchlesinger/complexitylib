/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step.Internal.Packed

/-!
# Whole-step direct-generator contracts

This file composes the exact per-region contracts into byte-for-byte contracts
for the complete formula phase, packed-copy phase, and deterministic step.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem identity_effect_top (values : BinaryValues n) :
    (BinaryRoutine.identity : BinaryRoutine n).effect values = values := rfl

private theorem identity_emitted_top (values : BinaryValues n) :
    (BinaryRoutine.identity : BinaryRoutine n).emitted values = [] := rfl

private theorem seqList_ofFn_effect_eq_trajectory_top
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

private theorem seqList_ofFn_emitted_eq_indexedGateBlocks_top
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

private theorem seqList_append_emitted_top
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
      simp only [BinaryRoutine.seqList, BinaryRoutine.seq,
        List.append_assoc]

private theorem seqList_append_effect_top
    (first second : List (BinaryRoutine n)) (values : BinaryValues n) :
    (BinaryRoutine.seqList (first ++ second)).effect values =
      (BinaryRoutine.seqList second).effect
        ((BinaryRoutine.seqList first).effect values) := by
  induction first generalizing values with
  | nil => rfl
  | cons routine routines ih =>
      rw [List.cons_append, BinaryRoutine.seqList, BinaryRoutine.seq]
      exact ih (routine.effect values)

private theorem indexedGateBlocks_succ_last_top
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

private theorem indexedGateBlocks_add_top
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
        indexedGateBlocks_succ_last_top, ih,
        indexedGateBlocks_succ_last_top]
      simp [List.append_assoc]

private theorem indexedGateBlocks_congr_top (count : ℕ)
    (first second : ℕ → CircuitCode.RawCircuit)
    (heq : ∀ index, first index = second index) :
    indexedGateBlocks count first = indexedGateBlocks count second := by
  induction count generalizing first second with
  | zero => rfl
  | succ count ih =>
      simp only [indexedGateBlocks]
      rw [heq 0, ih (fun index => first (index + 1))
        (fun index => second (index + 1)) (fun index => heq (index + 1))]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
private theorem headTapeSequence_effect_top (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hhorizon : 0 < values Work.horizon) (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon)) (Fintype.card tm.Q)) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeFormulas tm))).effect values =
      Function.update values Work.available
        (stepAvailable + prefixSize
          (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
          (Fintype.card tm.Q + (k + 2) *
            (values Work.horizon + 1))) := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update values Work.available
      (stepAvailable + prefixSize sizeAt
        (Fintype.card tm.Q + index * (T + 1)))
  rw [List.map_ofFn]
  apply seqList_ofFn_effect_eq_trajectory_top (k + 2)
    (emitStepHeadTapeFormulas tm ∘ tapeAt) values trajectory
  · funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simpa [trajectory, T, sizeAt, Work.available] using havailable.symm
    · simp [trajectory, havailableIdx]
  · intro index
    change (emitStepHeadTapeFormulas tm (tapeAt index)).effect
      (trajectory index.val) = trajectory (index.val + 1)
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (Fintype.card tm.Q + index.val * (T + 1)))
    have hphase : StepPhaseCleanInternal (trajectory index.val) :=
      { movedHeadClean := hcleanAt
        position := by simpa [trajectory, Work.available, Work.position] using
          hposition }
    rw [emitStepHeadTapeFormulas_effect_internal tm (tapeAt index)
      (trajectory index.val) hphase (by simpa [trajectory, T, Work.available,
        Work.horizon] using hhorizon) (by simpa [trajectory, T,
          Work.available, Work.limit₁, Work.horizon] using hlimit)]
    have hprefix := headPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simp [trajectory, Work.available, Work.horizon, T, sizeAt]
      change stepAvailable + prefixSize sizeAt
          (Fintype.card tm.Q + index.val * (T + 1)) +
            (T + 1) * nextHeadFormulaScheduleSize
              (transitionCases tm).length k T
              (movedHeadCaseSelectedAt tm (tapeAt index))
              (effectCaseChoiceAt tm) =
        stepAvailable + prefixSize sizeAt
          (Fintype.card tm.Q + (index.val + 1) * (T + 1))
      rw [show Fintype.card tm.Q + (index.val + 1) * (T + 1) =
          Fintype.card tm.Q + index.val * (T + 1) + (T + 1) by ring,
        hprefix]
      simp only [sizeAt, Nat.add_assoc]
    · simp [trajectory, havailableIdx]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
private theorem headTapeSequence_emitted_top (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 1)
    (hhorizon : 0 < values Work.horizon) (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon)) (Fintype.card tm.Q)) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepHeadTapeFormulas tm))).emitted values =
      (indexedGateBlocks ((k + 2) * (values Work.horizon + 1)) fun offset =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + offset)).flatMap
        CircuitCode.RawGate.encode := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update values Work.available
      (stepAvailable + prefixSize sizeAt
        (Fintype.card tm.Q + index * (T + 1)))
  rw [List.map_ofFn]
  rw [seqList_ofFn_emitted_eq_indexedGateBlocks_top (k + 2)
    (emitStepHeadTapeFormulas tm ∘ tapeAt) values trajectory
    (fun tapeIndex => indexedGateBlocks (T + 1) fun position =>
      stepFormulaBlockSpecializedInternal tm T (values Work.configBase)
        stepAvailable
        (Fintype.card tm.Q + tapeIndex * (T + 1) + position))]
  · have hgroup := indexedGateBlocks_group_internal (T + 1) (k + 2)
      (fun offset => stepFormulaBlockSpecializedInternal tm T
        (values Work.configBase) stepAvailable (Fintype.card tm.Q + offset))
    simpa [T, Nat.mul_comm, Nat.add_assoc] using
      congrArg (List.flatMap CircuitCode.RawGate.encode) hgroup.symm
  · funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simpa [trajectory, T, sizeAt, Work.available] using havailable.symm
    · simp [trajectory, havailableIdx]
  · intro index
    change (emitStepHeadTapeFormulas tm (tapeAt index)).effect
      (trajectory index.val) = trajectory (index.val + 1)
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (Fintype.card tm.Q + index.val * (T + 1)))
    have hphase : StepPhaseCleanInternal (trajectory index.val) :=
      { movedHeadClean := hcleanAt
        position := by simpa [trajectory, Work.available, Work.position] using
          hposition }
    rw [emitStepHeadTapeFormulas_effect_internal tm (tapeAt index)
      (trajectory index.val) hphase (by simpa [trajectory, T, Work.available,
        Work.horizon] using hhorizon) (by simpa [trajectory, T,
          Work.available, Work.limit₁, Work.horizon] using hlimit)]
    have hprefix := headPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simp [trajectory, Work.available, Work.horizon, T, sizeAt]
      change stepAvailable + prefixSize sizeAt
          (Fintype.card tm.Q + index.val * (T + 1)) +
            (T + 1) * nextHeadFormulaScheduleSize
              (transitionCases tm).length k T
              (movedHeadCaseSelectedAt tm (tapeAt index))
              (effectCaseChoiceAt tm) =
        stepAvailable + prefixSize sizeAt
          (Fintype.card tm.Q + (index.val + 1) * (T + 1))
      rw [show Fintype.card tm.Q + (index.val + 1) * (T + 1) =
          Fintype.card tm.Q + index.val * (T + 1) + (T + 1) by ring,
        hprefix]
      simp only [sizeAt, Nat.add_assoc]
    · simp [trajectory, havailableIdx]
  · intro index
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (Fintype.card tm.Q + index.val * (T + 1)))
    have hidx := tapeSlotEquiv_symm_index_internal index
    simpa [trajectory, tapeAt, T, sizeAt, Work.available, Work.horizon,
      Work.configBase, hidx] using
      emitStepHeadTapeFormulas_emitted_internal tm (tapeAt index)
        (trajectory index.val) hcleanAt (by simpa [trajectory, T,
          Work.available, Work.horizon] using hhorizon) (by simpa [trajectory,
          Work.available, Work.position] using hposition) (by simpa [trajectory,
          T, Work.available, Work.limit₁, Work.horizon] using hlimit)
        stepAvailable (by
          change stepAvailable + prefixSize sizeAt
              (Fintype.card tm.Q + index.val * (T + 1)) =
            stepAvailable + prefixSize
              (stepFormulaSizeAtSpecializedInternal tm
                (trajectory index.val Work.horizon))
              (Fintype.card tm.Q + (tapeAt index).index.val *
                (trajectory index.val Work.horizon + 1))
          have hhorizonAt : trajectory index.val Work.horizon = T := by
            simp [trajectory, T, Work.available, Work.horizon]
          rw [hhorizonAt, hidx])

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
private theorem cellTapeSequence_effect_top (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1))) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepCellTapeFormulas tm))).effect values =
      Function.update values Work.available
        (stepAvailable + prefixSize
          (stepFormulaSizeAtSpecializedInternal tm (values Work.horizon))
          (stepAtomCount (Fintype.card tm.Q) k
            (values Work.horizon))) := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let base := Fintype.card tm.Q + (k + 2) * (T + 1)
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update values Work.available
      (stepAvailable + prefixSize sizeAt
        (base + index * (4 * (T + 2))))
  rw [List.map_ofFn]
  refine (seqList_ofFn_effect_eq_trajectory_top (k + 2)
    (fun index => emitStepCellTapeFormulas tm (tapeAt index)) values trajectory
    ?_ ?_).trans ?_
  · funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simpa [trajectory, base, T, sizeAt, Work.available] using havailable.symm
    · simp [trajectory, havailableIdx]
  · intro index
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (base + index.val * (4 * (T + 2))))
    have hphase : StepPhaseCleanInternal (trajectory index.val) :=
      { movedHeadClean := hcleanAt
        position := by simpa [trajectory, Work.available, Work.position] using
          hposition }
    rw [emitStepCellTapeFormulas_effect_internal tm (tapeAt index)
      (trajectory index.val) hphase (by simpa [trajectory, T,
        Work.available, Work.limit₁, Work.horizon] using hlimit)]
    have htrajectoryHorizon : trajectory index.val Work.horizon = T := by
      simp [trajectory, T, Work.available, Work.horizon]
    simp only [htrajectoryHorizon]
    have hprefix := cellPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      change stepAvailable + prefixSize sizeAt
          (base + index.val * (4 * (T + 2))) +
            prefixSize (stepCellPositionEffectSizeInternal tm (tapeAt index) T)
              (T + 2) =
        stepAvailable + prefixSize sizeAt
          (base + (index.val + 1) * (4 * (T + 2)))
      have hstart : base + index.val * (4 * (T + 2)) =
          Fintype.card tm.Q + (k + 2) * (T + 1) +
            index.val * (T + 2) * 4 := by
        simp [base]
        ring
      have hend : base + (index.val + 1) * (4 * (T + 2)) =
          Fintype.card tm.Q + (k + 2) * (T + 1) +
              index.val * (T + 2) * 4 + 4 * (T + 2) := by
        simp [base]
        ring
      rw [hstart, hend, hprefix]
      simp only [sizeAt, Nat.add_assoc]
    · simp [trajectory, havailableIdx]
  · funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simp [trajectory, base, T, sizeAt, stepAtomCount, Work.available]
      congr 2
      ring
    · simp [trajectory, havailableIdx]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
private theorem cellTapeSequence_emitted_top (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : MovedHeadFormulaClean values)
    (hposition : values Work.position = 0)
    (hlimit : values Work.limit₁ = values Work.horizon + 2)
    (stepAvailable : ℕ)
    (havailable : values Work.available = stepAvailable +
      prefixSize (stepFormulaSizeAtSpecializedInternal tm
        (values Work.horizon))
        (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1))) :
    (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
      (emitStepCellTapeFormulas tm))).emitted values =
      (indexedGateBlocks ((k + 2) * (4 * (values Work.horizon + 2))) fun offset =>
        stepFormulaBlockSpecializedInternal tm (values Work.horizon)
          (values Work.configBase) stepAvailable
          (Fintype.card tm.Q + (k + 2) * (values Work.horizon + 1) +
            offset)).flatMap CircuitCode.RawGate.encode := by
  let T := values Work.horizon
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm T
  let base := Fintype.card tm.Q + (k + 2) * (T + 1)
  let tapeAt : Fin (k + 2) → TapeSlot k := (tapeSlotEquiv k).symm
  let trajectory : ℕ → BinaryValues WorkCount := fun index =>
    Function.update values Work.available
      (stepAvailable + prefixSize sizeAt
        (base + index * (4 * (T + 2))))
  rw [List.map_ofFn]
  change (BinaryRoutine.seqList (List.ofFn fun index =>
    emitStepCellTapeFormulas tm (tapeAt index))).emitted values = _
  rw [seqList_ofFn_emitted_eq_indexedGateBlocks_top (k + 2)
    (fun index => emitStepCellTapeFormulas tm (tapeAt index)) values trajectory
    (fun tapeIndex => indexedGateBlocks (4 * (T + 2)) fun position =>
      stepFormulaBlockSpecializedInternal tm T (values Work.configBase)
        stepAvailable (base + (tapeIndex * (4 * (T + 2)) + position)))]
  · have hgroup := indexedGateBlocks_group_internal (4 * (T + 2)) (k + 2)
      (fun flat => stepFormulaBlockSpecializedInternal tm T
        (values Work.configBase) stepAvailable (base + flat))
    simpa [base, T, Nat.mul_comm, Nat.add_assoc] using
      congrArg (List.flatMap CircuitCode.RawGate.encode) hgroup.symm
  · funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      simpa [trajectory, base, T, sizeAt, Work.available] using havailable.symm
    · simp [trajectory, havailableIdx]
  · intro index
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (base + index.val * (4 * (T + 2))))
    have hphase : StepPhaseCleanInternal (trajectory index.val) :=
      { movedHeadClean := hcleanAt
        position := by simpa [trajectory, Work.available, Work.position] using
          hposition }
    rw [emitStepCellTapeFormulas_effect_internal tm (tapeAt index)
      (trajectory index.val) hphase (by simpa [trajectory, T,
        Work.available, Work.limit₁, Work.horizon] using hlimit)]
    have htrajectoryHorizon : trajectory index.val Work.horizon = T := by
      simp [trajectory, T, Work.available, Work.horizon]
    simp only [htrajectoryHorizon]
    have hprefix := cellPrefixBlock_internal tm T (tapeAt index)
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [hidx] at hprefix
    funext i
    by_cases havailableIdx : i = Work.available
    · subst i
      change stepAvailable + prefixSize sizeAt
          (base + index.val * (4 * (T + 2))) +
            prefixSize (stepCellPositionEffectSizeInternal tm (tapeAt index) T)
              (T + 2) =
        stepAvailable + prefixSize sizeAt
          (base + (index.val + 1) * (4 * (T + 2)))
      have hstart : base + index.val * (4 * (T + 2)) =
          Fintype.card tm.Q + (k + 2) * (T + 1) +
            index.val * (T + 2) * 4 := by
        simp [base]
        ring
      have hend : base + (index.val + 1) * (4 * (T + 2)) =
          Fintype.card tm.Q + (k + 2) * (T + 1) +
              index.val * (T + 2) * 4 + 4 * (T + 2) := by
        simp [base]
        ring
      rw [hstart, hend, hprefix]
      simp only [sizeAt, Nat.add_assoc]
    · simp [trajectory, havailableIdx]
  · intro index
    have hcleanAt := hclean.updateAvailable_emitted_internal
      (stepAvailable + prefixSize sizeAt
        (base + index.val * (4 * (T + 2))))
    have hidx := tapeSlotEquiv_symm_index_internal index
    rw [emitStepCellTapeFormulas_emitted_internal tm (tapeAt index)
      (trajectory index.val) hcleanAt (by simpa [trajectory,
        Work.available, Work.position] using hposition) (by simpa [trajectory,
        T, Work.available, Work.limit₁, Work.horizon] using hlimit)
      stepAvailable (by
        change stepAvailable + prefixSize sizeAt
            (base + index.val * (4 * (T + 2))) =
          stepAvailable + prefixSize sizeAt
            (Fintype.card tm.Q + (k + 2) * (T + 1) +
              (tapeAt index).index.val * (T + 2) * 4)
        rw [hidx]
        congr 2
        ring)]
    apply congrArg (List.flatMap CircuitCode.RawGate.encode)
    apply indexedGateBlocks_congr_top
    intro offset
    have hhorizonAt : trajectory index.val Work.horizon = T := by
      simp [trajectory, T, Work.available, Work.horizon]
    have hconfigBaseAt : trajectory index.val Work.configBase =
        values Work.configBase := by
      simp [trajectory, Work.available, Work.configBase]
    rw [hhorizonAt, hconfigBaseAt, hidx]
    congr 1
    simp [base]
    ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000 in
/-- Exact byte stream of the complete forward formula phase. -/
theorem emitStepFormulas_emitted_internal (tm : NTM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStepFormulas tm).emitted values =
      (indexedGateBlocks
        (stepAtomCount (Fintype.card tm.Q) k (values Work.horizon)) fun index =>
          stepFormulaBlockSpecializedInternal tm (values Work.horizon)
            (values Work.configBase) (values Work.available) index).flatMap
        CircuitCode.RawGate.encode := by
  let sizeAt := stepFormulaSizeAtSpecializedInternal tm
    (values Work.horizon)
  let stateEnd := Fintype.card tm.Q
  let headEnd := stateEnd + (k + 2) * (values Work.horizon + 1)
  let afterState := Function.update values Work.available
    (values Work.available + prefixSize sizeAt stateEnd)
  let afterLimit₁ := Function.update afterState Work.limit₁
    (values Work.horizon + 1)
  let afterHeads := Function.update afterLimit₁ Work.available
    (values Work.available + prefixSize sizeAt headEnd)
  let afterLimit₂ := Function.update afterHeads Work.limit₁
    (values Work.horizon + 2)
  have hstateEffect : (emitStepStateFormulas tm).effect values = afterState := by
    rw [emitStepStateFormulas_effect_internal tm values hclean]
    change Function.update values Work.available
      (values Work.available + stepStateFormulasEffectSizeInternal tm
        (values Work.horizon)) = afterState
    rw [stepStateFormulasEffectSize_eq_prefixSize_internal]
  have hlimit₁Effect :
      (setStepPositionLimit 1).effect afterState = afterLimit₁ := by
    rw [setStepPositionLimit_effect_local_internal]
    simp [afterState, afterLimit₁, Work.available, Work.horizon]
  have hphaseState : StepPhaseCleanInternal afterState :=
    { movedHeadClean := hclean.movedHeadClean.updateAvailable_emitted_internal _
      position := by simpa [afterState, Work.available, Work.position] using
        hclean.position }
  have hphaseLimit₁ : StepPhaseCleanInternal afterLimit₁ := by
    simpa [afterLimit₁] using
      update_limit₁_preserves_phaseClean_internal hphaseState
        (values Work.horizon + 1)
  have hstateAvailable : afterLimit₁ Work.available =
      values Work.available + prefixSize sizeAt stateEnd := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.available]
  have hlimit₁Horizon : afterLimit₁ Work.horizon = values Work.horizon := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.available, Work.horizon]
  have hlimit₁ConfigBase : afterLimit₁ Work.configBase =
      values Work.configBase := by
    simp [afterLimit₁, afterState, Work.limit₁, Work.available,
      Work.configBase]
  have hheadsEffect :
      (BinaryRoutine.seqList ((List.ofFn (tapeSlotEquiv k).symm).map
        (emitStepHeadTapeFormulas tm))).effect afterLimit₁ = afterHeads := by
    rw [headTapeSequence_effect_top tm afterLimit₁ hphaseLimit₁.movedHeadClean
      (stepAvailable := values Work.available)]
    · funext i
      by_cases hi : i = Work.available
      · subst i
        change values Work.available + prefixSize
            (stepFormulaSizeAtSpecializedInternal tm
              (afterLimit₁ Work.horizon))
            (Fintype.card tm.Q + (k + 2) *
              (afterLimit₁ Work.horizon + 1)) =
          values Work.available + prefixSize sizeAt headEnd
        rw [hlimit₁Horizon]
      · simp [afterHeads, afterLimit₁, hi]
    · simpa [afterLimit₁, afterState, Work.limit₁, Work.available,
        Work.position] using hclean.position
    · simp [afterLimit₁, afterState, Work.limit₁, Work.available,
        Work.horizon]
    · simpa [afterLimit₁, afterState, Work.limit₁, Work.available,
        Work.horizon] using hhorizon
    · rw [hlimit₁Horizon]
      simpa only [sizeAt, stateEnd] using hstateAvailable
  have hlimit₂Effect :
      (setStepPositionLimit 2).effect afterHeads = afterLimit₂ := by
    rw [setStepPositionLimit_effect_local_internal]
    simp [afterHeads, afterLimit₁, afterState, afterLimit₂, Work.available,
      Work.limit₁, Work.horizon]
  have hphaseHeads : StepPhaseCleanInternal afterHeads :=
    { movedHeadClean := hphaseLimit₁.movedHeadClean.updateAvailable_emitted_internal _
      position := by simpa [afterHeads, Work.available, Work.position] using
        hphaseLimit₁.position }
  have hphaseLimit₂ : StepPhaseCleanInternal afterLimit₂ := by
    simpa [afterLimit₂] using
      update_limit₁_preserves_phaseClean_internal hphaseHeads
        (values Work.horizon + 2)
  have hlimit₂Horizon : afterLimit₂ Work.horizon = values Work.horizon := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.available, Work.horizon]
  have hlimit₂ConfigBase : afterLimit₂ Work.configBase =
      values Work.configBase := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.available, Work.configBase]
  have hlimit₂Available : afterLimit₂ Work.available =
      values Work.available + prefixSize sizeAt headEnd := by
    simp [afterLimit₂, afterHeads, afterLimit₁, afterState, Work.limit₁,
      Work.available]
  let tapes := List.ofFn (tapeSlotEquiv k).symm
  change (BinaryRoutine.seqList (tapes.map
    (emitStepHeadTapeFormulas tm))).effect afterLimit₁ = afterHeads at hheadsEffect
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
      [BinaryRoutine.clear Work.limit₁])).emitted values = _
  rw [hschedule, seqList_append_emitted_top,
    seqList_append_emitted_top
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm)),
    seqList_append_emitted_top
      [emitStepStateFormulas tm, setStepPositionLimit 1],
    seqList_append_emitted_top [setStepPositionLimit 2]]
  rw [seqList_append_effect_top
      ([emitStepStateFormulas tm, setStepPositionLimit 1] ++
        tapes.map (emitStepHeadTapeFormulas tm))
      ([setStepPositionLimit 2] ++
        tapes.map (emitStepCellTapeFormulas tm)),
    seqList_append_effect_top
      [emitStepStateFormulas tm, setStepPositionLimit 1]
      (tapes.map (emitStepHeadTapeFormulas tm)),
    seqList_append_effect_top [setStepPositionLimit 2]
      (tapes.map (emitStepCellTapeFormulas tm))]
  simp only [BinaryRoutine.seqList, BinaryRoutine.seq]
  simp only [identity_effect_top, identity_emitted_top]
  rw [hstateEffect, hlimit₁Effect, hheadsEffect, hlimit₂Effect]
  simp only [setStepPositionLimit, BinaryRoutine.seq, BinaryRoutine.binaryCopy,
    BinaryRoutine.addConst, BinaryRoutine.clear, List.nil_append,
    List.append_nil]
  rw [emitStepStateFormulas_emitted_internal tm values hclean]
  rw [headTapeSequence_emitted_top tm afterLimit₁
    hphaseLimit₁.movedHeadClean (stepAvailable := values Work.available)]
  · rw [cellTapeSequence_emitted_top tm afterLimit₂
      hphaseLimit₂.movedHeadClean (stepAvailable := values Work.available)]
    · rw [hlimit₁Horizon, hlimit₂Horizon, hlimit₁ConfigBase,
        hlimit₂ConfigBase, ← List.flatMap_append, ← List.flatMap_append]
      rw [← indexedGateBlocks_add_top stateEnd
          ((k + 2) * (values Work.horizon + 1)),
        ← indexedGateBlocks_add_top headEnd
          ((k + 2) * (4 * (values Work.horizon + 2)))]
      simp [stateEnd, headEnd, stepAtomCount, Work.available, Work.configBase,
        Work.horizon, Nat.add_assoc]
      congr 2
      ring
    · simpa [afterLimit₂, afterHeads, afterLimit₁, afterState,
        Work.limit₁, Work.available, Work.position] using hclean.position
    · simp [afterLimit₂, afterHeads, afterLimit₁, afterState,
        Work.limit₁, Work.available, Work.horizon]
    · simpa [headEnd, stateEnd, sizeAt, hlimit₂Horizon] using
        hlimit₂Available
  · simpa [afterLimit₁, afterState, Work.limit₁, Work.available,
      Work.position] using hclean.position
  · simp [afterLimit₁, afterState, Work.limit₁, Work.available,
      Work.horizon]
  · simpa [afterLimit₁, afterState, Work.limit₁, Work.available,
      Work.horizon] using hhorizon
  · rw [hlimit₁Horizon]
    simpa only [sizeAt, stateEnd] using hstateAvailable

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 3000 in
/-- Exact byte stream of one complete deterministic packed transition layer. -/
theorem emitStep_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).emitted values =
      (stepSchedule (transitionCases tm.toNTM).length (Fintype.card tm.Q) k
        (values Work.horizon) (values Work.configBase) 0
        (values Work.available) (nextHaltStateIndex tm.toNTM)
        (stepAtomKindAt tm.toNTM (values Work.horizon))
        (stepAtomStateIndexAt tm.toNTM (values Work.horizon))
        (stepAtomTapeIndexAt tm.toNTM (values Work.horizon))
        (stepAtomPositionAt tm.toNTM (values Work.horizon))
        (stepAtomSymbolIndexAt tm.toNTM (values Work.horizon))
        (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
        (effectCaseChoiceAt tm.toNTM) (effectCaseStateIndexAt tm.toNTM)
        (effectCaseInputSymbolIndexAt tm.toNTM)
        (effectCaseOutputSymbolIndexAt tm.toNTM)
        (effectCaseWorkSymbolIndexAt tm.toNTM)).flatMap
          CircuitCode.RawGate.encode := by
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
      (emitStepFormulas tm.toNTM).effect afterBound = afterFormulas :=
    emitStepFormulas_effect_internal tm.toNTM afterBound hcleanBound
      hhorizonBound
  have hformulaEmitted := emitStepFormulas_emitted_internal tm.toNTM
    afterBound hcleanBound hhorizonBound
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
  have hgateCount : afterCount Work.gateCount = values Work.available := by
    simp [afterCount, afterBase, afterFormulas, afterBound, Work.gateCount,
      Work.configBase, Work.available, Work.gateBound]
  have hpackedEmitted := emitStepPackedCopies_emitted_internal tm.toNTM
    afterCount hcleanCount (values Work.available) hgateCount
  simp only [emitStep, BinaryRoutine.seqList, BinaryRoutine.seq]
  simp only [BinaryRoutine.binaryCopy, BinaryRoutine.clear,
    identity_emitted_top, List.nil_append, List.append_nil]
  rw [hformulaEffect]
  change (emitStepFormulas tm.toNTM).emitted afterBound ++
      (emitStepPackedCopies tm.toNTM).emitted afterCount = _
  rw [hformulaEmitted, hpackedEmitted]
  simp [stepSchedule, stepFormulaGates,
    stepFormulaBlockSpecializedInternal, afterBound, afterCount, afterBase,
    afterFormulas, Work.gateBound, Work.gateCount, Work.configBase,
    Work.available, Work.horizon, List.flatMap_append]
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  rw [hcard]

/-- The explicit whole-step effect, stated with the canonical numeric prefix. -/
theorem emitStep_effect_canonical_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) :
    (emitStep tm).effect values =
      Function.update
        (Function.update
          (Function.update
            (Function.update values Work.available
              (values Work.available +
                stepScheduleSize (transitionCases tm.toNTM).length
                  (Fintype.card tm.Q) k (values Work.horizon)
                  (stepAtomKindAt tm.toNTM (values Work.horizon))
                  (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                  (effectCaseChoiceAt tm.toNTM)))
            Work.configBase
              (stepScheduleOutputBase (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (values Work.horizon)
                (values Work.available)
                (stepAtomKindAt tm.toNTM (values Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                (effectCaseChoiceAt tm.toNTM)))
          Work.gateBound 0) Work.gateCount 0 := by
  rw [emitStep_effect_explicit_internal tm values hclean hhorizon,
    stepFormulasEffectSize_eq_prefixSize_internal]
  unfold stepFormulaSizeAtSpecializedInternal
  change Function.update
      (Function.update
        (Function.update
          (Function.update values Work.available
            (values Work.available +
              prefixSize (stepFormulaSizeAt (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (values Work.horizon)
                (stepAtomKindAt tm.toNTM (values Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                (effectCaseChoiceAt tm.toNTM))
                (stepAtomCount (Fintype.card tm.Q) k
                  (values Work.horizon)) +
              stepAtomCount (Fintype.card tm.Q) k
                (values Work.horizon)))
          Work.configBase
            (values Work.available +
              prefixSize (stepFormulaSizeAt (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (values Work.horizon)
                (stepAtomKindAt tm.toNTM (values Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (values Work.horizon))
                (effectCaseChoiceAt tm.toNTM))
                (stepAtomCount (Fintype.card tm.Q) k
                  (values Work.horizon))))
        Work.gateBound 0) Work.gateCount 0 = _
  simp [stepScheduleSize, stepScheduleOutputBase, Nat.add_assoc]

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
