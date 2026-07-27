/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Threshold.Internal
public import Complexitylib.Circuits.Unrolling.Acceptance.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Amplification.Defs

/-!
# Structural internals for parallel amplification circuits

This file proves the exact fold invariants of the proof-free acceptance-copy
builder. Raw-list length is the single source of gate accounting. The main
results locate completed verdict wires and bound the complete amplified
circuit by one cubic unrolling per run plus a quadratic majority threshold.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- The zero-copy prefix is the empty initial build. -/
theorem prefixAcceptanceCopiesBuild_zero_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    prefixAcceptanceCopiesBuild tm runs T n primaryAvailable 0 layout =
      initialAcceptanceCopiesBuild runs := by
  simp [prefixAcceptanceCopiesBuild, acceptanceCopiesBuildFrom]

/-- Advancing a proper prefix appends exactly the acceptance copy indexed by
the old prefix length. -/
theorem prefixAcceptanceCopiesBuild_succ_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (hi : i < runs) :
    prefixAcceptanceCopiesBuild tm runs T n primaryAvailable (i + 1) layout =
      acceptanceCopiesBuildStep tm layout
        (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i layout)
        ⟨i, hi⟩ := by
  have hindex : i < (List.finRange runs).length := by simpa using hi
  have hget : (List.finRange runs)[i]'hindex = (⟨i, hi⟩ : Fin runs) := by
    apply Fin.ext
    simp
  have htake :
      (List.finRange runs).take (i + 1) =
        (List.finRange runs).take i ++ [(⟨i, hi⟩ : Fin runs)] := by
    rw [List.take_succ_eq_append_getElem hindex, hget]
  simp [prefixAcceptanceCopiesBuild, acceptanceCopiesBuildFrom, htake,
    List.foldl_append]

/-- Taking the full run prefix recovers the complete copy build. -/
theorem prefixAcceptanceCopiesBuild_all_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    prefixAcceptanceCopiesBuild tm runs T n primaryAvailable runs layout =
      acceptanceCopiesBuild tm runs T n primaryAvailable layout := by
  have htake : (List.finRange runs).take runs = List.finRange runs := by
    simp
  unfold prefixAcceptanceCopiesBuild acceptanceCopiesBuild
  rw [htake]

/-- Circuit projection of the canonical prefix recurrence. -/
theorem prefixAcceptanceCopiesBuild_succ_circuit_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (hi : i < runs) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable (i + 1)
        layout).circuit =
      (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).circuit ++
        acceptanceRawCircuit tm T n
          ((prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).available primaryAvailable)
          ((layout.run ⟨i, hi⟩).weaken
            (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
              layout).circuit.length) := by
  rw [prefixAcceptanceCopiesBuild_succ_internal tm runs T n
    primaryAvailable i layout hi]
  rfl

/-- First-unused-wire projection of the canonical prefix recurrence. -/
theorem prefixAcceptanceCopiesBuild_succ_available_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (hi : i < runs) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable (i + 1)
        layout).available primaryAvailable =
      (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).available primaryAvailable +
        (acceptanceRawCircuit tm T n
          ((prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).available primaryAvailable)
          ((layout.run ⟨i, hi⟩).weaken
            (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
              layout).circuit.length)).length := by
  rw [prefixAcceptanceCopiesBuild_succ_internal tm runs T n
    primaryAvailable i layout hi]
  simp [acceptanceCopiesBuildStep, AcceptanceCopiesBuild.available,
    Nat.add_assoc]

/-- A newly completed run records the last wire of its acceptance fragment. -/
theorem prefixAcceptanceCopiesBuild_succ_verdict_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (hi : i < runs) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable (i + 1)
        layout).verdictWires ⟨i, hi⟩ =
      (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).available primaryAvailable +
        (acceptanceRawCircuit tm T n
          ((prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).available primaryAvailable)
          ((layout.run ⟨i, hi⟩).weaken
            (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
              layout).circuit.length)).length - 1 := by
  rw [prefixAcceptanceCopiesBuild_succ_internal tm runs T n
    primaryAvailable i layout hi]
  simp [acceptanceCopiesBuildStep]

/-- Completing run `i` leaves every other verdict entry unchanged. -/
theorem prefixAcceptanceCopiesBuild_succ_verdict_of_ne_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (hi : i < runs)
    (j : Fin runs) (hji : j ≠ ⟨i, hi⟩) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable (i + 1)
        layout).verdictWires j =
      (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
        layout).verdictWires j := by
  rw [prefixAcceptanceCopiesBuild_succ_internal tm runs T n
    primaryAvailable i layout hi]
  simp [acceptanceCopiesBuildStep, hji]

/-- A prefix's first unused wire is exactly its primary prefix plus its raw
circuit length. -/
theorem prefixAcceptanceCopiesBuild_available_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
      layout).available primaryAvailable =
        primaryAvailable +
          (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
            layout).circuit.length := by
  rfl

/-- Every completed verdict lies in the emitted-gate interval: at or after the
primary prefix and strictly before the prefix build's first unused wire. -/
theorem prefixAcceptanceCopiesBuild_verdict_bounds_internal (tm : NTM k)
    (runs T n primaryAvailable i : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable)
    (hi : i ≤ runs) (j : Fin runs) (hj : j.val < i) :
    primaryAvailable ≤
        (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).verdictWires j ∧
      (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).verdictWires j <
        (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
          layout).available primaryAvailable := by
  induction i generalizing j with
  | zero => omega
  | succ i ih =>
      have hiruns : i < runs := by omega
      let previous :=
        prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i layout
      let runLayout :=
        (layout.run ⟨i, hiruns⟩).weaken previous.circuit.length
      let fragment :=
        acceptanceRawCircuit tm T n (previous.available primaryAvailable)
          runLayout
      have hfragmentLength :
          fragment.length =
            traceFragmentSize tm T n (previous.available primaryAvailable)
                runLayout + 1 := by
        exact length_acceptanceRawCircuit_internal tm T n
          (previous.available primaryAvailable) runLayout
      have hfragmentPositive : 0 < fragment.length := by omega
      by_cases hji : j = (⟨i, hiruns⟩ : Fin runs)
      · subst j
        rw [prefixAcceptanceCopiesBuild_succ_verdict_internal tm runs T n
          primaryAvailable i layout hiruns]
        rw [prefixAcceptanceCopiesBuild_succ_available_internal tm runs T n
          primaryAvailable i layout hiruns]
        change primaryAvailable ≤
            previous.available primaryAvailable + fragment.length - 1 ∧
          previous.available primaryAvailable + fragment.length - 1 <
            previous.available primaryAvailable + fragment.length
        have hprimary :
            primaryAvailable ≤ previous.available primaryAvailable := by
          simp [previous, AcceptanceCopiesBuild.available]
        omega
      · have hjlt : j.val < i := by
          have hjne : j.val ≠ i := by
            intro heq
            apply hji
            apply Fin.ext
            exact heq
          omega
        have hprevious := ih (by omega) j hjlt
        rw [prefixAcceptanceCopiesBuild_succ_verdict_of_ne_internal tm runs T n
          primaryAvailable i layout hiruns j hji]
        rw [prefixAcceptanceCopiesBuild_succ_available_internal tm runs T n
          primaryAvailable i layout hiruns]
        change primaryAvailable ≤ previous.verdictWires j ∧
          previous.verdictWires j <
            previous.available primaryAvailable + fragment.length
        exact ⟨hprevious.1,
          lt_of_lt_of_le hprevious.2 (Nat.le_add_right _ _)⟩

/-- Every complete verdict reference names a gate emitted by the copy build. -/
theorem acceptanceCopiesVerdictWires_bounds_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) (j : Fin runs) :
    primaryAvailable ≤
        acceptanceCopiesVerdictWires tm runs T n primaryAvailable layout j ∧
      acceptanceCopiesVerdictWires tm runs T n primaryAvailable layout j <
        primaryAvailable +
          acceptanceCopiesSize tm runs T n primaryAvailable layout := by
  have h := prefixAcceptanceCopiesBuild_verdict_bounds_internal tm runs T n
    primaryAvailable runs layout (Nat.le_refl runs) j j.isLt
  rw [prefixAcceptanceCopiesBuild_all_internal tm runs T n primaryAvailable
    layout] at h
  simpa [acceptanceCopiesVerdictWires, acceptanceCopiesSize,
    AcceptanceCopiesBuild.available] using h

/-- Folding acceptance copies adds at most one cubic unrolling bound per run
index in the supplied list. -/
theorem acceptanceCopiesBuildFrom_length_le_internal (tm : NTM k)
    {runs T n primaryAvailable : ℕ}
    (layout : ParallelInputWires runs T n primaryAvailable)
    (build : AcceptanceCopiesBuild runs) (indices : List (Fin runs)) :
    (acceptanceCopiesBuildFrom tm layout build indices).circuit.length ≤
      build.circuit.length + indices.length *
        (acceptanceSizeCoeff tm * (T + 2) ^ 3) := by
  induction indices generalizing build with
  | nil => simp [acceptanceCopiesBuildFrom]
  | cons j indices ih =>
      rw [acceptanceCopiesBuildFrom, List.foldl_cons]
      refine le_trans (ih (acceptanceCopiesBuildStep tm layout build j)) ?_
      let runLayout := (layout.run j).weaken build.circuit.length
      have hcopy := length_acceptanceRawCircuit_le_internal tm T n
        (build.available primaryAvailable) runLayout
      simp only [acceptanceCopiesBuildStep, List.length_append,
        List.length_cons]
      calc
        build.circuit.length +
              (acceptanceRawCircuit tm T n
                (build.available primaryAvailable) runLayout).length +
              indices.length * (acceptanceSizeCoeff tm * (T + 2) ^ 3) ≤
            build.circuit.length +
              (acceptanceSizeCoeff tm * (T + 2) ^ 3) +
              indices.length * (acceptanceSizeCoeff tm * (T + 2) ^ 3) :=
          Nat.add_le_add_right (Nat.add_le_add_left hcopy _) _
        _ = build.circuit.length + (indices.length + 1) *
            (acceptanceSizeCoeff tm * (T + 2) ^ 3) := by ring

/-- All acceptance copies together use at most `runs` times the cubic
single-run gate bound. -/
theorem acceptanceCopiesSize_le_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    acceptanceCopiesSize tm runs T n primaryAvailable layout ≤
      runs * (acceptanceSizeCoeff tm * (T + 2) ^ 3) := by
  simpa [acceptanceCopiesSize, acceptanceCopiesBuild,
    initialAcceptanceCopiesBuild] using
      (acceptanceCopiesBuildFrom_length_le_internal tm layout
        (initialAcceptanceCopiesBuild runs) (List.finRange runs))

/-- Appending strict majority adds its exact unary-threshold gate count. -/
theorem length_amplifiedAcceptanceRawCircuit_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout).length =
      acceptanceCopiesSize tm runs T n primaryAvailable layout +
        (3 + 2 * runs * strictMajorityThreshold runs) := by
  rw [amplifiedAcceptanceRawCircuit, List.length_append,
    CircuitCode.Threshold.length_compileRaw_internal]
  rfl

/-- The strict-majority threshold table is bounded by `2 * runs²` gates
beyond its three fixed gates. -/
theorem thresholdTableSize_le_square_internal (runs : ℕ) :
    2 * runs * strictMajorityThreshold runs ≤ 2 * runs * runs := by
  cases runs with
  | zero => simp [strictMajorityThreshold]
  | succ runs =>
      have hthreshold : strictMajorityThreshold (runs + 1) ≤ runs + 1 := by
        simp only [strictMajorityThreshold]
        omega
      exact Nat.mul_le_mul_left (2 * (runs + 1)) hthreshold

/-- Parallel amplification has one cubic unrolling per run plus a quadratic
strict-majority threshold. -/
theorem length_amplifiedAcceptanceRawCircuit_le_internal (tm : NTM k)
    (runs T n primaryAvailable : ℕ)
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable layout).length ≤
      runs * (acceptanceSizeCoeff tm * (T + 2) ^ 3) + 3 +
        2 * runs * runs := by
  rw [length_amplifiedAcceptanceRawCircuit_internal]
  have hcopies := acceptanceCopiesSize_le_internal tm runs T n
    primaryAvailable layout
  have hthreshold := thresholdTableSize_le_square_internal runs
  omega

end CircuitUnrolling

end Complexity
