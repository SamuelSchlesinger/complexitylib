/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Trace.Defs
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Size

/-!
# Structural properties of tiled bounded-trace circuits

This internal module proves that the recursive trace layout tracks its exact
gate count and first unused wire. It also identifies the final packed
configuration block and derives a machine-dependent cubic size bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Initialization records its exact emitted gate count. -/
theorem initialTraceBuild_length_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (initialTraceBuild tm T n available layout).circuit.length =
      (initialTraceBuild tm T n available layout).size := by
  simp [initialTraceBuild, length_initFragment_internal]

/-- Initialization's first unused wire is its primary prefix plus its size. -/
theorem initialTraceBuild_available_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (initialTraceBuild tm T n available layout).available =
      available + (initialTraceBuild tm T n available layout).size := by
  rfl

/-- The initialized configuration block ends at the first unused wire. -/
theorem initialTraceBuild_outputEnd_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (initialTraceBuild tm T n available layout).configBase + configWidth tm T =
      (initialTraceBuild tm T n available layout).available := by
  rfl

/-- Appending one layer preserves the exact circuit-length invariant. -/
theorem traceBuildStep_length_internal (tm : NTM k) {T n primaryAvailable : ℕ}
    (layout : InputWires T n primaryAvailable) (build : TraceBuild)
    (i : Fin T) (hbuild : build.circuit.length = build.size) :
    (traceBuildStep tm layout build i).circuit.length =
      (traceBuildStep tm layout build i).size := by
  simp [traceBuildStep, length_stepFragment_internal, hbuild]

/-- Appending one layer preserves the primary-prefix/end-wire invariant. -/
theorem traceBuildStep_available_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (i : Fin T)
    (hbuild : build.available = primaryAvailable + build.size) :
    (traceBuildStep tm layout build i).available =
      primaryAvailable + (traceBuildStep tm layout build i).size := by
  simp [traceBuildStep, hbuild, Nat.add_assoc]

/-- A newly packed successor block ends at the new first unused wire. -/
theorem traceBuildStep_outputEnd_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (i : Fin T) :
    (traceBuildStep tm layout build i).configBase + configWidth tm T =
      (traceBuildStep tm layout build i).available := by
  simpa [traceBuildStep] using
    stepOutputEnd_eq_internal tm T build.configBase (layout.choice i).val
      build.available

/-- Folding transition indices preserves the exact circuit-length invariant. -/
theorem traceBuildFrom_length_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (indices : List (Fin T))
    (hbuild : build.circuit.length = build.size) :
    (traceBuildFrom tm layout build indices).circuit.length =
      (traceBuildFrom tm layout build indices).size := by
  induction indices generalizing build with
  | nil => simpa [traceBuildFrom] using hbuild
  | cons i indices ih =>
      rw [traceBuildFrom, List.foldl_cons]
      exact ih (traceBuildStep tm layout build i)
        (traceBuildStep_length_internal tm layout build i hbuild)

/-- Folding transition indices preserves the primary-prefix/end-wire invariant. -/
theorem traceBuildFrom_available_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (indices : List (Fin T))
    (hbuild : build.available = primaryAvailable + build.size) :
    (traceBuildFrom tm layout build indices).available =
      primaryAvailable + (traceBuildFrom tm layout build indices).size := by
  induction indices generalizing build with
  | nil => simpa [traceBuildFrom] using hbuild
  | cons i indices ih =>
      rw [traceBuildFrom, List.foldl_cons]
      exact ih (traceBuildStep tm layout build i)
        (traceBuildStep_available_internal tm layout build i hbuild)

/-- A folded sequence leaves its final packed block at the circuit end. -/
theorem traceBuildFrom_outputEnd_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (indices : List (Fin T))
    (hbuild : build.configBase + configWidth tm T = build.available) :
    (traceBuildFrom tm layout build indices).configBase + configWidth tm T =
      (traceBuildFrom tm layout build indices).available := by
  induction indices generalizing build with
  | nil => simpa [traceBuildFrom] using hbuild
  | cons i indices ih =>
      rw [traceBuildFrom, List.foldl_cons]
      exact ih (traceBuildStep tm layout build i)
        (traceBuildStep_outputEnd_internal tm layout build i)

/-- A folded sequence adds at most one quadratic layer bound per index. -/
theorem traceBuildFrom_size_le_internal (tm : NTM k)
    {T n primaryAvailable : ℕ} (layout : InputWires T n primaryAvailable)
    (build : TraceBuild) (indices : List (Fin T)) :
    (traceBuildFrom tm layout build indices).size ≤
      build.size + indices.length * (stepSizeCoeff tm * (T + 2) ^ 2) := by
  induction indices generalizing build with
  | nil => simp [traceBuildFrom]
  | cons i indices ih =>
      rw [traceBuildFrom, List.foldl_cons]
      refine le_trans (ih (traceBuildStep tm layout build i)) ?_
      have hstep := stepFragmentSize_le_internal tm T build.configBase
        (layout.choice i).val
      simp only [traceBuildStep, List.length_cons]
      calc
        build.size + stepFragmentSize tm T build.configBase (layout.choice i).val +
              indices.length * (stepSizeCoeff tm * (T + 2) ^ 2) ≤
            build.size + (stepSizeCoeff tm * (T + 2) ^ 2) +
              indices.length * (stepSizeCoeff tm * (T + 2) ^ 2) :=
          Nat.add_le_add_right (Nat.add_le_add_left hstep _) _
        _ = build.size + (indices.length + 1) *
            (stepSizeCoeff tm * (T + 2) ^ 2) := by ring

/-- The zero-step prefix build is exactly the initialized configuration. -/
theorem prefixTraceBuild_zero_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    prefixTraceBuild tm T n available 0 layout =
      initialTraceBuild tm T n available layout := by
  simp [prefixTraceBuild, traceBuildFrom]

/-- Advancing a proper prefix appends exactly its indexed transition layer. -/
theorem prefixTraceBuild_succ_internal (tm : NTM k) (T n available i : ℕ)
    (layout : InputWires T n available) (hi : i < T) :
    prefixTraceBuild tm T n available (i + 1) layout =
      traceBuildStep tm layout (prefixTraceBuild tm T n available i layout)
        ⟨i, hi⟩ := by
  have hindex : i < (List.finRange T).length := by simpa using hi
  have hget : (List.finRange T)[i]'hindex = (⟨i, hi⟩ : Fin T) := by
    apply Fin.ext
    simp
  have htake :
      (List.finRange T).take (i + 1) =
        (List.finRange T).take i ++ [(⟨i, hi⟩ : Fin T)] := by
    rw [List.take_succ_eq_append_getElem hindex, hget]
  simp [prefixTraceBuild, traceBuildFrom, htake, List.foldl_append]

/-- Circuit projection of the canonical prefix recurrence. -/
theorem prefixTraceBuild_succ_circuit_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) (hi : i < T) :
    (prefixTraceBuild tm T n available (i + 1) layout).circuit =
      (prefixTraceBuild tm T n available i layout).circuit ++
        stepFragment tm T
          (prefixTraceBuild tm T n available i layout).configBase
          (layout.choice ⟨i, hi⟩).val
          (prefixTraceBuild tm T n available i layout).available := by
  rw [prefixTraceBuild_succ_internal tm T n available i layout hi]
  rfl

/-- Final-configuration-base projection of the canonical prefix recurrence. -/
theorem prefixTraceBuild_succ_configBase_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) (hi : i < T) :
    (prefixTraceBuild tm T n available (i + 1) layout).configBase =
      stepOutputBase tm T
        (prefixTraceBuild tm T n available i layout).configBase
        (layout.choice ⟨i, hi⟩).val
        (prefixTraceBuild tm T n available i layout).available := by
  rw [prefixTraceBuild_succ_internal tm T n available i layout hi]
  rfl

/-- End-wire projection of the canonical prefix recurrence. -/
theorem prefixTraceBuild_succ_available_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) (hi : i < T) :
    (prefixTraceBuild tm T n available (i + 1) layout).available =
      (prefixTraceBuild tm T n available i layout).available +
        stepFragmentSize tm T
          (prefixTraceBuild tm T n available i layout).configBase
          (layout.choice ⟨i, hi⟩).val := by
  rw [prefixTraceBuild_succ_internal tm T n available i layout hi]
  rfl

/-- Gate-count projection of the canonical prefix recurrence. -/
theorem prefixTraceBuild_succ_size_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) (hi : i < T) :
    (prefixTraceBuild tm T n available (i + 1) layout).size =
      (prefixTraceBuild tm T n available i layout).size +
        stepFragmentSize tm T
          (prefixTraceBuild tm T n available i layout).configBase
          (layout.choice ⟨i, hi⟩).val := by
  rw [prefixTraceBuild_succ_internal tm T n available i layout hi]
  rfl

/-- Every prefix build records its exact circuit length. -/
theorem prefixTraceBuild_length_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) :
    (prefixTraceBuild tm T n available i layout).circuit.length =
      (prefixTraceBuild tm T n available i layout).size := by
  apply traceBuildFrom_length_internal
  exact initialTraceBuild_length_internal tm T n available layout

/-- Every prefix ends its recorded size after the primary input prefix. -/
theorem prefixTraceBuild_available_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) :
    (prefixTraceBuild tm T n available i layout).available =
      available + (prefixTraceBuild tm T n available i layout).size := by
  apply traceBuildFrom_available_internal
  exact initialTraceBuild_available_internal tm T n available layout

/-- Every prefix's packed configuration block reaches its current end wire. -/
theorem prefixTraceBuild_outputEnd_internal (tm : NTM k)
    (T n available i : ℕ) (layout : InputWires T n available) :
    (prefixTraceBuild tm T n available i layout).configBase + configWidth tm T =
      (prefixTraceBuild tm T n available i layout).available := by
  apply traceBuildFrom_outputEnd_internal
  exact initialTraceBuild_outputEnd_internal tm T n available layout

/-- Taking all `T` canonical indices recovers the complete trace build. -/
theorem prefixTraceBuild_eq_traceBuild_internal (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    prefixTraceBuild tm T n available T layout =
      traceBuild tm T n available layout := by
  have htake : (List.finRange T).take T = List.finRange T := by
    simp
  unfold prefixTraceBuild traceBuild
  rw [htake]

/-- The complete trace build records its exact circuit length. -/
theorem traceBuild_length_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (traceBuild tm T n available layout).circuit.length =
      (traceBuild tm T n available layout).size := by
  apply traceBuildFrom_length_internal
  exact initialTraceBuild_length_internal tm T n available layout

/-- The complete trace ends exactly its recorded size after the primary prefix. -/
theorem traceBuild_available_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (traceBuild tm T n available layout).available =
      available + (traceBuild tm T n available layout).size := by
  apply traceBuildFrom_available_internal
  exact initialTraceBuild_available_internal tm T n available layout

/-- The complete trace's final packed configuration reaches the circuit end. -/
theorem traceBuild_outputEnd_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (traceBuild tm T n available layout).configBase + configWidth tm T =
      (traceBuild tm T n available layout).available := by
  apply traceBuildFrom_outputEnd_internal
  exact initialTraceBuild_outputEnd_internal tm T n available layout

/-- Internal exact gate count of the complete bounded-trace fragment. -/
theorem length_traceFragment_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (traceFragment tm T n available layout).length =
      traceFragmentSize tm T n available layout := by
  exact traceBuild_length_internal tm T n available layout

/-- Internal final-output block identity for the complete trace fragment. -/
theorem traceOutputEnd_eq_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    traceOutputBase tm T n available layout + configWidth tm T =
      available + traceFragmentSize tm T n available layout := by
  rw [traceOutputBase, traceFragmentSize]
  rw [traceBuild_outputEnd_internal, traceBuild_available_internal]

/-- The complete bounded trace has machine-dependent cubic gate count. -/
theorem traceFragmentSize_le_internal (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    traceFragmentSize tm T n available layout ≤
      traceSizeCoeff tm * (T + 2) ^ 3 := by
  have hfold := traceBuildFrom_size_le_internal tm layout
    (initialTraceBuild tm T n available layout) (List.finRange T)
  have hwidth := configWidth_le_linear_internal tm T
  have hstepHorizon : T * (T + 2) ^ 2 ≤ (T + 2) ^ 3 := by
    calc
      T * (T + 2) ^ 2 ≤ (T + 2) * (T + 2) ^ 2 :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (T + 2) ^ 3 := by ring
  have hwidthHorizon : T + 2 ≤ (T + 2) ^ 3 := by
    have hone : 1 ≤ (T + 2) ^ 2 := Nat.one_le_pow 2 (T + 2) (by omega)
    calc
      T + 2 = (T + 2) * 1 := by simp
      _ ≤ (T + 2) * (T + 2) ^ 2 := Nat.mul_le_mul_left _ hone
      _ = (T + 2) ^ 3 := by ring
  simp only [List.length_finRange, initialTraceBuild] at hfold
  calc
    (traceBuild tm T n available layout).size ≤
        configWidth tm T + T * (stepSizeCoeff tm * (T + 2) ^ 2) := hfold
    _ ≤ (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) +
        T * (stepSizeCoeff tm * (T + 2) ^ 2) :=
      Nat.add_le_add_right hwidth _
    _ ≤ (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) ^ 3 +
        stepSizeCoeff tm * (T + 2) ^ 3 := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ hwidthHorizon
      · calc
          T * (stepSizeCoeff tm * (T + 2) ^ 2) =
              stepSizeCoeff tm * (T * (T + 2) ^ 2) := by ring
          _ ≤ stepSizeCoeff tm * (T + 2) ^ 3 :=
            Nat.mul_le_mul_left _ hstepHorizon
    _ = traceSizeCoeff tm * (T + 2) ^ 3 := by
      simp only [traceSizeCoeff]
      ring

end CircuitUnrolling

end Complexity
