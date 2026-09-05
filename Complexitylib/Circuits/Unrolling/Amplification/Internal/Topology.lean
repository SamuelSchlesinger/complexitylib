/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Unrolling.Amplification.Internal.Structure

/-!
# Topology internals for parallel amplification circuits

Independent acceptance copies are appended after one shared primary-input
prefix. Their recorded verdict wires then feed the final strict-majority
threshold fragment. This file proves that both stages are topologically
ordered and that the final nonempty raw circuit is well formed.
-/


public section

namespace Complexity

namespace CircuitUnrolling

/-- The empty acceptance-copy build is topologically well formed. -/
theorem initialAcceptanceCopiesBuild_topologicallyWellFormed_internal
    (runs primaryAvailable : ℕ) :
    (initialAcceptanceCopiesBuild runs).circuit.TopologicallyWellFormed
      primaryAvailable := by
  simp [initialAcceptanceCopiesBuild,
    CircuitCode.RawCircuit.TopologicallyWellFormed]

/-- Appending one independent acceptance copy preserves topology. -/
theorem acceptanceCopiesBuildStep_topologicallyWellFormed_internal
    (tm : NTM k) {runs T n primaryAvailable : ℕ}
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (build : AcceptanceCopiesBuild runs) (j : Fin runs)
    (hbuild : build.circuit.TopologicallyWellFormed primaryAvailable) :
    ((acceptanceCopiesBuildStep tm layout build j).circuit
      ).TopologicallyWellFormed primaryAvailable := by
  let available := build.available primaryAvailable
  let runLayout := (layout.run j).weaken build.circuit.length
  have : NeZero available := ⟨by
    simp [available, AcceptanceCopiesBuild.available,
      NeZero.ne primaryAvailable]⟩
  change (build.circuit ++ acceptanceRawCircuit tm T n available
    runLayout).TopologicallyWellFormed primaryAvailable
  rw [CircuitCode.RawCircuit.topologicallyWellFormed_append]
  refine ⟨hbuild, ?_⟩
  have hcopy := acceptanceRawCircuit_topologicallyWellFormed_internal
    tm T n available runLayout
  simpa [available, AcceptanceCopiesBuild.available] using hcopy

/-- Folding any sequence of run indices preserves copy topology. -/
theorem acceptanceCopiesBuildFrom_topologicallyWellFormed_internal
    (tm : NTM k) {runs T n primaryAvailable : ℕ}
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable)
    (build : AcceptanceCopiesBuild runs) (indices : List (Fin runs))
    (hbuild : build.circuit.TopologicallyWellFormed primaryAvailable) :
    ((acceptanceCopiesBuildFrom tm layout build indices).circuit
      ).TopologicallyWellFormed primaryAvailable := by
  induction indices generalizing build with
  | nil => simpa [acceptanceCopiesBuildFrom] using hbuild
  | cons j indices ih =>
      rw [acceptanceCopiesBuildFrom, List.foldl_cons]
      exact ih (acceptanceCopiesBuildStep tm layout build j)
        (acceptanceCopiesBuildStep_topologicallyWellFormed_internal
          tm layout build j hbuild)

/-- Every canonical prefix of the acceptance-copy fold is topologically
ordered after the shared primary-input prefix. -/
theorem prefixAcceptanceCopiesBuild_topologicallyWellFormed_internal
    (tm : NTM k) (runs T n primaryAvailable i : ℕ)
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (prefixAcceptanceCopiesBuild tm runs T n primaryAvailable i
      layout).circuit.TopologicallyWellFormed primaryAvailable := by
  unfold prefixAcceptanceCopiesBuild
  apply acceptanceCopiesBuildFrom_topologicallyWellFormed_internal tm layout
  exact initialAcceptanceCopiesBuild_topologicallyWellFormed_internal
    runs primaryAvailable

/-- The complete collection of independent acceptance copies is
topologically ordered. -/
theorem acceptanceCopiesBuild_topologicallyWellFormed_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ)
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (acceptanceCopiesBuild tm runs T n primaryAvailable
      layout).circuit.TopologicallyWellFormed primaryAvailable := by
  unfold acceptanceCopiesBuild
  apply acceptanceCopiesBuildFrom_topologicallyWellFormed_internal tm layout
  exact initialAcceptanceCopiesBuild_topologicallyWellFormed_internal
    runs primaryAvailable

/-- The acceptance copies followed by their strict-majority threshold are
topologically ordered after any nonempty primary prefix. -/
theorem amplifiedAcceptanceRawCircuit_topologicallyWellFormed_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ)
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
      layout).TopologicallyWellFormed primaryAvailable := by
  let built := acceptanceCopiesBuild tm runs T n primaryAvailable layout
  change (built.circuit ++ CircuitCode.Threshold.compileRaw
    (primaryAvailable + built.circuit.length)
      (strictMajorityThreshold runs) built.verdictWires
    ).TopologicallyWellFormed primaryAvailable
  rw [CircuitCode.RawCircuit.topologicallyWellFormed_append]
  refine ⟨?_, ?_⟩
  · simpa [built] using
      acceptanceCopiesBuild_topologicallyWellFormed_internal tm runs T n
        primaryAvailable layout
  · have : NeZero (primaryAvailable + built.circuit.length) := ⟨by
      simp [NeZero.ne primaryAvailable]⟩
    have hrefs : ∀ j, built.verdictWires j <
        primaryAvailable + built.circuit.length := by
      intro j
      have hbounds := acceptanceCopiesVerdictWires_bounds_internal tm runs T n
        primaryAvailable layout j
      simpa [built, acceptanceCopiesVerdictWires, acceptanceCopiesSize] using
        hbounds.2
    exact CircuitCode.Threshold.topologicallyWellFormed_compileRaw_internal
      (primaryAvailable + built.circuit.length)
        (strictMajorityThreshold runs) built.verdictWires hrefs

/-- The final threshold fragment is nonempty, so amplified topology upgrades
to full raw-circuit well-formedness. -/
theorem amplifiedAcceptanceRawCircuit_wellFormed_internal
    (tm : NTM k) (runs T n primaryAvailable : ℕ)
    [NeZero primaryAvailable]
    (layout : ParallelInputWires runs T n primaryAvailable) :
    (amplifiedAcceptanceRawCircuit tm runs T n primaryAvailable
      layout).WellFormed primaryAvailable := by
  refine ⟨?_, amplifiedAcceptanceRawCircuit_topologicallyWellFormed_internal
    tm runs T n primaryAvailable layout⟩
  apply List.ne_nil_of_length_pos
  rw [length_amplifiedAcceptanceRawCircuit_internal]
  omega

end CircuitUnrolling

end Complexity
