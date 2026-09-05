/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Topology

/-!
# Topology of tiled bounded-trace circuits

This internal module proves that initialization followed by any sequence of
packed transition layers is topologically well formed. The recursive proof
tracks the exact circuit length, first unused wire, and end of the current
configuration block supplied by the trace-structure layer.
-/


public section

namespace Complexity

namespace CircuitUnrolling

/-- The initial-configuration portion of a trace build is topologically well
formed after its primary-wire prefix. -/
theorem initialTraceBuild_topologicallyWellFormed_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (initialTraceBuild tm T n available layout).circuit.TopologicallyWellFormed
      available := by
  simpa [initialTraceBuild] using
    initFragment_topologicallyWellFormed_internal tm T n available layout

/-- Appending one packed transition preserves topology when the accumulated
build records its exact length, end wire, and current configuration block. -/
theorem traceBuildStep_topologicallyWellFormed_internal
    (tm : NTM k) {T n primaryAvailable : ℕ} [NeZero primaryAvailable]
    (layout : InputWires T n primaryAvailable) (build : TraceBuild)
    (i : Fin T)
    (hwell : build.circuit.TopologicallyWellFormed primaryAvailable)
    (hlength : build.circuit.length = build.size)
    (havailable : build.available = primaryAvailable + build.size)
    (houtputEnd : build.configBase + configWidth tm T = build.available) :
    (traceBuildStep tm layout build i).circuit.TopologicallyWellFormed
      primaryAvailable := by
  have hprimary : 0 < primaryAvailable :=
    Nat.pos_of_ne_zero (NeZero.ne primaryAvailable)
  have hbuildAvailable : 0 < build.available := by
    rw [havailable]
    omega
  let : NeZero build.available := ⟨Nat.ne_of_gt hbuildAvailable⟩
  have hchoice : (layout.choice i).val < build.available := by
    exact (layout.choice i).isLt.trans_le (by rw [havailable]; omega)
  have hconfig : build.configBase + configWidth tm T ≤ build.available :=
    houtputEnd.le
  have horigin : primaryAvailable + build.circuit.length = build.available := by
    rw [hlength, ← havailable]
  rw [traceBuildStep]
  apply (CircuitCode.RawCircuit.topologicallyWellFormed_append
    primaryAvailable build.circuit
      (stepFragment tm T build.configBase (layout.choice i).val
        build.available)).2
  refine ⟨hwell, ?_⟩
  rw [horigin]
  exact stepFragment_topologicallyWellFormed_internal tm T build.configBase
    (layout.choice i).val build.available hchoice hconfig

/-- Folding any list of transition indices preserves topology together with
the trace build's structural invariants. -/
theorem traceBuildFrom_topologicallyWellFormed_internal
    (tm : NTM k) {T n primaryAvailable : ℕ} [NeZero primaryAvailable]
    (layout : InputWires T n primaryAvailable) (build : TraceBuild)
    (indices : List (Fin T))
    (hwell : build.circuit.TopologicallyWellFormed primaryAvailable)
    (hlength : build.circuit.length = build.size)
    (havailable : build.available = primaryAvailable + build.size)
    (houtputEnd : build.configBase + configWidth tm T = build.available) :
    (traceBuildFrom tm layout build indices).circuit.TopologicallyWellFormed
      primaryAvailable := by
  induction indices generalizing build with
  | nil => simpa [traceBuildFrom] using hwell
  | cons i indices ih =>
      rw [traceBuildFrom, List.foldl_cons]
      apply ih (traceBuildStep tm layout build i)
      · exact traceBuildStep_topologicallyWellFormed_internal tm layout build i
          hwell hlength havailable houtputEnd
      · exact traceBuildStep_length_internal tm layout build i hlength
      · exact traceBuildStep_available_internal tm layout build i havailable
      · exact traceBuildStep_outputEnd_internal tm layout build i

/-- Every canonical partial trace build is topologically well formed. -/
theorem prefixTraceBuild_topologicallyWellFormed_internal
    (tm : NTM k) (T n available i : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (prefixTraceBuild tm T n available i layout).circuit.TopologicallyWellFormed
      available := by
  unfold prefixTraceBuild
  apply traceBuildFrom_topologicallyWellFormed_internal tm layout
  · exact initialTraceBuild_topologicallyWellFormed_internal tm T n available layout
  · exact initialTraceBuild_length_internal tm T n available layout
  · exact initialTraceBuild_available_internal tm T n available layout
  · exact initialTraceBuild_outputEnd_internal tm T n available layout

/-- The complete trace build is topologically well formed. -/
theorem traceBuild_topologicallyWellFormed_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (traceBuild tm T n available layout).circuit.TopologicallyWellFormed
      available := by
  unfold traceBuild
  apply traceBuildFrom_topologicallyWellFormed_internal tm layout
  · exact initialTraceBuild_topologicallyWellFormed_internal tm T n available layout
  · exact initialTraceBuild_length_internal tm T n available layout
  · exact initialTraceBuild_available_internal tm T n available layout
  · exact initialTraceBuild_outputEnd_internal tm T n available layout

/-- The complete bounded-trace fragment is topologically well formed after its
primary-wire prefix. -/
theorem traceFragment_topologicallyWellFormed_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (traceFragment tm T n available layout).TopologicallyWellFormed available := by
  unfold traceFragment
  exact traceBuild_topologicallyWellFormed_internal tm T n available layout

end CircuitUnrolling

end Complexity
