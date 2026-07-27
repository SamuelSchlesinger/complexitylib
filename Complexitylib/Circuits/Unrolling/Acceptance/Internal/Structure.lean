/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Acceptance.Defs
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Topology
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Structure of bounded-trace acceptance circuits

This internal module proves that appending the final halt-and-output test adds
exactly one gate, preserves topological well-formedness, and retains a cubic
machine-dependent size bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- A final acceptance gate is well formed whenever its packed configuration
block lies in the existing wire prefix. -/
theorem acceptanceGate_wellFormedAt_internal (tm : NTM k)
    (T configBase available : ℕ)
    (hconfig : configBase + configWidth tm T ≤ available) :
    (acceptanceGate tm T configBase).WellFormedAt available := by
  unfold acceptanceGate CircuitCode.RawGate.WellFormedAt configWire
  constructor
  · change configBase + configIndex tm T (.state tm.qhalt) < available
    exact lt_of_lt_of_le
      (Nat.add_lt_add_left (configIndex_lt tm T (.state tm.qhalt)) configBase)
      hconfig
  · change configBase +
      configIndex tm T (.cell .output ⟨1, by omega⟩ Γ.one) < available
    exact lt_of_lt_of_le
      (Nat.add_lt_add_left
        (configIndex_lt tm T (.cell .output ⟨1, by omega⟩ Γ.one)) configBase)
      hconfig

/-- The canonical final acceptance gate points only into the final packed
configuration block at the end of the trace fragment. -/
theorem finalAcceptanceGate_wellFormedAt_internal (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    (acceptanceGate tm T (traceOutputBase tm T n available layout)).WellFormedAt
      (available + traceFragmentSize tm T n available layout) := by
  apply acceptanceGate_wellFormedAt_internal
  exact (traceOutputEnd_eq_internal tm T n available layout).le

/-- Appending the final test adds exactly one gate to the complete trace. -/
theorem length_acceptanceRawCircuit_internal (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).length =
      traceFragmentSize tm T n available layout + 1 := by
  simp [acceptanceRawCircuit, length_traceFragment_internal]

/-- The complete trace plus its final acceptance gate is topologically ordered
after the primary-wire prefix. -/
theorem acceptanceRawCircuit_topologicallyWellFormed_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).TopologicallyWellFormed
      available := by
  rw [acceptanceRawCircuit,
    CircuitCode.RawCircuit.topologicallyWellFormed_append]
  refine ⟨traceFragment_topologicallyWellFormed_internal tm T n available layout, ?_⟩
  rw [length_traceFragment_internal]
  simpa [CircuitCode.RawCircuit.TopologicallyWellFormed] using
    finalAcceptanceGate_wellFormedAt_internal tm T n available layout

/-- The appended acceptance gate makes the raw circuit nonempty, so topology
upgrades directly to full raw-circuit well-formedness. -/
theorem acceptanceRawCircuit_wellFormed_internal
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).WellFormed available := by
  refine ⟨?_, acceptanceRawCircuit_topologicallyWellFormed_internal
    tm T n available layout⟩
  simp [acceptanceRawCircuit]

/-- The final acceptance gate is absorbed into a machine-dependent cubic
gate-count bound. -/
theorem length_acceptanceRawCircuit_le_internal (tm : NTM k)
    (T n available : ℕ) (layout : InputWires T n available) :
    (acceptanceRawCircuit tm T n available layout).length ≤
      acceptanceSizeCoeff tm * (T + 2) ^ 3 := by
  have htrace := traceFragmentSize_le_internal tm T n available layout
  have hone : 1 ≤ (T + 2) ^ 3 :=
    Nat.one_le_pow 3 (T + 2) (by omega)
  rw [length_acceptanceRawCircuit_internal, acceptanceSizeCoeff]
  calc
    traceFragmentSize tm T n available layout + 1 ≤
        traceSizeCoeff tm * (T + 2) ^ 3 + 1 :=
      Nat.add_le_add_right htrace 1
    _ ≤ traceSizeCoeff tm * (T + 2) ^ 3 + (T + 2) ^ 3 :=
      Nat.add_le_add_left hone _
    _ = (traceSizeCoeff tm + 1) * (T + 2) ^ 3 := by ring

end CircuitUnrolling

end Complexity
