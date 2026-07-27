/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Trace.Defs
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Evaluation
public import Complexitylib.Circuits.Unrolling.Trace.Internal.HeadBounds
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Trace.Internal.Topology

/-!
# Circuits for bounded Turing-machine traces

This module exposes the complete bounded-trace fragment: an initialized
one-hot configuration followed by one packed transition layer per choice bit.
Its final configuration occupies a contiguous block at the end of the
fragment. The construction is topologically well formed at positive primary
arity and has machine-dependent cubic size in the trace horizon.

## Main results

- `length_traceFragment`: exact gate count.
- `traceOutputEnd_eq`: the final configuration block ends with the fragment.
- `traceFragment_topologicallyWellFormed`: every reference points backward.
- `evalAux?_traceFragment`: evaluation encodes the complete bounded trace.
- `traceFragmentSize_le`: a machine-dependent cubic gate-count bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- A complete bounded-trace fragment emits exactly its recursively recorded
gate count. -/
@[simp] theorem length_traceFragment (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (traceFragment tm T n available layout).length =
      traceFragmentSize tm T n available layout :=
  length_traceFragment_internal tm T n available layout

/-- The final packed configuration block ends exactly at the end of the trace
fragment. -/
theorem traceOutputEnd_eq (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    traceOutputBase tm T n available layout + configWidth tm T =
      available + traceFragmentSize tm T n available layout :=
  traceOutputEnd_eq_internal tm T n available layout

/-- A complete trace fragment is topologically well formed whenever its
primary-wire prefix is nonempty. -/
theorem traceFragment_topologicallyWellFormed
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) :
    (traceFragment tm T n available layout).TopologicallyWellFormed available :=
  traceFragment_topologicallyWellFormed_internal tm T n available layout

/-- Evaluating a complete trace fragment appends its exact gate count,
preserves the primary-wire prefix, and packs the final bounded machine
configuration. -/
theorem evalAux?_traceFragment
    (tm : NTM k) (T n available : ℕ) [NeZero available]
    (layout : InputWires T n available) (x : BitString n)
    (choices : Fin T → Bool) (wires : Array Bool)
    (hsize : wires.size = available)
    (hdata : ∀ j, wires[(layout.data j).val]? = some (x j))
    (hchoices : ∀ j, wires[(layout.choice j).val]? = some (choices j)) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (traceFragment tm T n available layout) wires = some result ∧
        result.size = wires.size + traceFragmentSize tm T n available layout ∧
        (∀ j < wires.size, result[j]? = wires[j]?) ∧
        EncodesConfig tm T (traceOutputBase tm T n available layout) result
          (tm.trace T choices (tm.initCfg x.toList)) :=
  evalAux?_traceFragment_internal tm T n available layout x choices wires
    hsize hdata hchoices

/-- The complete bounded trace has a machine-dependent cubic gate count in
the trace horizon. -/
theorem traceFragmentSize_le (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    traceFragmentSize tm T n available layout ≤
      traceSizeCoeff tm * (T + 2) ^ 3 :=
  traceFragmentSize_le_internal tm T n available layout

end CircuitUnrolling

end Complexity
