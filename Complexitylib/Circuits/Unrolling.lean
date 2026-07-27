/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Defs
public import Complexitylib.Circuits.Unrolling.Acceptance
public import Complexitylib.Circuits.Unrolling.Acceptance.Hardwiring
public import Complexitylib.Circuits.Unrolling.Amplification
public import Complexitylib.Circuits.Unrolling.Internal.Initialization
public import Complexitylib.Circuits.Unrolling.Trace
public import Complexitylib.Circuits.Unrolling.Transition
public import Complexitylib.Circuits.Unrolling.Transition.Fragment

/-!
# Circuit unrolling for bounded Turing-machine traces

This module exposes the auditable wire layout, initialization layer, packed
one-step transition compiler, and complete bounded-trace tiling for
nondeterministic Turing machines. The tiled fragment has exact evaluation and
topology laws together with a machine-dependent cubic size bound. A final gate
selects the exact halt-and-output acceptance predicate, and the resulting raw
code reconstructs to a typed single-output circuit. Parallel copies can share
the data input, consume disjoint choice blocks, and feed a strict-majority
threshold with an explicit polynomial gate bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

open CircuitCode

/-- The canonical atom list has exactly one entry for every wire in a
configuration block. -/
@[simp] theorem length_configAtoms (tm : NTM k) (T : ℕ) :
    (configAtoms tm T).length = configWidth tm T :=
  length_configAtoms_internal tm T

/-- Looking up an atom at its explicit index in the canonical ordering
recovers that atom. -/
theorem getElem_configAtoms_configIndex (tm : NTM k) (T : ℕ)
    (atom : ConfigAtom tm T) :
    (configAtoms tm T)[configIndex tm T atom]'(by
      simpa using configIndex_lt tm T atom) = atom :=
  getElem_configAtoms_configIndex_internal tm T atom

/-- Initialization emits exactly one raw gate per configuration atom. -/
@[simp] theorem length_initFragment (tm : NTM k) (T n available : ℕ)
    (layout : InputWires T n available) :
    (initFragment tm T n available layout).length = configWidth tm T :=
  length_initFragment_internal tm T n available layout

/-- Every gate of the initialization fragment refers to an existing input
wire, hence the fragment is topologically well formed at its prefix. -/
theorem initFragment_topologicallyWellFormed (tm : NTM k)
    (T n available : ℕ) [NeZero available] (layout : InputWires T n available) :
    (initFragment tm T n available layout).TopologicallyWellFormed available :=
  initFragment_topologicallyWellFormed_internal tm T n available layout

/-- Evaluating any list of one-gate initialization sources appends exactly
their values, preserves the existing prefix, and records each emitted value
at its consecutive output wire. -/
theorem evalAux?_sourceGates (available : ℕ) [NeZero available]
    (sources : List (InitSource available)) (assignment : Fin available → Bool)
    (wires : Array Bool) (hsize : wires.size = available)
    (hinput : ∀ i, wires[i.val]? = some (assignment i)) :
    ∃ result,
      RawCircuit.evalAux? (sources.map InitSource.gate) wires = some result ∧
        result.size = wires.size + sources.length ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        (∀ (j : ℕ) (hj : j < sources.length),
          result[available + j]? = some ((sources[j]'hj).value assignment)) :=
  evalAux?_sourceGates_internal available sources assignment wires hsize hinput

/-- Initialization appends one atom wire per configuration proposition,
preserves the complete existing prefix, and encodes the machine's initial
configuration. Choice wires may occur in the prefix but are not inspected. -/
theorem evalAux?_initFragment (tm : NTM k) (T n available : ℕ)
    [NeZero available] (layout : InputWires T n available) {wires : Array Bool}
    (hsize : wires.size = available) (x : BitString n)
    (hx : ∀ i, wires[(layout.data i).val]? = some (x i)) :
    ∃ result,
      RawCircuit.evalAux? (initFragment tm T n available layout) wires = some result ∧
        result.size = wires.size + configWidth tm T ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        EncodesConfig tm T available result (tm.initCfg x.toList) :=
  evalAux?_initFragment_internal tm T n available layout hsize x hx

end CircuitUnrolling

end Complexity
