/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Defs
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.ArrayEvaluation
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Evaluation
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Size
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Topology

/-!
# Packed circuit fragments for one Turing-machine transition

This module exposes an appendable raw circuit that evaluates every next-atom
formula and packs the results into a contiguous successor-configuration block.
The fragment preserves its input prefix, is topologically well formed, and has
machine-dependent quadratic size in the trace horizon.

## Main results

- `length_stepFragment`: exact fragment gate count.
- `stepFragment_topologicallyWellFormed`: all references point backward.
- `evalAux?_stepFragment`: exact packed successor-configuration semantics.
- `stepFragmentSize_le`: a machine-dependent quadratic size bound.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- The canonical next-formula list has one formula per configuration atom. -/
@[simp] theorem length_stepFormulas (tm : NTM k) (T configBase choiceWire : ℕ) :
    (stepFormulas tm T configBase choiceWire).length = configWidth tm T :=
  length_stepFormulas_internal tm T configBase choiceWire

/-- Looking up the canonical next-formula list by an atom's explicit index
recovers that atom's transition formula. -/
theorem getElem_stepFormulas_configIndex (tm : NTM k)
    (T configBase choiceWire : ℕ) (atom : ConfigAtom tm T) :
    (stepFormulas tm T configBase choiceWire)[configIndex tm T atom]'(by
      rw [length_stepFormulas]
      exact configIndex_lt tm T atom) =
        nextFormula tm T configBase choiceWire atom :=
  getElem_stepFormulas_configIndex_internal tm T configBase choiceWire atom

/-- A packed one-step fragment emits exactly its named gate count. -/
@[simp] theorem length_stepFragment (tm : NTM k)
    (T configBase choiceWire available : ℕ) :
    (stepFragment tm T configBase choiceWire available).length =
      stepFragmentSize tm T configBase choiceWire :=
  length_stepFragment_internal tm T configBase choiceWire available

/-- Packed atom addresses are exactly configuration-wire addresses based at
the packed successor block. -/
@[simp] theorem configWire_stepOutputBase (tm : NTM k)
    (T configBase choiceWire available : ℕ) (atom : ConfigAtom tm T) :
    configWire tm T (stepOutputBase tm T configBase choiceWire available) atom =
      stepOutputBase tm T configBase choiceWire available + configIndex tm T atom :=
  configWire_stepOutputBase_internal tm T configBase choiceWire available atom

/-- The packed successor block ends exactly at the end of the emitted fragment,
so it can serve as the incoming block of the next unrolled step. -/
theorem stepOutputEnd_eq (tm : NTM k)
    (T configBase choiceWire available : ℕ) :
    stepOutputBase tm T configBase choiceWire available + configWidth tm T =
      available + stepFragmentSize tm T configBase choiceWire :=
  stepOutputEnd_eq_internal tm T configBase choiceWire available

/-- A packed step is topologically well formed when its choice wire and
incoming configuration block lie in the existing prefix. -/
theorem stepFragment_topologicallyWellFormed (tm : NTM k)
    (T configBase choiceWire available : ℕ) [NeZero available]
    (hchoice : choiceWire < available)
    (hconfig : configBase + configWidth tm T ≤ available) :
    (stepFragment tm T configBase choiceWire available).TopologicallyWellFormed
      available :=
  stepFragment_topologicallyWellFormed_internal tm T configBase choiceWire
    available hchoice hconfig

/-- Evaluating a packed step appends its exact gate count, preserves the input
prefix, and packs an encoding of the selected successor configuration. -/
theorem evalAux?_stepFragment
    (tm : NTM k) (T configBase choiceWire available : ℕ) [NeZero available]
    (choice : Bool) (assignment : ℕ → Bool) (wires : Array Bool)
    (c : Cfg k tm.Q) (hsize : wires.size = available)
    (hinput : ∀ i < available, wires[i]? = some (assignment i))
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ atom,
      assignment (configWire tm T configBase atom) = atom.value c)
    (hchoiceBound : choiceWire < available)
    (hconfigBound : configBase + configWidth tm T ≤ available)
    (hheads : HeadsLt T c) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (stepFragment tm T configBase choiceWire available) wires = some result ∧
        result.size =
          wires.size + stepFragmentSize tm T configBase choiceWire ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        EncodesConfig tm T
          (stepOutputBase tm T configBase choiceWire available) result
          (choiceStep tm choice c) :=
  evalAux?_stepFragment_internal tm T configBase choiceWire available choice
    assignment wires c hsize hinput hchoice hconfig hchoiceBound hconfigBound hheads

/-- Evaluate a packed step directly from an encoded configuration and the
concrete value stored at its choice wire. -/
theorem evalAux?_stepFragment_of_encodes
    (tm : NTM k) (T configBase choiceWire available : ℕ) [NeZero available]
    (choice : Bool) (wires : Array Bool) (c : Cfg k tm.Q)
    (hsize : wires.size = available)
    (hchoice : wires[choiceWire]? = some choice)
    (hconfig : EncodesConfig tm T configBase wires c)
    (hchoiceBound : choiceWire < available)
    (hconfigBound : configBase + configWidth tm T ≤ available)
    (hheads : HeadsLt T c) :
    ∃ result,
      CircuitCode.RawCircuit.evalAux?
          (stepFragment tm T configBase choiceWire available) wires = some result ∧
        result.size =
          wires.size + stepFragmentSize tm T configBase choiceWire ∧
        (∀ i < wires.size, result[i]? = wires[i]?) ∧
        EncodesConfig tm T
          (stepOutputBase tm T configBase choiceWire available) result
          (choiceStep tm choice c) :=
  evalAux?_stepFragment_of_encodes_internal tm T configBase choiceWire available
    choice wires c hsize hchoice hconfig hchoiceBound hconfigBound hheads

/-- The exact packed one-step gate count is quadratic in the trace horizon,
with a coefficient depending only on the fixed machine. -/
theorem stepFragmentSize_le (tm : NTM k) (T configBase choiceWire : ℕ) :
    stepFragmentSize tm T configBase choiceWire ≤
      stepSizeCoeff tm * (T + 2) ^ 2 :=
  stepFragmentSize_le_internal tm T configBase choiceWire

/-- A bounded configuration block has width linear in the trace horizon. -/
theorem configWidth_le (tm : NTM k) (T : ℕ) :
    configWidth tm T ≤
      (Fintype.card tm.Q + 5 * (k + 2)) * (T + 2) :=
  configWidth_le_explicit_internal tm T

end CircuitUnrolling

end Complexity
