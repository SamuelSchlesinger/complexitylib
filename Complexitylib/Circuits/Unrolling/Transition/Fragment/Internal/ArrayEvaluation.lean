/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Evaluation

/-!
# Array-level evaluation of packed transition fragments

This internal adapter derives the abstract assignment expected by the formula
compiler directly from the concrete input array. Consequently, clients can
evaluate a packed transition using an encoded configuration and an actual
choice wire, without separately constructing a total Boolean assignment.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Evaluate one packed step directly from a concrete encoded configuration
and choice wire. -/
theorem evalAux?_stepFragment_of_encodes_internal
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
          (choiceStep tm choice c) := by
  let assignment : ℕ → Bool := fun i => (wires[i]?).getD false
  have hinput : ∀ i < available, wires[i]? = some (assignment i) := by
    intro i hi
    have hiwires : i < wires.size := by
      rw [hsize]
      exact hi
    simp [assignment, Array.getElem?_eq_getElem hiwires]
  have hchoiceAssignment : assignment choiceWire = choice := by
    simp [assignment, hchoice]
  have hconfigAssignment : ∀ atom,
      assignment (configWire tm T configBase atom) = atom.value c := by
    intro atom
    simp [assignment, hconfig atom]
  exact evalAux?_stepFragment_internal tm T configBase choiceWire available
    choice assignment wires c hsize hinput hchoiceAssignment hconfigAssignment
    hchoiceBound hconfigBound hheads

end CircuitUnrolling

end Complexity
