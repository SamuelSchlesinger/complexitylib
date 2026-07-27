/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Internal.Structure
public import Complexitylib.Circuits.Unrolling.Transition.Internal.Semantics
public import Complexitylib.Circuits.Unrolling.Transition.Internal.Support

/-!
# Evaluation of packed one-step circuit fragments

This internal module lifts the semantics of individual transition formulas
through the formula batch compiler. The packed outputs form a fresh encoded
configuration block for the halted-or-successor machine configuration.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Internal evaluation theorem for a packed one-step transition fragment. -/
theorem evalAux?_stepFragment_internal
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
          (choiceStep tm choice c) := by
  have hvars :
      ∀ formula ∈ stepFormulas tm T configBase choiceWire,
        ∀ i ∈ formula.vars, i < available := by
    intro formula hformula i hi
    rw [stepFormulas] at hformula
    rcases List.mem_map.mp hformula with ⟨atom, _hatom, rfl⟩
    exact vars_nextFormula_lt_internal tm T configBase choiceWire available atom
      hchoiceBound hconfigBound i hi
  obtain ⟨result, heval, hresultSize, hprefix, houtputs⟩ :=
    BoolFormula.evalAux?_compileRawBatch available
      (stepFormulas tm T configBase choiceWire) assignment wires
      hsize hinput hvars
  refine ⟨result, ?_, ?_, hprefix, ?_⟩
  · simpa [stepFragment] using heval
  · simpa [stepFragmentSize, Nat.add_assoc] using hresultSize
  · intro atom
    let index : Fin (stepFormulas tm T configBase choiceWire).length :=
      ⟨configIndex tm T atom, by
        rw [length_stepFormulas_internal]
        exact configIndex_lt tm T atom⟩
    have houtput := houtputs index
    simp only [List.get_eq_getElem] at houtput
    rw [getElem_stepFormulas_configIndex_internal,
      nextFormula_eval_internal tm T configBase choiceWire atom choice
        assignment c hchoice hconfig hheads] at houtput
    simpa [index, stepOutputBase, configWire] using houtput

end CircuitUnrolling

end Complexity
