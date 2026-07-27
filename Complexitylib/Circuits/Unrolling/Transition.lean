/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Unrolling.Transition.Defs
public import Complexitylib.Circuits.Unrolling.Transition.Internal.Semantics
public import Complexitylib.Circuits.Unrolling.Transition.Internal.Support

/-!
# Boolean formulas for one Turing-machine transition

This module exposes the semantic and variable-support guarantees for the
auditable transition formulas defined in `Transition.Defs`. A formula for one
configuration atom reads only its designated choice bit and the preceding
configuration block, and evaluates to that atom's value after one halted-or-
successor machine step.

## Main results

- `nextFormula_eval`: semantic correctness of every next-atom formula.
- `mem_vars_nextFormula`: exact source family of every referenced variable.
- `vars_nextFormula_lt`: all references lie in a sufficiently large prefix.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- A next-atom formula evaluates to the corresponding atom of the selected
halted-or-successor configuration. -/
theorem nextFormula_eval
    (tm : NTM k) (T base choiceWire : ℕ) (atom : ConfigAtom tm T)
    (choice : Bool) (assignment : ℕ → Bool) (c : Cfg k tm.Q)
    (hchoice : assignment choiceWire = choice)
    (hconfig : ∀ oldAtom,
      assignment (configWire tm T base oldAtom) = oldAtom.value c)
    (hheads : HeadsLt T c) :
    (nextFormula tm T base choiceWire atom).eval assignment =
      atom.value (choiceStep tm choice c) :=
  nextFormula_eval_internal tm T base choiceWire atom choice assignment c
    hchoice hconfig hheads

/-- Every next-atom formula variable is either its choice wire or a wire in
the incoming configuration block. -/
theorem mem_vars_nextFormula (tm : NTM k) (T base choiceWire : ℕ)
    (atom : ConfigAtom tm T) (i : ℕ)
    (hi : i ∈ (nextFormula tm T base choiceWire atom).vars) :
    i = choiceWire ∨
      ∃ oldAtom : ConfigAtom tm T, i = configWire tm T base oldAtom :=
  mem_vars_nextFormula_internal tm T base choiceWire atom i hi

/-- If the choice wire and incoming configuration block lie in a prefix, every
variable of a next-atom formula lies in that prefix. -/
theorem vars_nextFormula_lt (tm : NTM k) (T base choiceWire available : ℕ)
    (atom : ConfigAtom tm T) (hchoice : choiceWire < available)
    (hconfig : base + configWidth tm T ≤ available) :
    ∀ i ∈ (nextFormula tm T base choiceWire atom).vars, i < available :=
  vars_nextFormula_lt_internal tm T base choiceWire available atom hchoice hconfig

end CircuitUnrolling

end Complexity
