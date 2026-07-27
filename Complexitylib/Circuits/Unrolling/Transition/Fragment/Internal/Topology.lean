/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Defs
public import Complexitylib.Circuits.Unrolling.Transition.Internal.Support

/-!
# Topology of packed one-step circuit fragments

This internal module proves that a packed transition fragment is
topologically well formed whenever its choice wire and incoming configuration
block lie in the existing circuit prefix.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Internal topological well-formedness of a packed one-step fragment. -/
theorem stepFragment_topologicallyWellFormed_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) [NeZero available]
    (hchoice : choiceWire < available)
    (hconfig : configBase + configWidth tm T ≤ available) :
    (stepFragment tm T configBase choiceWire available).TopologicallyWellFormed
      available := by
  unfold stepFragment
  apply BoolFormula.topologicallyWellFormed_compileRawBatch
  intro formula hformula i hi
  rw [stepFormulas] at hformula
  rcases List.mem_map.mp hformula with ⟨atom, _hatom, rfl⟩
  exact vars_nextFormula_lt_internal tm T configBase choiceWire available atom
    hchoice hconfig i hi

end CircuitUnrolling

end Complexity
