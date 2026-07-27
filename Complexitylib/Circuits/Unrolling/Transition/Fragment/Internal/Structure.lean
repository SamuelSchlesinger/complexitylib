/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch
public import Complexitylib.Circuits.Unrolling.Internal.Initialization
public import Complexitylib.Circuits.Unrolling.Transition.Fragment.Defs

/-!
# Structural properties of packed one-step circuit fragments

This internal module connects the canonical configuration-atom ordering to
the formula batch compiler. It records the exact formula and gate counts,
formula lookup order, and arithmetic addresses of packed successor atoms.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

/-- Internal exact length of the canonical next-formula ordering. -/
theorem length_stepFormulas_internal (tm : NTM k)
    (T configBase choiceWire : ℕ) :
    (stepFormulas tm T configBase choiceWire).length = configWidth tm T := by
  simp [stepFormulas, length_configAtoms_internal]

/-- Internal lookup law connecting atom indices to next-configuration formulas. -/
theorem getElem_stepFormulas_configIndex_internal (tm : NTM k)
    (T configBase choiceWire : ℕ) (atom : ConfigAtom tm T) :
    (stepFormulas tm T configBase choiceWire)[configIndex tm T atom]'(by
      rw [length_stepFormulas_internal]
      exact configIndex_lt tm T atom) =
        nextFormula tm T configBase choiceWire atom := by
  simp only [stepFormulas, List.getElem_map]
  rw [getElem_configAtoms_configIndex_internal]

/-- Internal exact gate count of a packed one-step fragment. -/
theorem length_stepFragment_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) :
    (stepFragment tm T configBase choiceWire available).length =
      stepFragmentSize tm T configBase choiceWire := by
  simp [stepFragment, stepFragmentSize]

/-- Internal arithmetic description of the packed successor-block base. -/
theorem stepOutputBase_eq_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) :
    stepOutputBase tm T configBase choiceWire available =
      available +
        ((stepFormulas tm T configBase choiceWire).map BoolFormula.size).sum := rfl

/-- Internal absolute address of a packed successor-configuration atom. -/
theorem stepOutputAddress_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) (atom : ConfigAtom tm T) :
    stepOutputBase tm T configBase choiceWire available + configIndex tm T atom =
      available +
          ((stepFormulas tm T configBase choiceWire).map BoolFormula.size).sum +
        configIndex tm T atom := rfl

/-- Internal bridge from packed output addresses to configuration-wire addresses. -/
theorem configWire_stepOutputBase_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) (atom : ConfigAtom tm T) :
    configWire tm T (stepOutputBase tm T configBase choiceWire available) atom =
      stepOutputBase tm T configBase choiceWire available + configIndex tm T atom := rfl

/-- Internal end address of the packed successor-configuration block. -/
theorem stepOutputEnd_eq_internal (tm : NTM k)
    (T configBase choiceWire available : ℕ) :
    stepOutputBase tm T configBase choiceWire available + configWidth tm T =
      available + stepFragmentSize tm T configBase choiceWire := by
  unfold stepOutputBase stepFragmentSize BoolFormula.rawBatchOutputBase
  rw [length_stepFormulas_internal]
  omega

end CircuitUnrolling

end Complexity
