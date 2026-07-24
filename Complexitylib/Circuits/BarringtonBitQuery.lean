/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBitQuery.Defs
import Complexitylib.Circuits.BarringtonBitQuery.Internal
import Complexitylib.Circuits.BarringtonTokenQuery

/-!
# Direct Barrington queries over canonical formula bits

This module moves the fixed-address Barrington controller from postfix token
lists to their canonical bit encoding. The controller recovers token roots and
child spans through bit-level probes, follows one base-four address, and never
reconstructs the inductive formula or materializes the complete branching
program.

## Main results

- `barringtonBitsFirstOccupiedSlot?_eq` -- encoded traversal finds the exact
  structural first address.
- `barringtonBitsLastOccupiedSlot?_eq` -- encoded traversal finds the exact
  structural last address.
- `barringtonCompileBitsSlot?_eq_instruction?` -- every encoded-bit query
  returns exactly the corresponding fixed-schedule instruction.
-/

namespace Complexity

/-- Traversal over canonical formula bits computes the structural first
occupied Barrington address. -/
theorem barringtonBitsFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonBitsFirstOccupiedSlot? fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ =
      barringtonFirstOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensFirstOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonBitsOccupiedSlots_correct_context_internal fuel [] []
          formula).1
    _ = _ := barringtonTokensFirstOccupiedSlot?_eq fuel formula

/-- Traversal over canonical formula bits computes the structural last
occupied Barrington address. -/
theorem barringtonBitsLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonBitsLastOccupiedSlot? fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ =
      barringtonLastOccupiedSlot? fuel formula := by
  calc
    _ = barringtonTokensLastOccupiedSlot? fuel
        (FormulaCode.tokens formula) := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        (barringtonBitsOccupiedSlots_correct_context_internal fuel [] []
          formula).2
    _ = _ := barringtonTokensLastOccupiedSlot?_eq fuel formula

/-- Every direct query over canonical formula bits agrees with the selected
instruction of the list-valued fixed Barrington schedule. -/
theorem barringtonCompileBitsSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileBitsSlot? fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  calc
    _ = barringtonCompileTokensSlot? fuel (FormulaCode.tokens formula)
        target slot := by
      simpa [FormulaCode.encode, FormulaCode.encodeTokenStream] using
        barringtonCompileBitsSlot?_correct_context_internal fuel [] []
          formula target slot
    _ = _ :=
      barringtonCompileTokensSlot?_eq_instruction? fuel formula target slot

end Complexity
