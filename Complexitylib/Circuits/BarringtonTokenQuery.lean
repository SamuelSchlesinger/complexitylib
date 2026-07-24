/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonTokenQuery.Defs
import Complexitylib.Circuits.BarringtonTokenQuery.Internal

/-!
# Direct Barrington queries over postfix token streams

This module bridges the canonical postfix formula representation to the
fixed-address Barrington query. Binary children are recovered with the
backwards owed-subtree scan, so the recursive controller never reconstructs an
inductive formula or materializes a compiled branching program.

## Main results

- `FormulaCode.postfixBinaryChildren?_tokens` -- exact child splitting.
- `barringtonTokensFirstOccupiedSlot?_eq` -- exact structural first address.
- `barringtonTokensLastOccupiedSlot?_eq` -- exact structural last address.
- `barringtonCompileTokensSlot?_eq_instruction?` -- token-stream queries agree
  with the list-valued fixed-slot compiler.
-/

namespace Complexity

namespace FormulaCode

/-- The postfix splitter recovers the exact canonical children below a binary
root. -/
theorem postfixBinaryChildren?_tokens (left right : BoolFormula) (op : Token) :
    postfixBinaryChildren? (tokens left ++ tokens right ++ [op]) =
      some (tokens left, tokens right) :=
  postfixBinaryChildren?_tokens_internal left right op

end FormulaCode

/-- Token-stream traversal computes the same first occupied address as the
formula-valued recurrence. -/
theorem barringtonTokensFirstOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonTokensFirstOccupiedSlot? fuel (FormulaCode.tokens formula) =
      barringtonFirstOccupiedSlot? fuel formula :=
  (barringtonTokensOccupiedSlots_correct_internal fuel formula).1

/-- Token-stream traversal computes the same last occupied address as the
formula-valued recurrence. -/
theorem barringtonTokensLastOccupiedSlot?_eq (fuel : ℕ)
    (formula : BoolFormula) :
    barringtonTokensLastOccupiedSlot? fuel (FormulaCode.tokens formula) =
      barringtonLastOccupiedSlot? fuel formula :=
  (barringtonTokensOccupiedSlots_correct_internal fuel formula).2

/-- Every direct query over canonical postfix tokens agrees with the
list-valued fixed-address compiler. -/
theorem barringtonCompileTokensSlot?_eq_instruction? (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (slot : ℕ) :
    barringtonCompileTokensSlot? fuel (FormulaCode.tokens formula)
        target slot =
      BPSlots.instruction?
        (barringtonCompileSlots fuel formula target) slot := by
  rw [barringtonCompileTokensSlot?_correct_internal]
  exact barringtonCompileSlot?_correct_internal fuel formula target slot

end Complexity
