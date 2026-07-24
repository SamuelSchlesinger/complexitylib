/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonStreaming.Defs
import Complexitylib.Circuits.BarringtonStreaming.Internal

/-!
# Random-access Barrington instruction streams

`barringtonCompileStream` mirrors the executable Barrington compiler using
only lengths and indexed instruction queries. It never constructs the complete
recursive instruction list. The exactness theorem identifies both its length
and every query with the existing reference compiler.

## Main results

- `barringtonInstructionCount_eq_length` -- target-independent exact length.
- `barringtonCompileStream_length` -- exact instruction count.
- `barringtonCompileStream_instruction?` -- exact indexed instruction query.
-/

namespace Complexity

/-- The target-independent recurrence is the exact compiled-program length. -/
theorem barringtonInstructionCount_eq_length (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) :
    barringtonInstructionCount formula =
      (barringtonCompile formula target).length :=
  barringtonInstructionCount_eq_length_internal formula target

/-- The random-access compiler has exactly the reference program's length. -/
theorem barringtonCompileStream_length (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) :
    (barringtonCompileStream formula target).length =
      (barringtonCompile formula target).length :=
  (barringtonCompileStream_correctFor_internal formula target).1

/-- Every random-access instruction query agrees with the reference compiler. -/
theorem barringtonCompileStream_instruction? (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) (index : ℕ) :
    (barringtonCompileStream formula target).instruction? index =
      (barringtonCompile formula target)[index]? :=
  (barringtonCompileStream_correctFor_internal formula target).2 index

/-- The random-access compiler inherits the textbook instruction bound. -/
theorem barringtonCompileStream_length_le (formula : BoolFormula)
    (target : Equiv.Perm (Fin 5)) :
    (barringtonCompileStream formula target).length ≤ 4 ^ formula.depth := by
  rw [barringtonCompileStream_length]
  exact barringtonCompile_length_le formula target

end Complexity
