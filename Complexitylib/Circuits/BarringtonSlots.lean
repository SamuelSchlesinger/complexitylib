/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonSlots.Defs
import Complexitylib.Circuits.BarringtonSlots.Internal

/-!
# Fixed-address Barrington compilation slots

`barringtonCompileSlots fuel formula target` schedules the existing compiler
inside exactly `4 ^ fuel` optional slots. Under the promised depth bound,
erasing empty slots recovers the existing compiler exactly. The fixed
four-block address space is the machine-facing traversal used by the uniform
generator.

## Main results

- `barringtonCompileSlots_length` -- the slot count is exactly `4 ^ fuel`.
- `barringtonCompileSlots_filterMap` -- occupied slots are exactly the
  reference compiler output.
- `barringtonCompileSlots_occupiedCount` -- counting occupied slots gives the
  exact instruction-count recurrence.
-/

namespace Complexity

/-- The fixed-address schedule has exactly `4 ^ fuel` slots. -/
theorem barringtonCompileSlots_length (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    (barringtonCompileSlots fuel formula target).length = 4 ^ fuel :=
  barringtonCompileSlots_length_internal fuel formula target

/-- Under its depth promise, erasing empty slots recovers the existing
Barrington compiler exactly. -/
theorem barringtonCompileSlots_filterMap (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileSlots fuel formula target).filterMap id =
      barringtonCompile formula target :=
  barringtonCompileSlots_filterMap_internal fuel formula target hdepth

/-- Counting the occupied slots recovers the exact number of instructions in
the reference compiler output. -/
theorem barringtonCompileSlots_occupiedCount (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    ((barringtonCompileSlots fuel formula target).filterMap id).length =
      barringtonInstructionCount formula :=
  barringtonCompileSlots_occupiedCount_internal fuel formula target hdepth

end Complexity
