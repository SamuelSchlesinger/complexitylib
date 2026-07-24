/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBitSerializer.Defs
import Complexitylib.Circuits.BarringtonBitSerializer.Internal

/-!
# Fixed-slot Barrington serialization over encoded formula bits

This module specifies the exact two-pass stream used by the uniform generator:
query all `4 ^ fuel` fixed addresses, count and erase empty slots, then emit the
canonical branching-program code. Under the promised depth bound, the result
is byte-for-byte the existing executable Barrington compiler's code.

## Main results

- `barringtonCompileBitsSlots_eq` -- querying every fixed address reconstructs
  the fixed optional schedule exactly.
- `barringtonCompileBitsProgram_eq` -- erasing empty queried slots recovers the
  executable Barrington compiler.
- `barringtonCompileBitsProgram_length` -- the first pass computes the exact
  instruction count used by the canonical header.
- `barringtonCompileBitsCode_eq` -- the complete serialized output is exact.
-/

namespace Complexity

/-- Querying all encoded-bit addresses reconstructs the fixed optional schedule
exactly. -/
theorem barringtonCompileBitsSlots_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonCompileBitsSlots fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      barringtonCompileSlots fuel formula target :=
  barringtonCompileBitsSlots_correct_internal fuel formula target

/-- Under the depth promise, erasing empty queried addresses recovers the
executable Barrington compiler instruction-for-instruction. -/
theorem barringtonCompileBitsProgram_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileBitsProgram fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      barringtonCompile formula target :=
  barringtonCompileBitsProgram_correct_internal fuel formula target hdepth

/-- The queried instruction stream has exactly the target-independent count
used by the canonical program header. -/
theorem barringtonCompileBitsProgram_length (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileBitsProgram fuel (FormulaCode.encode formula)
      ⟨0, formula.size⟩ target).length =
      barringtonInstructionCount formula :=
  barringtonCompileBitsProgram_length_internal fuel formula target hdepth

/-- Under the depth promise, the fixed-address two-pass serializer emits the
exact canonical code of the executable Barrington compiler. -/
theorem barringtonCompileBitsCode_eq (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileBitsCode fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      BPCode.Program.encode (barringtonCompile formula target) :=
  barringtonCompileBitsCode_correct_internal fuel formula target hdepth

end Complexity
