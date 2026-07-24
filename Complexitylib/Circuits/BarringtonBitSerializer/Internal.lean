/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonBitQuery
import Complexitylib.Circuits.BarringtonBitSerializer.Defs
import Complexitylib.Circuits.BarringtonSlots

/-!
# Fixed-slot Barrington serialization over encoded formula bits -- internals
-/

namespace Complexity

theorem barringtonCompileBitsSlots_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) :
    barringtonCompileBitsSlots fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      barringtonCompileSlots fuel formula target := by
  apply List.ext_getElem
  · simp [barringtonCompileBitsSlots, barringtonCompileSlots_length]
  · intro slot hbits hslots
    simp only [barringtonCompileBitsSlots, List.length_map,
      List.length_range] at hbits
    simp only [barringtonCompileBitsSlots]
    rw [List.getElem_map]
    simp only [List.getElem_range]
    rw [barringtonCompileBitsSlot?_eq_instruction?]
    simp [BPSlots.instruction?, List.getElem?_eq_getElem hslots]

theorem barringtonCompileBitsProgram_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileBitsProgram fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      barringtonCompile formula target := by
  rw [barringtonCompileBitsProgram,
    barringtonCompileBitsSlots_correct_internal,
    barringtonCompileSlots_filterMap fuel formula target hdepth]

theorem barringtonCompileBitsProgram_length_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileBitsProgram fuel (FormulaCode.encode formula)
      ⟨0, formula.size⟩ target).length =
      barringtonInstructionCount formula := by
  rw [barringtonCompileBitsProgram,
    barringtonCompileBitsSlots_correct_internal]
  exact barringtonCompileSlots_occupiedCount fuel formula target hdepth

theorem barringtonCompileBitsCode_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5))
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileBitsCode fuel (FormulaCode.encode formula)
        ⟨0, formula.size⟩ target =
      BPCode.Program.encode (barringtonCompile formula target) := by
  rw [barringtonCompileBitsCode,
    barringtonCompileBitsProgram_correct_internal fuel formula target hdepth]

end Complexity
