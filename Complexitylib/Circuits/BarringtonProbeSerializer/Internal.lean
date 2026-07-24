/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeQuery
import Complexitylib.Circuits.BarringtonProbeSerializer.Defs
import Complexitylib.Circuits.BarringtonSlots

/-!
# Two-pass Barrington serialization through a bit oracle -- proof internals
-/

namespace Complexity

theorem barringtonCompileProbeSlots_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlots fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      barringtonCompileSlots fuel formula target := by
  apply List.ext_getElem
  · simp [barringtonCompileProbeSlots, barringtonCompileSlots_length]
  · intro slot hprobe hslots
    simp only [barringtonCompileProbeSlots, List.length_map,
      List.length_range] at hprobe
    simp only [barringtonCompileProbeSlots]
    rw [List.getElem_map]
    simp only [List.getElem_range]
    rw [barringtonCompileProbeScannedSlot?_eq_instruction? fuel formula
      bitFuel target slot hheader hbound]
    simp [BPSlots.instruction?, List.getElem?_eq_getElem hslots]

theorem barringtonCompileProbeProgram_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileProbeProgram fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      barringtonCompile formula target := by
  rw [barringtonCompileProbeProgram,
    barringtonCompileProbeSlots_correct_internal fuel formula bitFuel target
      hheader hbound,
    barringtonCompileSlots_filterMap fuel formula target hdepth]

theorem barringtonCompileProbeProgram_length_internal (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileProbeProgram fuel
      (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
      bitFuel ⟨0, formula.size⟩ target).length =
        barringtonInstructionCount formula := by
  rw [barringtonCompileProbeProgram,
    barringtonCompileProbeSlots_correct_internal fuel formula bitFuel target
      hheader hbound]
  exact barringtonCompileSlots_occupiedCount fuel formula target hdepth

theorem barringtonCompileProbeCode_correct_internal (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileProbeCode fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      BPCode.Program.encode (barringtonCompile formula target) := by
  rw [barringtonCompileProbeCode,
    barringtonCompileProbeProgram_correct_internal fuel formula bitFuel
      target hheader hbound hdepth]

end Complexity
