/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonProbeSerializer.Defs
import Complexitylib.Circuits.BarringtonProbeSerializer.Internal

/-!
# Two-pass Barrington serialization through a bit oracle

This module fixes the complete output of the restartable-probe serializer.
Under the canonical formula-code and depth promises, scanning all `4 ^ fuel`
addresses twice yields the executable Barrington compiler's canonical code
byte-for-byte.
-/

namespace Complexity

/-- Querying every scan-based oracle address reconstructs the fixed optional
schedule exactly. -/
theorem barringtonCompileProbeSlots_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel) :
    barringtonCompileProbeSlots fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      barringtonCompileSlots fuel formula target :=
  barringtonCompileProbeSlots_correct_internal fuel formula bitFuel target
    hheader hbound

/-- Under the depth promise, erasing empty oracle addresses recovers the
executable compiler instruction-for-instruction. -/
theorem barringtonCompileProbeProgram_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileProbeProgram fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      barringtonCompile formula target :=
  barringtonCompileProbeProgram_correct_internal fuel formula bitFuel target
    hheader hbound hdepth

/-- The first oracle scan computes the exact target-independent instruction
count used by the canonical program header. -/
theorem barringtonCompileProbeProgram_length (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    (barringtonCompileProbeProgram fuel
      (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
      bitFuel ⟨0, formula.size⟩ target).length =
        barringtonInstructionCount formula :=
  barringtonCompileProbeProgram_length_internal fuel formula bitFuel target
    hheader hbound hdepth

/-- The complete two-pass oracle serializer emits the exact canonical code of
the executable Barrington compiler. -/
theorem barringtonCompileProbeCode_eq (fuel : ℕ)
    (formula : BoolFormula) (bitFuel : ℕ)
    (target : Equiv.Perm (Fin 5))
    (hheader : formula.size + 1 ≤ bitFuel)
    (hbound : ∀ token ∈ FormulaCode.tokens formula,
      token.codeLength ≤ bitFuel)
    (hdepth : formula.depth ≤ fuel) :
    barringtonCompileProbeCode fuel
        (FormulaCode.BitOracle.ofList (FormulaCode.encode formula))
        bitFuel ⟨0, formula.size⟩ target =
      BPCode.Program.encode (barringtonCompile formula target) :=
  barringtonCompileProbeCode_correct_internal fuel formula bitFuel target
    hheader hbound hdepth

end Complexity
