/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.BarringtonUniform.Defs
import Complexitylib.Classes.L.PolynomialTime

/-!
# Uniform Barrington classes -- proof internals
-/

namespace Complexity

/-- Internal forgetful containment for uniform formula families. -/
theorem uniformFormulaNC1_subset_formulaNC1_internal :
    UniformFormulaNC1 ⊆ FormulaNC1 := by
  rintro function ⟨family, hdepth, _huniform, hcomputes⟩
  exact ⟨family, hdepth, hcomputes⟩

/-- Internal forgetful containment for uniform branching-program families. -/
theorem uniformWidth5BP_subset_width5BP_internal :
    UniformWidth5BP ⊆ Width5BP := by
  rintro function ⟨family, point, hlength, _huniform, hdecides⟩
  exact ⟨family, point, hlength, hdecides⟩

/-- Internal polynomial bound for the canonical codes emitted by a uniform
formula family. -/
theorem FormulaFamily.Uniform.code_polynomial_length_internal
    {family : FormulaFamily} (huniform : family.Uniform) :
    ∃ p : Polynomial ℕ, ∀ n,
      (FormulaCode.encode (family n)).length ≤ p.eval n := by
  obtain ⟨generator, hgenerator, hcorrect⟩ := huniform
  obtain ⟨p, hp⟩ := mem_FL_polynomial_output_length hgenerator
  refine ⟨p, fun n => ?_⟩
  rw [← hcorrect n]
  simpa only [unaryList, List.length_replicate] using
    hp (unaryList n)

/-- Internal polynomial-length theorem for the concrete compiled family. -/
theorem FormulaFamily.barringtonProgram_polynomialLength_internal
    (family : FormulaFamily) (hdepth : family.LogDepth) :
    family.barringtonProgram.PolynomialLength := by
  obtain ⟨constant, hconstant⟩ := hdepth
  refine ⟨4 ^ constant, 2 * constant, fun n => ?_⟩
  calc
    (family.barringtonProgram n).length ≤ 4 ^ (family n).depth :=
      barringtonCompile_length_le (family n) barringtonTargetBase
    _ ≤ 4 ^ (constant * Nat.log 2 n + constant) :=
      Nat.pow_le_pow_right (by omega) (hconstant n)
    _ ≤ 4 ^ constant * (n + 1) ^ (2 * constant) :=
      pow4_poly constant n

/-- Internal polynomial bound for the complete canonical code of the concrete
compiled family. Unlike instruction-count polynomiality, this also accounts
for the terminated-unary variable fields. -/
theorem FormulaFamily.barringtonProgram_code_polynomial_length_internal
    (family : FormulaFamily) (hdepth : family.LogDepth)
    (huniform : family.Uniform) :
    ∃ p : Polynomial ℕ, ∀ n,
      (BPCode.Program.encode (family.barringtonProgram n)).length ≤
        p.eval n := by
  obtain ⟨constant, hconstant⟩ := hdepth
  obtain ⟨codePolynomial, hcode⟩ :=
    huniform.code_polynomial_length_internal
  let constructionBound : Polynomial ℕ :=
    Polynomial.C (4 ^ constant) *
      (Polynomial.X + 1) ^ (2 * constant)
  let outputPolynomial : Polynomial ℕ :=
    constructionBound + 1 +
      constructionBound * (codePolynomial + 15)
  refine ⟨outputPolynomial, fun n => ?_⟩
  have hconstruction :
      4 ^ (family n).depth ≤
        4 ^ constant * (n + 1) ^ (2 * constant) := by
    calc
      4 ^ (family n).depth ≤
          4 ^ (constant * Nat.log 2 n + constant) :=
        Nat.pow_le_pow_right (by omega) (hconstant n)
      _ ≤ 4 ^ constant * (n + 1) ^ (2 * constant) :=
        pow4_poly constant n
  calc
    (BPCode.Program.encode (family.barringtonProgram n)).length =
        (barringtonCompileCode
          (FormulaCode.encode (family n))).length := by
      rw [barringtonCompileCode_encode]
      rfl
    _ ≤ 4 ^ (family n).depth + 1 +
          4 ^ (family n).depth *
            ((FormulaCode.encode (family n)).length + 15) :=
      length_barringtonCompileCode_encode_le (family n)
    _ ≤ 4 ^ constant * (n + 1) ^ (2 * constant) + 1 +
          (4 ^ constant * (n + 1) ^ (2 * constant)) *
            (codePolynomial.eval n + 15) := by
      gcongr
      exact hcode n
    _ = outputPolynomial.eval n := by
      simp [outputPolynomial, constructionBound]

/-- Internal logarithmic-width bound for an index into the concrete compiled
program code. -/
theorem FormulaFamily.barringtonProgram_code_index_width_log_internal
    (family : FormulaFamily) (hdepth : family.LogDepth)
    (huniform : family.Uniform) :
    (fun n =>
      (BPCode.Program.encode (family.barringtonProgram n)).length.size) =O
        (fun n => Nat.log 2 n) := by
  obtain ⟨p, hp⟩ :=
    family.barringtonProgram_code_polynomial_length_internal hdepth huniform
  exact BigO.natSize_of_pow (BigO.of_polynomial_bound p hp)

/-- Internal exact decision semantics of the concrete compiled family. -/
theorem FormulaFamily.barringtonProgram_decides_internal
    (family : FormulaFamily) :
    family.barringtonProgram.Decides (fun _ => 0)
      (fun n assignment => BoolFormula.eval assignment (family n)) := by
  intro n assignment
  change BP.eval assignment
      (barringtonCompile (family n) barringtonTargetBase) 0 ≠ 0 ↔
    BoolFormula.eval assignment (family n) = true
  rw [(barringtonCompile_computes (family n) barringtonTargetBase
    barringtonTargetBase_spec.1 barringtonTargetBase_spec.2) assignment]
  cases heval : BoolFormula.eval assignment (family n) <;>
    simp [heval, barringtonTargetBase_moves_zero]

/-- Internal decision theorem after identifying the formula family's semantic
function. -/
theorem FormulaFamily.barringtonProgram_decides_of_computes_internal
    {family : FormulaFamily} {function : ℕ → (ℕ → Bool) → Bool}
    (hcomputes : family.Computes function) :
    family.barringtonProgram.Decides (fun _ => 0) function := by
  intro n assignment
  simpa only [hcomputes n assignment] using
    family.barringtonProgram_decides_internal n assignment

/-- Internal reduction of uniform Barrington's forward direction to the one
named compilation-uniformity obligation. -/
theorem uniformFormulaNC1_subset_uniformWidth5BP_of_compilation_internal
    (hcompilation : UniformBarringtonCompilation) :
    UniformFormulaNC1 ⊆ UniformWidth5BP := by
  rintro function ⟨family, hdepth, huniform, hcomputes⟩
  refine ⟨family.barringtonProgram, fun _ => 0,
    family.barringtonProgram_polynomialLength_internal hdepth,
    hcompilation family hdepth huniform,
    family.barringtonProgram_decides_of_computes_internal hcomputes⟩

end Complexity
