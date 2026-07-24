/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.BarringtonUniform.Defs
import Complexitylib.Classes.BarringtonUniform.Internal

/-!
# Log-space-uniform Barrington families

Formula and width-`5` branching-program families are uniform when an `FL`
transducer emits their canonical member code on unary input. The executable
Barrington compiler gives a concrete program family with one fixed decision
point, exact semantics, and polynomial length for every log-depth source
family.

The only missing forward-uniformity statement is isolated as
`UniformBarringtonCompilation`: the concrete compiled family of a uniform
log-depth formula family is itself uniform. The conditional containment theorem
shows that proving this one machine-level obligation completes the forward
uniform Barrington theorem. No claim is made that the unbounded formula-code
compiler lies in `FL` on arbitrary inputs.

## Main results

- `FormulaFamily.barringtonProgram_polynomialLength` -- explicit polynomial
  length.
- `FormulaFamily.Uniform.code_polynomial_length` -- uniform source codes have
  polynomial length.
- `FormulaFamily.barringtonProgram_code_polynomial_length` -- the complete
  compiled program code, including variable fields, has polynomial length.
- `FormulaFamily.barringtonProgram_code_index_width_log` -- a binary cursor
  into that code is logarithmic-width.
- `FormulaFamily.barringtonProgram_decides` -- exact fixed-point semantics.
- `uniformFormulaNC1_subset_uniformWidth5BP_of_compilation` -- reduction of the
  uniform forward theorem to the named generator obligation.
-/

namespace Complexity

/-- Forgetting formula-family uniformity gives the nonuniform formula class. -/
theorem uniformFormulaNC1_subset_formulaNC1 :
    UniformFormulaNC1 ⊆ FormulaNC1 :=
  uniformFormulaNC1_subset_formulaNC1_internal

/-- Forgetting branching-program uniformity gives the nonuniform class. -/
theorem uniformWidth5BP_subset_width5BP :
    UniformWidth5BP ⊆ Width5BP :=
  uniformWidth5BP_subset_width5BP_internal

namespace FormulaFamily

/-- The canonical codes of a log-space-uniform formula family have polynomial
length in the unary family index. -/
theorem Uniform.code_polynomial_length
    {family : FormulaFamily} (huniform : family.Uniform) :
    ∃ p : Polynomial ℕ, ∀ n,
      (FormulaCode.encode (family n)).length ≤ p.eval n :=
  huniform.code_polynomial_length_internal

/-- A log-depth formula family compiles through the executable construction to
a concrete polynomial-length width-`5` family. -/
theorem barringtonProgram_polynomialLength
    (family : FormulaFamily) (hdepth : family.LogDepth) :
    family.barringtonProgram.PolynomialLength :=
  family.barringtonProgram_polynomialLength_internal hdepth

/-- The full canonical code of the concrete Barrington family has polynomial
length whenever the source family is both log-depth and uniform. This bound
includes the terminated-unary variable indices, not just the number of
instructions. -/
theorem barringtonProgram_code_polynomial_length
    (family : FormulaFamily) (hdepth : family.LogDepth)
    (huniform : family.Uniform) :
    ∃ p : Polynomial ℕ, ∀ n,
      (BPCode.Program.encode (family.barringtonProgram n)).length ≤
        p.eval n :=
  family.barringtonProgram_code_polynomial_length_internal hdepth huniform

/-- A binary cursor into the complete canonical code of the concrete
Barrington family occupies logarithmic space. This is the numeric resource
bound needed by the remaining streaming/recomputation generator. -/
theorem barringtonProgram_code_index_width_log
    (family : FormulaFamily) (hdepth : family.LogDepth)
    (huniform : family.Uniform) :
    (fun n =>
      (BPCode.Program.encode (family.barringtonProgram n)).length.size) =O
        (fun n => Nat.log 2 n) :=
  family.barringtonProgram_code_index_width_log_internal hdepth huniform

/-- The concrete compiled family decides source-formula evaluation by testing
whether the fixed point zero moves. -/
theorem barringtonProgram_decides (family : FormulaFamily) :
    family.barringtonProgram.Decides (fun _ => 0)
      (fun n assignment => BoolFormula.eval assignment (family n)) :=
  family.barringtonProgram_decides_internal

/-- The concrete compiled family decides any function computed by the source
formula family. -/
theorem barringtonProgram_decides_of_computes
    {family : FormulaFamily} {function : ℕ → (ℕ → Bool) → Bool}
    (hcomputes : family.Computes function) :
    family.barringtonProgram.Decides (fun _ => 0) function :=
  family.barringtonProgram_decides_of_computes_internal hcomputes

end FormulaFamily

/-- Once explicit compilation is proved to preserve promised family
uniformity, uniform log-depth formulas are contained in uniform width-`5`
branching programs. -/
theorem uniformFormulaNC1_subset_uniformWidth5BP_of_compilation
    (hcompilation : UniformBarringtonCompilation) :
    UniformFormulaNC1 ⊆ UniformWidth5BP :=
  uniformFormulaNC1_subset_uniformWidth5BP_of_compilation_internal hcompilation

end Complexity
