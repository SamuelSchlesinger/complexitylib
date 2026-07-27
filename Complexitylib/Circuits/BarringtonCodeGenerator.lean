/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonCodeGenerator.Defs
public import Complexitylib.Circuits.BarringtonCodeGenerator.Internal

/-!
# Bitstring-level Barrington code generator

`barringtonCompileCode` is the exact total function targeted by the remaining
uniformity proof. On a canonical postfix formula code it emits the canonical
code of `barringtonCompile formula barringtonTargetBase`; malformed inputs map
to the empty string.

This module proves the complete extensional specification independently of a
machine implementation: output decoding recovers the executable program, its
evaluation matches the source formula, and its instruction count is at most
`4 ^ depth`. The next layer must realize this particular function in `FL`.

## Main results

- `barringtonCompileCode_encode` -- exact generated bits.
- `decode?_barringtonCompileCode_encode` -- generated-code round trip.
- `length_barringtonCompileCode_encode_le` -- serialized output-size bound.
- `barringtonCompileCode_spec` -- decoded semantics and Barrington length bound.
-/

@[expose] public section

namespace Complexity

/-- Every variable referenced by a formula is at most its canonical code
length. -/
theorem formula_variable_le_code_length
    (formula : BoolFormula) (index : ℕ) (hindex : index ∈ formula.vars) :
    index ≤ (FormulaCode.encode formula).length :=
  formula_variable_le_code_length_internal formula index hindex

/-- On canonical formula input, the generator emits exactly the canonical
encoding of the executable Barrington compiler's result. -/
@[simp] theorem barringtonCompileCode_encode (formula : BoolFormula) :
    barringtonCompileCode (FormulaCode.encode formula) =
      BPCode.Program.encode
        (barringtonCompile formula barringtonTargetBase) :=
  barringtonCompileCode_encode_internal formula

/-- Decoding generated code recovers the executable compiler's program. -/
theorem decode?_barringtonCompileCode_encode
    (formula : BoolFormula) :
    BPCode.Program.decode?
        (barringtonCompileCode (FormulaCode.encode formula)) =
      some (barringtonCompile formula barringtonTargetBase) :=
  decode?_barringtonCompileCode_encode_internal formula

/-- Exact generated-code length on canonical formula input. -/
theorem length_barringtonCompileCode_encode
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length =
      (barringtonCompile formula barringtonTargetBase).length + 1 +
        (((barringtonCompile formula barringtonTargetBase).map
          fun instruction => instruction.var + 15).sum) :=
  length_barringtonCompileCode_encode_internal formula

/-- Serialized generated output is bounded by the Barrington instruction bound
times the source-code length needed for each terminated-unary variable field. -/
theorem length_barringtonCompileCode_encode_le
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length ≤
      4 ^ formula.depth + 1 +
        4 ^ formula.depth * ((FormulaCode.encode formula).length + 15) :=
  length_barringtonCompileCode_encode_le_internal formula

/-- **Bitstring-level constructive Barrington theorem.** Generated code decodes
to a program with exact formula semantics through the fixed nonidentity target
cycle and instruction count at most `4 ^ depth`. -/
theorem barringtonCompileCode_spec (formula : BoolFormula) :
    barringtonTargetBase ≠ 1 ∧
      (∀ assignment,
        BP.eval assignment
          (barringtonCompile formula barringtonTargetBase) =
            if BoolFormula.eval assignment formula then
              barringtonTargetBase else 1) ∧
      (barringtonCompile formula barringtonTargetBase).length ≤
        4 ^ formula.depth ∧
      BPCode.Program.decode?
          (barringtonCompileCode (FormulaCode.encode formula)) =
        some (barringtonCompile formula barringtonTargetBase) :=
  barringtonCompileCode_spec_internal formula

end Complexity
