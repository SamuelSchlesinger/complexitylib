/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BarringtonCodeGenerator.Defs
public import Complexitylib.Circuits.BarringtonCompiler
public import Complexitylib.Circuits.BranchingProgramEncoding
public import Complexitylib.Circuits.FormulaEncoding

/-!
# Pure Barrington code-generator internals
-/

@[expose] public section

namespace Complexity

/-- Internal bound placing every referenced variable below the formula-code
length. -/
theorem formula_variable_le_code_length_internal
    (formula : BoolFormula) (index : ℕ) (hindex : index ∈ formula.vars) :
    index ≤ (FormulaCode.encode formula).length := by
  induction formula with
  | var sourceIndex =>
      simp only [BoolFormula.vars, Finset.mem_singleton] at hindex
      subst index
      simp [FormulaCode.length_encode, FormulaCode.tokens,
        FormulaCode.Token.codeLength, BoolFormula.size]
      omega
  | tru => simp [BoolFormula.vars] at hindex
  | fls => simp [BoolFormula.vars] at hindex
  | neg formula ih =>
      have hsub : index ≤ (FormulaCode.encode formula).length :=
        ih (by simpa only [BoolFormula.vars] using hindex)
      apply hsub.trans
      simp [FormulaCode.length_encode, FormulaCode.tokens,
        FormulaCode.Token.codeLength, BoolFormula.size]
      omega
  | conj left right ihLeft ihRight =>
      simp only [BoolFormula.vars, Finset.mem_union] at hindex
      rcases hindex with hleft | hright
      · apply (ihLeft hleft).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
      · apply (ihRight hright).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
  | disj left right ihLeft ihRight =>
      simp only [BoolFormula.vars, Finset.mem_union] at hindex
      rcases hindex with hleft | hright
      · apply (ihLeft hleft).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
      · apply (ihRight hright).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega

/-- Internal exact action of the code generator on a canonical formula code. -/
theorem barringtonCompileCode_encode_internal (formula : BoolFormula) :
    barringtonCompileCode (FormulaCode.encode formula) =
      BPCode.Program.encode
        (barringtonCompile formula barringtonTargetBase) := by
  simp [barringtonCompileCode]

/-- Internal decoding theorem for generated program code. -/
theorem decode?_barringtonCompileCode_encode_internal
    (formula : BoolFormula) :
    BPCode.Program.decode?
        (barringtonCompileCode (FormulaCode.encode formula)) =
      some (barringtonCompile formula barringtonTargetBase) := by
  rw [barringtonCompileCode_encode_internal]
  exact BPCode.Program.decode?_encode _

/-- Internal exact output-code length on canonical formula input. -/
theorem length_barringtonCompileCode_encode_internal
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length =
      (barringtonCompile formula barringtonTargetBase).length + 1 +
        (((barringtonCompile formula barringtonTargetBase).map
          fun instruction => instruction.var + 15).sum) := by
  rw [barringtonCompileCode_encode_internal]
  exact BPCode.Program.length_encode _

/-- Internal serialized-output bound in terms of formula-code length and depth.
The extra factor comes from the terminated-unary variable field in each
instruction. -/
theorem length_barringtonCompileCode_encode_le_internal
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length ≤
      4 ^ formula.depth + 1 +
        4 ^ formula.depth * ((FormulaCode.encode formula).length + 15) := by
  let program := barringtonCompile formula barringtonTargetBase
  have hvariables :
      ∀ instruction ∈ program,
        instruction.var ≤ (FormulaCode.encode formula).length := by
    apply barringtonCompile_var_bound
    intro index hindex
    exact formula_variable_le_code_length_internal formula index hindex
  have hprogram :=
    BPCode.Program.length_encode_le program
      (FormulaCode.encode formula).length hvariables
  have hlength : program.length ≤ 4 ^ formula.depth :=
    barringtonCompile_length_le formula barringtonTargetBase
  have hscaled := Nat.mul_le_mul_right
    ((FormulaCode.encode formula).length + 15) hlength
  rw [barringtonCompileCode_encode_internal]
  exact hprogram.trans (by omega)

/-- Internal combined semantic and program-length specification of generated
code on canonical formula input. -/
theorem barringtonCompileCode_spec_internal (formula : BoolFormula) :
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
        some (barringtonCompile formula barringtonTargetBase) := by
  obtain ⟨htarget, hsemantics, hlength⟩ :=
    barringtonCompile_representation formula
  exact ⟨htarget, hsemantics, hlength,
    decode?_barringtonCompileCode_encode_internal formula⟩

end Complexity
