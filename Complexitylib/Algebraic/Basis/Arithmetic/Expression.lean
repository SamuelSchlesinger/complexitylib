/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.Arithmetic
public import Complexitylib.Algebraic.Substitution

/-!
# Arithmetic expressions compiled to circuits

This module supplies a small reusable expression language for arithmetic
circuits.  Compilation is tree-shaped: the left subtree is emitted first, the
right subtree is instantiated after it over the same original inputs, and the
root operation is appended last.  The result is a circuit whose bundled
`size` is definitionally the expression gate count.
-/

@[expose] public section

namespace Algebraic
namespace Arithmetic

/-- Tree-shaped arithmetic expressions with named constants. -/
inductive Expression (C : Type u) (n : Nat)
  | input (index : Fin n)
  | constant (value : C)
  | add (left right : Expression C n)
  | mul (left right : Expression C n)

namespace Expression

/-- Number of gates emitted by tree compilation. Inputs are free. -/
@[reducible] def gateCount : Expression C n → Nat
  | .input _ => 0
  | .constant _ => 1
  | .add left right | .mul left right =>
      gateCount left + gateCount right + 1

/-- Weighted number of binary arithmetic nodes.  Constants are free, matching
`Arithmetic.weightedCost`; tree compilation realizes this cost exactly. -/
@[reducible] def weightedCost
    (addition multiplication : Nat) : Expression C n → Nat
  | .input _ | .constant _ => 0
  | .add left right =>
      weightedCost addition multiplication left +
        weightedCost addition multiplication right + addition
  | .mul left right =>
      weightedCost addition multiplication left +
        weightedCost addition multiplication right + multiplication

/-- Number of multiplication nodes in an expression. -/
@[reducible] def multiplicationCount : Expression C n → Nat :=
  weightedCost 0 1

/-- Number of addition nodes in an expression. -/
@[reducible] def additionCount : Expression C n → Nat :=
  weightedCost 1 0

/-- Evaluate an expression in an arbitrary arithmetic carrier. -/
def eval
    [Add R]
    [Mul R]
    (constant : C → R)
    (input : Fin n → R) : Expression C n → R
  | .input index => input index
  | .constant value => constant value
  | .add left right => eval constant input left + eval constant input right
  | .mul left right => eval constant input left * eval constant input right

/-- A compiled expression program together with its result wire. -/
structure Compilation (expression : Expression C n) where
  /-- Emitted straight-line program. -/
  program : Program (Arithmetic.signature C) n expression.gateCount
  /-- Wire carrying the expression value. -/
  output : Wire n expression.gateCount

/-- Compile an arithmetic expression to a straight-line program. -/
def compile : (expression : Expression C n) → Compilation expression
  | .input index =>
      { program := .empty
        output := Wire.input index }
  | .constant value =>
      { program := (Program.empty :
          Program (Arithmetic.signature C) n 0).gate
            { op := .constant value
              wires := fun argument =>
                Fin.elim0 (Fin.cast (Arithmetic.arity_constant (K := C) value)
                  argument) }
        output := Wire.gate (Fin.last 0) }
  | .add left right =>
      let leftCompiled := compile left
      let rightCompiled := compile right
      let inputWires : Fin n → Wire n left.gateCount := Wire.input
      let combined := rightCompiled.program.instantiate leftCompiled.program
        inputWires
      let leftOutput := Wire.Renaming.castAdd right.gateCount
        leftCompiled.output
      let rightOutput := Wire.Substitution.append inputWires right.gateCount
        rightCompiled.output
      { program := combined.gate
          { op := .add
            wires := fun argument =>
              Fin.cases leftOutput (fun _ => rightOutput)
                (Fin.cast (Arithmetic.arity_add (K := C)) argument) }
        output := Wire.gate (Fin.last (left.gateCount + right.gateCount)) }
  | .mul left right =>
      let leftCompiled := compile left
      let rightCompiled := compile right
      let inputWires : Fin n → Wire n left.gateCount := Wire.input
      let combined := rightCompiled.program.instantiate leftCompiled.program
        inputWires
      let leftOutput := Wire.Renaming.castAdd right.gateCount
        leftCompiled.output
      let rightOutput := Wire.Substitution.append inputWires right.gateCount
        rightCompiled.output
      { program := combined.gate
          { op := .mul
            wires := fun argument =>
              Fin.cases leftOutput (fun _ => rightOutput)
                (Fin.cast (Arithmetic.arity_mul (K := C)) argument) }
        output := Wire.gate (Fin.last (left.gateCount + right.gateCount)) }

/-- The one-output circuit emitted for an expression. -/
def circuit (expression : Expression C n) :
    Circuit (Arithmetic.signature C) n 1 where
  program := (compile expression).program
  outputs := fun _ => (compile expression).output

/-- The circuit emitted for an expression has exactly the expression gate count. -/
@[simp] theorem size_circuit (expression : Expression C n) :
    (circuit expression).size = expression.gateCount := rfl

/-- Tree compilation preserves every binary arithmetic weighting exactly. -/
theorem compile_weightedCost
    (addition multiplication : Nat)
    (expression : Expression C n) :
    (compile expression).program.cost
        (Arithmetic.weightedCost addition multiplication) =
      expression.weightedCost addition multiplication := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | add left right leftIH rightIH =>
      simp [compile, weightedCost, leftIH, rightIH,
        Arithmetic.weightedCost]
  | mul left right leftIH rightIH =>
      simp [compile, weightedCost, leftIH, rightIH,
        Arithmetic.weightedCost]

/-- Exact multiplicative complexity of a compiled expression. -/
@[simp] theorem circuit_multiplicationCost
    (expression : Expression C n) :
    (circuit expression).cost (Arithmetic.multiplicationCost (K := C)) =
      expression.multiplicationCount := by
  simpa [circuit, Circuit.cost, multiplicationCount,
    Arithmetic.multiplicationCost] using
      compile_weightedCost 0 1 expression

/-- Exact additive complexity of a compiled expression. -/
@[simp] theorem circuit_additionCost
    (expression : Expression C n) :
    (circuit expression).cost (Arithmetic.additionCost (K := C)) =
      expression.additionCount := by
  simpa [circuit, Circuit.cost, additionCount,
    Arithmetic.additionCost] using
      compile_weightedCost 1 0 expression

/-- Tree compilation preserves expression evaluation. -/
theorem compile_trace
    [Add R]
    [Mul R]
    (constant : C → R)
    (input : Fin n → R)
    (expression : Expression C n) :
    (compile expression).program.trace (Arithmetic.interpretation constant)
        input (compile expression).output =
      expression.eval constant input := by
  induction expression with
  | input index =>
      simp only [compile, eval]
      exact Program.trace_input
        (Program.empty : Program (Arithmetic.signature C) n 0)
        (Arithmetic.interpretation constant) input index
  | constant value =>
      simp only [compile, eval]
      rw [Program.trace_gateWire, Program.gateFunction_gate_last]
      rfl
  | add left right leftIH rightIH =>
      simp only [compile, eval]
      rw [Program.trace_gateWire, Program.gateFunction_gate_last]
      change
        ((compile right).program.instantiate (compile left).program
            Wire.input).trace (Arithmetic.interpretation constant) input
              (Wire.Renaming.castAdd right.gateCount
                (compile left).output) +
          ((compile right).program.instantiate (compile left).program
            Wire.input).trace (Arithmetic.interpretation constant) input
              (Wire.Substitution.append Wire.input right.gateCount
                (compile right).output) = _
      rw [(compile right).program.instantiate_trace_ambient
        (compile left).program Wire.input
        (Arithmetic.interpretation constant) input (compile left).output,
        (compile right).program.instantiate_trace
          (compile left).program Wire.input
          (Arithmetic.interpretation constant) input (compile right).output]
      have inputWires_eval :
          (compile left).program.trace (Arithmetic.interpretation constant)
              input ∘ (Wire.input : Fin n → Wire n left.gateCount) = input := by
        funext index
        exact Program.trace_input (compile left).program
          (Arithmetic.interpretation constant) input index
      rw [leftIH, inputWires_eval, rightIH]
  | mul left right leftIH rightIH =>
      simp only [compile, eval]
      rw [Program.trace_gateWire, Program.gateFunction_gate_last]
      change
        ((compile right).program.instantiate (compile left).program
            Wire.input).trace (Arithmetic.interpretation constant) input
              (Wire.Renaming.castAdd right.gateCount
                (compile left).output) *
          ((compile right).program.instantiate (compile left).program
            Wire.input).trace (Arithmetic.interpretation constant) input
              (Wire.Substitution.append Wire.input right.gateCount
                (compile right).output) = _
      rw [(compile right).program.instantiate_trace_ambient
        (compile left).program Wire.input
        (Arithmetic.interpretation constant) input (compile left).output,
        (compile right).program.instantiate_trace
          (compile left).program Wire.input
          (Arithmetic.interpretation constant) input (compile right).output]
      have inputWires_eval :
          (compile left).program.trace (Arithmetic.interpretation constant)
              input ∘ (Wire.input : Fin n → Wire n left.gateCount) = input := by
        funext index
        exact Program.trace_input (compile left).program
          (Arithmetic.interpretation constant) input index
      rw [leftIH, inputWires_eval, rightIH]

/-- Circuit evaluation of a compiled expression is its direct evaluation. -/
theorem circuit_eval
    [Add R]
    [Mul R]
    (constant : C → R)
    (input : Fin n → R)
    (expression : Expression C n) :
    (circuit expression).eval (Arithmetic.interpretation constant) input 0 =
      expression.eval constant input :=
  compile_trace constant input expression

end Expression
end Arithmetic
end Algebraic
