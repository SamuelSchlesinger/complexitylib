/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Elementary semantics of the signed gate model

Parity commutes with pointwise XOR. The sixteen binary Boolean operations have
arity-preserving signed affine or conjunction normal forms, so the model contains
the full binary basis without increasing gate count.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- Parity of pointwise XOR is the XOR of the two parities. -/
theorem xorSum_xor {r : ℕ} (x y : Fin r → Bool) :
    xorSum (fun i => x i ^^ y i) = (xorSum x ^^ xorSum y) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [xorSum, Fin.tail_def, ih]
    simp only [Bool.xor_assoc, Bool.xor_left_comm]

/-- A binary operation in signed affine/conjunction normal form. -/
def binaryOp (f : Bool → Bool → Bool) : Op :=
  let a := f false false
  let b := f true false
  let c := f false true
  let d := f true true
  if a ^^ b ^^ c ^^ d then
    let p := !(a ^^ c)
    let q := !(a ^^ b)
    .conjunction 2 ![p, q] (a ^^ ((!p) && (!q)))
  else .affine 2 a ![a ^^ b, a ^^ c]

/-- Binary normalization retains both ordered argument slots. -/
@[simp] theorem binaryOp_arity (f : Bool → Bool → Bool) : (binaryOp f).arity = 2 := by
  simp only [binaryOp]
  split <;> rfl

/-- A binary line translated into a single signed gate. -/
def binaryLine {n g : ℕ} (line : Line Binary.signature n g) : Line signature n g :=
  ⟨binaryOp line.op, fun i => line.wires (Fin.cast (binaryOp_arity line.op) i)⟩

/-- Every one-gate binary normalization computes the original truth table. -/
theorem interpretation_binaryOp (f : Bool → Bool → Bool) (x : Fin 2 → Bool) :
    interpretation (binaryOp f) (fun i => x (Fin.cast (binaryOp_arity f) i)) =
      f (x 0) (x 1) := by
  have hf : f = fun a b => if a then (if b then f true true else f true false)
      else (if b then f false true else f false false) := by
    funext a b
    cases a <;> cases b <;> rfl
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  rw [hx, hf]
  generalize f false false = a, f true false = b, f false true = c, f true true = d
  generalize x 0 = u, x 1 = v
  cases a <;> cases b <;> cases c <;> cases d <;> cases u <;> cases v <;> decide

/-- Replace each binary gate by its one-gate signed normal form. -/
def binaryProgram {n : ℕ} : {g : ℕ} → Program Binary.signature n g → Program signature n g
  | _, .empty => .empty
  | _, .gate p line => (binaryProgram p).gate (binaryLine line)

/-- Binary normalization preserves the complete gate trace. -/
theorem eval_binaryProgram {n g : ℕ} (p : Program Binary.signature n g) (x : Fin n → Bool) :
    (binaryProgram p).eval interpretation x = p.eval Binary.interpretation x := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [binaryProgram, Program.eval_gate_last, binaryLine, Line.eval, ih]
      exact interpretation_binaryOp line.op (Wire.elim x (p.eval Binary.interpretation x) ∘
        line.wires)
    · simpa only [binaryProgram, Program.eval_gate_castSucc] using congrFun ih j

/-- Normalize a binary circuit without changing any gate or output index. -/
def binaryCircuit {n m : ℕ} (c : Circuit Binary.signature n m) : Circuit signature n m :=
  ⟨binaryProgram c.program, c.outputs⟩

/-- The translation charges exactly one gate per original binary gate. -/
@[simp] theorem size_binaryCircuit {n m : ℕ} (c : Circuit Binary.signature n m) :
    (binaryCircuit c).size = c.size := rfl

/-- The normalized circuit has identical Boolean outputs. -/
@[simp] theorem eval_binaryCircuit {n m : ℕ} (c : Circuit Binary.signature n m)
    (x : Fin n → Bool) : (binaryCircuit c).eval interpretation x =
      c.eval Binary.interpretation x := by
  simp only [Circuit.eval, binaryCircuit, Program.trace, eval_binaryProgram]

end Algebraic.Aggregate.Geometry
