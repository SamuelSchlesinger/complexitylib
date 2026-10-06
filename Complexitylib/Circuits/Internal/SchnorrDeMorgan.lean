/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.StraightLine
public import Complexitylib.Algebraic.LowerBound.GateElimination.DeMorganXor

/-!
# Internal: Schnorr's `3(N - 1)` bound via De Morgan gate elimination

This module translates a straight-line `Basis.andOr2` program into a straight-line
De Morgan program (`Algebraic.DeMorgan.signature`) with the same wire values and
whose charged binary-gate cost equals the source gate count. Composing with the
three-gate elimination theorem `Algebraic.GateElimination.Xor.lowerBound` for
`Algebraic.DeMorgan.xorThreeGateEliminator` gives
`parity_size_ge_three_mul_internal`, the proof of the public theorem
`parity_size_ge_three_mul` in `Complexitylib.Circuits.Schnorr`.
-/

public section

namespace Complexity

namespace SchnorrDeMorgan

/-- A De Morgan program simulating a straight-line `Basis.andOr2` program `p`:
every source wire is mapped to a target wire with the same value, and the
target's charged binary-gate cost equals the number of source gates. -/
structure Translation {N s : Nat}
    (p : Cslib.Circuits.Program Basis.andOr2.signature N s) where
  /-- Number of gates in the translated program. -/
  gateCount : Nat
  /-- The translated De Morgan program. -/
  result : Cslib.Circuits.Program Algebraic.DeMorgan.signature N gateCount
  /-- Where each source wire lives in the translated program. -/
  wireMap : Cslib.Circuits.Wire N s → Cslib.Circuits.Wire N gateCount
  /-- Wire values are preserved. -/
  trace_eq : ∀ (x : BitString N) (w : Cslib.Circuits.Wire N s),
    result.trace Algebraic.DeMorgan.interpretation x (wireMap w) =
      p.trace Basis.andOr2.interpretation x w
  /-- Binary-gate cost equals the source gate count. -/
  cost_eq : result.cost Algebraic.DeMorgan.binaryCost = s

/-- The De Morgan binary operation corresponding to an AND/OR operation. -/
def toBinaryOp : AndOrOp → Algebraic.DeMorgan.BinaryOp
  | .and => .and
  | .or => .or

/-- A fan-in-two AND/OR gate and its De Morgan counterpart agree on every pair
of input values. -/
theorem toBinaryOp_eval (op : AndOrOp) (inputs : BitString 2) :
    (toBinaryOp op).eval (inputs 0) (inputs 1) = op.eval 2 inputs := by
  cases op
  · exact (AndOrOp.eval_two_and inputs).symm
  · exact (AndOrOp.eval_two_or inputs).symm

/-- Translate a straight-line `Basis.andOr2` program gate by gate into a De Morgan
program, absorbing input negations into residual wire values. -/
def translate {N s : Nat} :
    (p : Cslib.Circuits.Program Basis.andOr2.signature N s) → Translation p
  | .empty =>
    { gateCount := 0
      result := .empty
      wireMap := id
      trace_eq := fun _ w => by cases w with | input _ => rfl | gate j => exact j.elim0
      cost_eq := rfl }
  | @Cslib.Circuits.Program.gate _ _ s₀ p₀ line => by
    rcases line with ⟨⟨op, fanIn, arityOk, negated⟩, wires⟩
    change fanIn = 2 at arityOk
    subst arityOk
    change Fin 2 → Cslib.Circuits.Wire N s₀ at wires
    let ih := translate p₀
    let left : Algebraic.DeMorgan.ResidualValue N ih.gateCount :=
      .wire (negated 0) (ih.wireMap (wires 0))
    let right : Algebraic.DeMorgan.ResidualValue N ih.gateCount :=
      .wire (negated 1) (ih.wireMap (wires 1))
    let ret := Algebraic.DeMorgan.retainGate ih.result (toBinaryOp op) left right
    refine
      { gateCount := ret.gateCount
        result := ret.result
        wireMap := fun w => match w with
          | .input i => ret.embedding (ih.wireMap (.input i))
          | .gate j => Fin.lastCases ret.output
              (fun j₀ => ret.embedding (ih.wireMap (.gate j₀))) j
        trace_eq := fun x w => ?_
        cost_eq := ret.cost_eq.trans (by rw [ih.cost_eq]) }
    cases w with
    | input i =>
      rw [ret.embedding_eq, ih.trace_eq]
      rfl
    | gate j =>
      refine Fin.lastCases ?_ (fun j₀ => ?_) j
      · simp only [Fin.lastCases_last]
        rw [ret.output_eq, Cslib.Circuits.Program.trace_gateWire,
          Cslib.Circuits.Program.gateFunction_apply,
          Cslib.Circuits.Program.eval_gate_last]
        have hl : left.eval ih.result x =
            (negated 0).xor (p₀.trace Basis.andOr2.interpretation x (wires 0)) := by
          cases h0 : negated 0 <;>
            simp [left, h0, Algebraic.DeMorgan.ResidualValue.eval, ih.trace_eq]
        have hr : right.eval ih.result x =
            (negated 1).xor (p₀.trace Basis.andOr2.interpretation x (wires 1)) := by
          cases h1 : negated 1 <;>
            simp [right, h1, Algebraic.DeMorgan.ResidualValue.eval, ih.trace_eq]
        rw [hl, hr]
        exact toBinaryOp_eval op
          (fun i => (negated i).xor (p₀.trace Basis.andOr2.interpretation x (wires i)))
      · simp only [Fin.lastCases_castSucc]
        rw [ret.embedding_eq, ih.trace_eq]
        exact (Cslib.Circuits.Program.trace_gate_castSucc p₀ _
          Basis.andOr2.interpretation x (.gate j₀)).symm

/-- `Schnorr.xorBool` agrees with the algebraic library's `parity`. -/
theorem xorBool_eq_parity :
    ∀ (N : Nat) (x : BitString N),
      Schnorr.xorBool N x = Algebraic.GateElimination.Xor.parity x
  | 0, _ => rfl
  | n + 1, x => by
    rw [Schnorr.xorBool, xorBool_eq_parity n (x ∘ Fin.succ)]
    unfold Algebraic.GateElimination.Xor.parity
    rw [Fin.sum_univ_succ]
    change (x 0).xor (∑ i : Fin n, x i.succ) = x 0 + ∑ i : Fin n, x i.succ
    cases x 0 <;> cases (∑ i : Fin n, x i.succ) <;> rfl

end SchnorrDeMorgan

open SchnorrDeMorgan in
/-- Internal proof of `parity_size_ge_three_mul`. -/
theorem parity_size_ge_three_mul_internal (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
    3 * (N - 1) ≤ c.size := by
  let sl := c.toStraightLine
  let tr := translate sl.program
  let dm : Cslib.Circuits.Circuit Algebraic.DeMorgan.signature N 1 :=
    { size := tr.gateCount
      program := tr.result
      outputs := fun o => tr.wireMap (sl.outputs o) }
  have hcomp : dm.ComputesWith Algebraic.DeMorgan.interpretation
      (Algebraic.GateElimination.Xor.target ⟨N, comp⟩) := by
    intro x
    funext o
    have ho : o = 0 := Fin.eq_zero o
    subst ho
    change tr.result.trace Algebraic.DeMorgan.interpretation x
      (tr.wireMap (sl.outputs 0)) = _
    rw [tr.trace_eq]
    have hsl : sl.program.trace Basis.andOr2.interpretation x (sl.outputs 0) =
        c.eval x 0 := congrFun (c.eval_toStraightLine x) 0
    rw [hsl, heval x, xorBool_eq_parity]
    unfold Algebraic.GateElimination.Xor.target
    cases comp <;> cases Algebraic.GateElimination.Xor.parity x <;> rfl
  have hlb := Algebraic.GateElimination.Xor.lowerBound
    Algebraic.DeMorgan.xorThreeGateEliminator ⟨N, comp⟩ dm hcomp
  have hcost : dm.cost Algebraic.DeMorgan.binaryCost = c.size :=
    tr.cost_eq.trans c.size_toStraightLine
  simpa [hcost] using hlb

end Complexity
