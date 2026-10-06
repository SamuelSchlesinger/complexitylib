/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot
public import Complexitylib.Circuits.XOR
public import Complexitylib.Circuits.Internal.SchnorrBridge
import Complexitylib.Circuits.StraightLine
import Complexitylib.Algebraic.LowerBound.GateElimination.DeMorganXor

/-! # Schnorr's Lower Bound for XOR Circuits

Any fan-in-2 AND/OR circuit computing the N-input XOR function (or its
complement) requires at least `3(N − 1)` gates (`parity_size_ge_three_mul`),
improving the two-gate-elimination bound `2N − 1` (`schnorr_lower_bound_circuit`).

The `2N − 1` bound proceeds by induction on `N`:
1. **Restrict** one input variable, reducing to XOR on `N − 1` inputs.
2. **Eliminate** two gates that become redundant after restriction.
3. Apply the inductive hypothesis to the smaller circuit.

The `3(N − 1)` bound (`parity_size_ge_three_mul`) translates a typed
`Circuit Basis.andOr2 N 1 G` into a straight-line De Morgan circuit whose
charged binary gate count (`Algebraic.DeMorgan.binaryCost`) equals `c.size`,
and applies the three-gate elimination theorem `Algebraic.GateElimination.Xor.lowerBound`
with `Algebraic.DeMorgan.xorThreeGateEliminator`.

## Definitions (from `Complexitylib.Circuits.XOR`)

* `Schnorr.xorBool N x` — the N-input XOR (parity) function

## Main results

* `schnorr_lower_bound_circuit` — `2 * N - 1 ≤ c.size`
* `parity_size_ge_three_mul` — `3 * (N - 1) ≤ c.size`
* `sizeComplexity_xorBool_ge` —
  `Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1`
* `sizeComplexity_xorBool_ge_three_mul` —
  `3 * (N - 1) ≤ Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N)`
-/


public section

namespace Complexity

/-- **Schnorr's lower bound for circuits**: any fan-in-two AND/OR circuit
computing `N`-input parity or its complement has at least `2(N - 1)` internal
gates. Equivalently, its total size is at least `2N - 1`. -/
theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
    2 * N - 1 ≤ c.size := by
  have hbound :=
    schnorr_lower_bound_circuit_internal N G c comp heval (NeZero.pos N)
  simp only [Circuit.size]
  omega

/-- **Schnorr lower bound in terms of `sizeComplexity`**: the fan-in-2
    AND/OR circuit complexity of N-input XOR is at least `2N − 1`. -/
theorem sizeComplexity_xorBool_ge (N : Nat) [NeZero N] :
    Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) ≥ 2 * N - 1 := by
  by_contra hlt; push Not at hlt
  obtain ⟨G, c, hs, hc⟩ := Circuit.sizeComplexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  have hbound := schnorr_lower_bound_circuit N G c false heval
  rw [hs] at hbound
  omega

private structure AndOr2ToDeMorgan {N s : Nat}
    (p : Cslib.Circuits.Program Basis.andOr2.signature N s) where
  gateCount : Nat
  result : Cslib.Circuits.Program Algebraic.DeMorgan.signature N gateCount
  wireMap : Cslib.Circuits.Wire N s → Cslib.Circuits.Wire N gateCount
  trace_eq : ∀ (x : BitString N) (w : Cslib.Circuits.Wire N s),
    result.trace Algebraic.DeMorgan.interpretation x (wireMap w) =
      p.trace Basis.andOr2.interpretation x w
  cost_eq : result.cost Algebraic.DeMorgan.binaryCost = s

private def andOr2ToDeMorgan {N s : Nat} :
    (p : Cslib.Circuits.Program Basis.andOr2.signature N s) → AndOr2ToDeMorgan p
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
    let ih := andOr2ToDeMorgan p₀
    let bop : Algebraic.DeMorgan.BinaryOp :=
      match op with | .and => .and | .or => .or
    let left : Algebraic.DeMorgan.ResidualValue N ih.gateCount :=
      .wire (negated 0) (ih.wireMap (wires 0))
    let right : Algebraic.DeMorgan.ResidualValue N ih.gateCount :=
      .wire (negated 1) (ih.wireMap (wires 1))
    let ret := Algebraic.DeMorgan.retainGate ih.result bop left right
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
        cases op <;>
          (simp [bop, Algebraic.DeMorgan.BinaryOp.eval, Cslib.Circuits.Line.eval,
            Basis.interpretation, Basis.andOr2, AndOrOp.eval_two_and,
            AndOrOp.eval_two_or, Cslib.Circuits.Program.trace]; rfl)
      · simp only [Fin.lastCases_castSucc]
        rw [ret.embedding_eq, ih.trace_eq]
        exact (Cslib.Circuits.Program.trace_gate_castSucc p₀ _
          Basis.andOr2.interpretation x (.gate j₀)).symm

private theorem xorBool_eq_parity :
    ∀ (N : Nat) (x : BitString N),
      Schnorr.xorBool N x = Algebraic.GateElimination.Xor.parity x
  | 0, _ => rfl
  | n + 1, x => by
    rw [Schnorr.xorBool, xorBool_eq_parity n (x ∘ Fin.succ)]
    unfold Algebraic.GateElimination.Xor.parity
    rw [Fin.sum_univ_succ]
    change (x 0).xor (∑ i : Fin n, x i.succ) = x 0 + ∑ i : Fin n, x i.succ
    cases x 0 <;> cases (∑ i : Fin n, x i.succ) <;> rfl

/-- **Schnorr's `3(N - 1)` lower bound for parity circuits**: any fan-in-two
AND/OR circuit computing `N`-input parity or its complement has total size at
least `3(N - 1)`. -/
theorem parity_size_ge_three_mul (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x)) :
    3 * (N - 1) ≤ c.size := by
  let sl := c.toStraightLine
  let tr := andOr2ToDeMorgan sl.program
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

/-- **The `3(N - 1)` parity lower bound in terms of `sizeComplexity`**: the
fan-in-two AND/OR circuit size complexity of `N`-input XOR is at least
`3(N - 1)`. -/
theorem sizeComplexity_xorBool_ge_three_mul (N : Nat) [NeZero N] :
    3 * (N - 1) ≤ Circuit.sizeComplexity Basis.andOr2 (Schnorr.xorBool N) := by
  obtain ⟨G, c, hs, hc⟩ := Circuit.sizeComplexity_witness (B := Basis.andOr2)
    (Schnorr.xorBool N)
  have heval : ∀ x, (c.eval x) 0 = false.xor (Schnorr.xorBool N x) := by
    intro x; simp [congr_fun hc x]
  rw [← hs]
  exact parity_size_ge_three_mul N G c false heval

end Complexity
