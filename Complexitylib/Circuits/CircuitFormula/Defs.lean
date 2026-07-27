/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.AndOrNot.Defs
public import Complexitylib.Circuits.Formula

/-!
# Unfolding fan-in-two circuit outputs into Boolean formulas -- definitions

These definitions recursively unfold the DAG below one selected circuit wire or
output gate. Shared subcircuits are intentionally duplicated in the resulting
formula tree; no formula-size claim is implicit in this bridge.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- Negate a formula exactly when the Boolean edge flag is set. -/
def negateIf (negated : Bool) (formula : BoolFormula) : BoolFormula :=
  if negated then .neg formula else formula

end BoolFormula

namespace Gate

/-- Replace the two inputs of a fan-in-two AND/OR gate by formulas, retaining
the gate operation and its two edge-negation flags. -/
def toBoolFormula {W : ℕ} (gate : Gate Basis.andOr2 W)
    (wireFormula : Fin W → BoolFormula) : BoolFormula :=
  have hfan : gate.fanIn = 2 := fanIn_andOr2 gate
  let input₀ : Fin gate.fanIn := ⟨0, by omega⟩
  let input₁ : Fin gate.fanIn := ⟨1, by omega⟩
  let formula₀ := BoolFormula.negateIf (gate.negated input₀)
    (wireFormula (gate.inputs input₀))
  let formula₁ := BoolFormula.negateIf (gate.negated input₁)
    (wireFormula (gate.inputs input₁))
  match gate.op with
  | .and => .conj formula₀ formula₁
  | .or => .disj formula₀ formula₁

end Gate

namespace Circuit

variable {N M G : ℕ} [NeZero N] [NeZero M]

/-- Recursively unfold the fan-in-two circuit DAG below wire `wire` into a
Boolean formula over the primary-input indices. -/
def wireFormula (circuit : Circuit Basis.andOr2 N M G)
    (wire : Fin (N + G)) : BoolFormula :=
  if hinput : wire.val < N then
    .var wire.val
  else
    have hgate : wire.val - N < G := by omega
    let gate := circuit.gates ⟨wire.val - N, hgate⟩
    have hfan : gate.fanIn = 2 := fanIn_andOr2 gate
    let input₀ : Fin gate.fanIn := ⟨0, by omega⟩
    let input₁ : Fin gate.fanIn := ⟨1, by omega⟩
    let formula₀ := BoolFormula.negateIf (gate.negated input₀)
      (circuit.wireFormula (gate.inputs input₀))
    let formula₁ := BoolFormula.negateIf (gate.negated input₁)
      (circuit.wireFormula (gate.inputs input₁))
    match gate.op with
    | .and => .conj formula₀ formula₁
    | .or => .disj formula₀ formula₁
termination_by wire.val
decreasing_by
  all_goals
    have hacyclic₀ :=
      circuit.acyclic ⟨wire.val - N, hgate⟩ input₀
    have hacyclic₁ :=
      circuit.acyclic ⟨wire.val - N, hgate⟩ input₁
    simp only [gate, input₀, input₁] at hacyclic₀ hacyclic₁ ⊢
    omega

/-- Unfold one selected output gate into a Boolean formula. -/
def outputFormula (circuit : Circuit Basis.andOr2 N M G)
    (output : Fin M) : BoolFormula :=
  (circuit.outputs output).toBoolFormula fun wire => circuit.wireFormula wire

end Circuit

end Complexity
