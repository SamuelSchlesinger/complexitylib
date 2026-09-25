/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Parallel

/-!
# Iterating an endomorphism circuit

Sequentially compose a circuit with itself while retaining exact semantics and
cost.  This construction is useful for fixed-round arithmetic algorithms such
as exponentiation and inversion.
-/

@[expose] public section

namespace Algebraic

/-- Left-associated iteration, universe-polymorphic over `Sort`. -/
def _root_.Cslib.Circuits.Circuit.iterateFunction {A : Sort u} (function : A -> A) : Nat -> A -> A
  | 0 => _root_.id
  | steps + 1 => fun input => function (iterateFunction function steps input)

export Cslib.Circuits (Circuit.iterateFunction)

/-- Compose an endomorphism circuit with itself `steps` times. -/
def _root_.Cslib.Circuits.Circuit.iterate
    (circuit : Circuit σ n n) :
    (steps : Nat) -> Circuit σ n n
  | 0 => Circuit.id σ n
  | steps + 1 => circuit.comp (circuit.iterate steps)

export Cslib.Circuits (Circuit.iterate)

/-- Iterating a circuit multiplies its gate count by the round count. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_iterate
    (circuit : Circuit σ n n)
    (steps : Nat) :
    (circuit.iterate steps).size = steps * circuit.size := by
  induction steps with
  | zero => simp [Circuit.iterate]
  | succ steps inductionHypothesis =>
      rw [Circuit.iterate, Cslib.Circuits.Circuit.size_comp, inductionHypothesis,
        Nat.succ_mul]

export Cslib.Circuits (Circuit.size_iterate)

/-- Iterated circuit evaluation is function iteration. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_iterate
    (circuit : Circuit σ n n)
    (steps : Nat)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (circuit.iterate steps).eval interpretation input =
      Circuit.iterateFunction (circuit.eval interpretation) steps input := by
  induction steps with
  | zero =>
      simp [Circuit.iterate, Circuit.iterateFunction]
  | succ steps inductionHypothesis =>
      simp only [Circuit.iterate, Circuit.eval_comp]
      rw [inductionHypothesis]
      rfl

export Cslib.Circuits (Circuit.eval_iterate)

/-- Iterating a circuit multiplies its weighted cost by the round count. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_iterate
    (circuit : Circuit σ n n)
    (steps : Nat)
    (operationCost : OperationCost σ) :
    (circuit.iterate steps).cost operationCost =
      steps * circuit.cost operationCost := by
  induction steps with
  | zero => simp [Circuit.iterate]
  | succ steps inductionHypothesis =>
      rw [Circuit.iterate, Circuit.cost_comp,
        inductionHypothesis, Nat.succ_mul]

export Cslib.Circuits (Circuit.cost_iterate)

end Algebraic
