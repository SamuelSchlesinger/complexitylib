/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.UhligDecoder
public import Complexitylib.Algebraic.MassProduction.Nonuniform.MaskedScatter

/-!
# Shared XOR folds over fixed valid slots

Each request folds its returned point values once. Invalid slots are wired
to false. Compiling arithmetic addition preserves sharing and charges four
De Morgan gates per scalar slot, avoiding formula duplication.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.MaskedXor

/-- One masked XOR fold for each request's point list. -/
noncomputable def circuit (valid : Fin slots → Bool) (requests : Nat) :=
  Circuit.parallelFin requests (fun _ => _)
    (fun request => (UhligCircuit.xorInputCircuit slots).comp
      (DeMorgan.Wiring.circuit (fun slot =>
        if valid slot then (.input (finProdFinEquiv (request, slot)) : DeMorgan.Wiring (requests * slots))
        else .constant false)))

/-- Each output is the Boolean sum over that request's valid point slots. -/
theorem circuit_eval (valid : Fin slots → Bool)
    (input : Fin (requests * slots) → Bool) (request : Fin requests) :
    (circuit valid requests).eval DeMorgan.interpretation input request =
      ∑ slot, if valid slot then input (finProdFinEquiv (request, slot)) else false := by
  rw [circuit, Circuit.eval_parallelFin, Circuit.eval_comp, UhligCircuit.xorInputCircuit_eval,
    DeMorgan.Wiring.circuit_eval]
  apply Finset.sum_congr rfl
  intro slot _
  cases valid slot <;> simp

/-- Exactly four charged gates per padded scalar slot. -/
theorem circuit_cost (valid : Fin slots → Bool) (requests : Nat) :
    (circuit valid requests).cost DeMorgan.standardCost = requests * slots * 4 := by
  rw [circuit, Circuit.cost_parallelFin]
  simp only [Circuit.cost_comp, DeMorgan.Wiring.circuit_cost, UhligCircuit.xorInputCircuit_cost, Nat.zero_add]
  simp [Nat.mul_assoc]

end Algebraic.MassProduction.Nonuniform.MaskedXor
