/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.ShannonParameters
public import Complexitylib.Algebraic.MassProduction.Statement

/-!
# Uniform Shannon synthesis

This module packages the standard `O(2^N / N)` Shannon circuit and connects
it to Boolean mass complexity.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace ShannonSynthesis

/-- Reindex a function along an equality of finite input counts. -/
def reindexFunction
    (inputCount : splitInputs = inputs)
    (function : ScalarFunction Bool inputs) :
    ScalarFunction Bool splitInputs :=
  fun input => function (input ∘ Fin.cast inputCount.symm)

/-- Uniform native Shannon circuit for an arbitrary `N`-input Boolean
function. -/
noncomputable def shannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    Circuit DeMorgan.signature inputs
      (synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      1 :=
  (circuit (addressWidth := shannonAddressWidth inputs)
    (dataWidth := shannonDataWidth inputs)
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      |>.castCounts (shannonAddressDataSum inputs inputsLarge) rfl rfl

@[simp] theorem shannonCircuit_eval
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (input : Fin inputs -> Bool) :
    (shannonCircuit inputs inputsLarge function).eval
        DeMorgan.interpretation input 0 = function input := by
  rw [shannonCircuit, Circuit.eval_castCounts]
  simp only [Fin.cast_refl, id_eq]
  rw [circuit_eval]
  unfold reindexFunction
  apply congrArg function
  funext index
  simp [Function.comp_apply]

theorem shannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).ComputesWith
      DeMorgan.interpretation (scalarTarget function) := by
  intro input
  funext output
  have outputZero : output = 0 := Fin.eq_zero output
  subst output
  exact shannonCircuit_eval inputs inputsLarge function input

theorem shannonCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs) :
    (shannonCircuit inputs inputsLarge function).cost
        DeMorgan.standardCost <= 27 * 2 ^ inputs / inputs := by
  rw [shannonCircuit, Circuit.cost_castCounts]
  exact (circuit_cost_le
    (reindexFunction (shannonAddressDataSum inputs inputsLarge) function)).trans
      (shannonCostBound_le inputs inputsLarge)

/-- The concrete independently replicated Shannon circuit. -/
noncomputable def replicatedShannonCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit DeMorgan.signature (copies * inputs)
      (copies * synthesisGateCount
        (reindexFunction (shannonAddressDataSum inputs inputsLarge) function))
      copies :=
  (shannonCircuit inputs inputsLarge function).replicateScalar copies

theorem replicatedShannonCircuit_computes
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    (replicatedShannonCircuit inputs inputsLarge function copies).ComputesWith
      DeMorgan.interpretation (directProduct function copies) := by
  intro input
  rw [replicatedShannonCircuit, Circuit.eval_replicateScalar]
  funext copy
  exact shannonCircuit_eval inputs inputsLarge function
    (directProductInput input copy)

/-- A minimum-cost realization of a finite Boolean direct product, selected
from the nonempty implementation family witnessed by Shannon replication. -/
noncomputable def minimumMassCircuit
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    Circuit.Minimum DeMorgan.standardCost DeMorgan.interpretation
      (directProduct function copies) :=
  Circuit.minimum DeMorgan.standardCost
    (replicatedShannonCircuit inputs inputsLarge function copies)
    DeMorgan.interpretation (directProduct function copies)
    (replicatedShannonCircuit_computes inputs inputsLarge function copies)

/-- The selected minimum circuit realizes `booleanMassComplexity` exactly. -/
theorem minimumMassCircuit_cost_eq_complexity
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies =
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost : ENat) := by
  unfold booleanMassComplexity
  exact Circuit.costComplexity_eq DeMorgan.standardCost
    (minimumMassCircuit inputs inputsLarge function copies).computes
    (minimumMassCircuit inputs inputsLarge function copies).minimal.cost

theorem minimumMassCircuit_cost_le
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies bound : Nat)
    (complexityBound : booleanMassComplexity function copies <=
      (bound : Nat)) :
    (minimumMassCircuit inputs inputsLarge function copies).circuit.cost
        DeMorgan.standardCost <= bound := by
  have castBound :
      ((minimumMassCircuit inputs inputsLarge function copies).circuit.cost
          DeMorgan.standardCost : ENat) <= (bound : Nat) := by
    rw [← minimumMassCircuit_cost_eq_complexity]
    exact complexityBound
  exact_mod_cast castBound

/-- Naive replication of native Shannon synthesis bounds any finite number
of independent copies.  This is the base finite upper bound used before the
mass-production composition improves the dependence on `copies`. -/
theorem booleanMassComplexity_le_replicatedShannon
    (inputs : Nat)
    (inputsLarge : 16 <= inputs)
    (function : ScalarFunction Bool inputs)
    (copies : Nat) :
    booleanMassComplexity function copies <=
      (copies * (27 * 2 ^ inputs / inputs) : Nat) := by
  let base := shannonCircuit inputs inputsLarge function
  let replicated := base.replicateScalar copies
  have computes : replicated.ComputesWith DeMorgan.interpretation
      (directProduct function copies) := by
    intro input
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.eval_replicateScalar]
    funext copy
    exact shannonCircuit_eval inputs inputsLarge function
      (directProductInput input copy)
  have complexityBound := replicated.costComplexity_le
    DeMorgan.standardCost computes
  have finiteBound : replicated.cost DeMorgan.standardCost <=
      copies * (27 * 2 ^ inputs / inputs) := by
    rw [show replicated = base.replicateScalar copies by rfl,
      Circuit.cost_replicateScalar]
    apply Nat.mul_le_mul_left
    exact shannonCircuit_cost_le inputs inputsLarge function
  unfold booleanMassComplexity
  exact complexityBound.trans (by exact_mod_cast finiteBound)

end ShannonSynthesis
end MassProduction
end Algebraic
