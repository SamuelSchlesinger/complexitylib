/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.PointUpdate
public import Complexitylib.Algebraic.Basis.DeMorgan.Completeness
public import Complexitylib.Algebraic.BooleanCube
public import Complexitylib.Algebraic.Complexity

/-!
# Boolean circuit complexity on the truth-table cube

Every Boolean function has a De Morgan circuit. Its minimum internal gate
count is therefore a natural number, agreeing with the generic extended-
natural `Circuit.gateComplexity`. Constants and identities count as gates;
designated output wires remain free.

Changing one truth-table entry costs at most `2 * n` gates. Consequently the
complexity measure is `2 * n` Lipschitz for unnormalized Hamming distance and
crosses every attainable threshold with overshoot at most `2 * n`.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- A minimum-size circuit chosen by well-ordering. This is a classical proof
witness, not an executable circuit optimizer. -/
noncomputable def minimumCircuit (function : ScalarFunction Bool n) :
    Circuit.Minimum (σ := signature) OperationCost.unit interpretation
      (fun input (_ : Fin 1) => function input) := by
  classical
  let available := Classical.choose_spec (exists_circuit function)
  let circuit := Classical.choose available
  exact circuit.minimum OperationCost.unit interpretation _ (Classical.choose_spec available)

/-- Minimum number of internal gates in a scalar De Morgan circuit. -/
noncomputable def complexity (function : ScalarFunction Bool n) : Nat :=
  (minimumCircuit function).gateCount

/-- The natural-valued Boolean measure agrees with generic gate complexity. -/
theorem complexity_eq_gateComplexity (function : ScalarFunction Bool n) :
    (complexity function : ENat) =
      Circuit.gateComplexity (σ := signature) interpretation (fun input (_ : Fin 1) => function input) := by
  simpa [Circuit.gateComplexity, complexity, Circuit.size] using
    (Circuit.costComplexity_eq OperationCost.unit
      (minimumCircuit function).computes (minimumCircuit function).minimal.cost).symm

/-- Any concrete circuit upper-bounds minimum internal gate count. -/
theorem complexity_le (circuit : Circuit signature n gates 1)
    {function : ScalarFunction Bool n}
    (computes : circuit.ComputesWith interpretation (fun input _ => function input)) :
    complexity function ≤ gates := by
  simpa [complexity, Circuit.size] using (minimumCircuit function).minimal.cost circuit computes

/-- The constant functions have one-gate implementations at every width. -/
theorem complexity_constant_le (n : Nat) (value : Bool) :
    complexity (fun _ : Fin n → Bool => value) ≤ 1 := by
  apply complexity_le (Expression.constant value : Expression n).circuit
  intro input
  funext output
  have equal : output = 0 := Subsingleton.elim _ _
  simp [equal, Expression.circuit_eval, Expression.eval]

/-- Gate hardness is exactly a strict lower bound on the natural minimum. -/
theorem gateHard_iff (function : ScalarFunction Bool n) (budget : Nat) :
    Circuit.GateHard (σ := signature) interpretation budget (fun input (_ : Fin 1) => function input) ↔
      budget < complexity function := by
  constructor
  · intro hard
    by_contra low
    exact hard _ (Nat.le_of_not_gt low) (minimumCircuit function).circuit
      (minimumCircuit function).computes
  · intro hard gates small circuit computes
    have := complexity_le circuit computes
    omega

/-- Changing one truth-table entry adds at most twice the input width. -/
theorem complexity_update_le (function : ScalarFunction Bool n) (point : Fin n → Bool)
    (value : Bool) :
    complexity (Function.update function point value) ≤ complexity function + 2 * n := by
  obtain ⟨gates, circuit, computes, bound⟩ := exists_update_circuit
    (minimumCircuit function).circuit function (minimumCircuit function).computes point value
  exact (complexity_le circuit computes).trans bound

/-- One-sided Hamming Lipschitz bound on Boolean circuit complexity. -/
theorem complexity_le_add_hammingDist (left right : ScalarFunction Bool n) :
    complexity right ≤ complexity left + 2 * n * hammingDist left right :=
  BooleanCube.le_add_mul_hammingDist complexity (2 * n) complexity_update_le left right

/-- Boolean circuit complexity is `2 * n` Lipschitz on the truth-table cube. -/
theorem complexity_dist_le (left right : ScalarFunction Bool n) :
    Nat.dist (complexity left) (complexity right) ≤ 2 * n * hammingDist left right :=
  BooleanCube.dist_le_mul_hammingDist complexity (2 * n) complexity_update_le left right

/-- Every threshold above the constant-function cost and below an attained
complexity is crossed with overshoot at most `2 * n`. -/
theorem exists_complexity_between (threshold : Nat) (positive : 1 ≤ threshold)
    (hard : ScalarFunction Bool n) (above : threshold < complexity hard) :
    ∃ function : ScalarFunction Bool n,
      threshold < complexity function ∧ complexity function ≤ threshold + 2 * n :=
  BooleanCube.exists_between complexity (2 * n) threshold complexity_update_le
    (fun _ => false) hard ((complexity_constant_le n false).trans positive) above

end Algebraic.DeMorgan
