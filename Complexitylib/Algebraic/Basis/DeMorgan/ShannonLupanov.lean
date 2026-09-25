/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.NativeCost
public import Complexitylib.Algebraic.Basis.DeMorgan.CSLib
public import Cslib.Computability.Circuit.Boolean.Shannon
public import Cslib.Computability.Circuit.Boolean.Lupanov

/-!
# Shannon and Lupanov bounds for De Morgan complexity

CSLib's sharp Boolean bounds transfer through the realizations in
`DeMorgan.CSLib`. Identity elimination preserves the Shannon lower bound on
total internal gates; importing Lupanov circuits preserves their total size.
For `standardCost`, which makes constants free, the lower bound has an
additive two-gate allowance supplied by `withSharedConstants`.

The local explicit mass-production constructions retain their finite cost
ledgers. The results here use CSLib's asymptotic existence theorems.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- For all sufficiently large input widths, some Boolean function requires
strictly more than `2^n / n` internal gates, including constants and identities. -/
theorem exists_complexity_gt_two_pow_div :
    ∃ N : Nat, ∀ n ≥ N, ∃ function : ScalarFunction Bool n,
      2 ^ n / (n : Real) < (complexity function : Real) := by
  obtain ⟨N, hard⟩ := Cslib.Circuits.Boolean.Shannon.exists_hard_function
  refine ⟨N, fun n large => ?_⟩
  obtain ⟨function, lower⟩ := hard n large
  refine ⟨function, ?_⟩
  have bound := lower (toBoolean.compile (minimumCircuit function).circuit)
    ((toBoolean_computes _ function).2 (minimumCircuit function).computes)
  exact bound.trans_le (by exact_mod_cast toBoolean_size_le (minimumCircuit function).circuit)

/-- Lupanov's leading coefficient one bounds the minimum total gate count
uniformly over all Boolean functions of a sufficiently large input width. -/
theorem eventually_complexity_le_lupanov (ε : Real) (positive : 0 < ε) :
    ∃ N : Nat, ∀ n ≥ N, ∀ function : ScalarFunction Bool n,
      (complexity function : Real) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, upper⟩ := Cslib.Circuits.Boolean.Lupanov.exists_circuit ε positive
  refine ⟨N, fun n large function => ?_⟩
  obtain ⟨gates, circuit, computes, bounded⟩ := upper n large function
  have minimal := complexity_le (fromBoolean.compile circuit)
    ((fromBoolean_computes circuit function).2 computes)
  change complexity function ≤ (fromBoolean.compile circuit).size at minimal
  rw [fromBoolean_size] at minimal
  exact (show (complexity function : Real) ≤ (circuit.size : Real) by
    exact_mod_cast minimal).trans bounded

/-- Free constants change the Shannon lower bound by at most two gates. -/
theorem exists_standardCost_add_two_gt_two_pow_div :
    ∃ N : Nat, ∀ n ≥ N, ∃ function : ScalarFunction Bool n,
      ∀ {g} (circuit : Circuit signature n g 1),
        circuit.ComputesWith interpretation (fun input _ => function input) →
          2 ^ n / (n : Real) < (circuit.cost standardCost : Real) + 2 := by
  obtain ⟨N, hard⟩ := exists_complexity_gt_two_pow_div
  refine ⟨N, fun n large => ?_⟩
  obtain ⟨function, lower⟩ := hard n large
  refine ⟨function, fun circuit computes => ?_⟩
  exact lower.trans_le (by exact_mod_cast complexity_le_standardCost_add_two circuit computes)

/-- The standard weighted cost also satisfies Lupanov's sharp upper bound. -/
theorem exists_standardCost_le_lupanov (ε : Real) (positive : 0 < ε) :
    ∃ N : Nat, ∀ n ≥ N, ∀ function : ScalarFunction Bool n,
      ∃ g, ∃ circuit : Circuit signature n g 1,
        circuit.ComputesWith interpretation (fun input _ => function input) ∧
          (circuit.cost standardCost : Real) ≤ (1 + ε) * 2 ^ n / n := by
  obtain ⟨N, upper⟩ := Cslib.Circuits.Boolean.Lupanov.exists_circuit ε positive
  refine ⟨N, fun n large function => ?_⟩
  obtain ⟨gates, circuit, computes, bounded⟩ := upper n large function
  refine ⟨_, fromBoolean.compile circuit,
    (fromBoolean_computes circuit function).2 computes, ?_⟩
  exact (show ((fromBoolean.compile circuit).cost standardCost : Real) ≤
      (circuit.size : Real) by
    exact_mod_cast fromBoolean_standardCost_le circuit).trans bounded

end Algebraic.DeMorgan
