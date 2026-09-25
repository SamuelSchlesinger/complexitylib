/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Complexity
public import Complexitylib.Algebraic.LowerBound.Counting.Shannon

/-!
# Finite circuit size hierarchy

Shannon counting supplies a hard endpoint, and the truth-table cube supplies
intermediate complexities. The finite theorem uses the exact sharp census.
The eventual theorem crosses every threshold from `1` through `2^n / n`,
with additive overshoot at most `2 * n`. Complexity counts all internal gates
of the De Morgan signature, exactly as in the counting theorem.
-/

@[expose] public section

namespace Algebraic.DeMorgan

private theorem scalar_hard_of_target {target : Target Bool n 1}
    (hard : Circuit.GateHard (σ := signature) interpretation budget target) :
    budget < complexity (fun input => target input 0) := by
  apply (gateHard_iff _ budget).mp
  convert hard using 1
  funext input output
  exact congrArg (target input) (Subsingleton.elim _ _)

/-- Exact finite hierarchy criterion, retaining the factorial-improved
Shannon census as the sufficient condition for a hard endpoint. -/
theorem exists_complexity_between_of_sharpBudget (threshold : Nat)
    (positive : 1 ≤ threshold)
    (small : signature.sharpBudget n 1 threshold < Target.count Bool n 1) :
    ∃ function : ScalarFunction Bool n,
      threshold < complexity function ∧ complexity function ≤ threshold + 2 * n := by
  obtain ⟨target, hard⟩ := Circuit.exists_boolean_hard_sharp (σ := signature) interpretation small
  exact exists_complexity_between threshold positive _ (scalar_hard_of_target hard)

private theorem maximumArity : signature.HasMaximumArity 2 where
  arity_le := by intro op; cases op <;> decide
  attained := ⟨.and, rfl⟩

/-- At every sufficiently large width, all thresholds through the Shannon
scale are attained to within an additive `2 * n` gates. -/
theorem eventually_exists_complexity_between :
    ∀ᶠ n in Filter.atTop, ∀ threshold : Nat,
      1 ≤ threshold → threshold ≤ 2 ^ n / n →
        ∃ function : ScalarFunction Bool n,
          threshold < complexity function ∧ complexity function ≤ threshold + 2 * n := by
  have hard := (Circuit.asymptoticallyAlmostAllHard_shannon (σ := signature) interpretation maximumArity
    (by decide) (by decide) (show 0 < 1 by decide)).eventually_exists_hard
    (Filter.Eventually.of_forall fun n => by
      rw [Circuit.card_fullFamily, Target.count_eq]
      simp)
  filter_upwards [hard] with n hn
  obtain ⟨target, _, targetHard⟩ := hn
  have above : 2 ^ n / n < complexity (fun input => target input 0) := by
    simpa using scalar_hard_of_target targetHard
  intro threshold positive below
  exact exists_complexity_between threshold positive _ (below.trans_lt above)

end Algebraic.DeMorgan
