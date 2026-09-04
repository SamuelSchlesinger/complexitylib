/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.Iteration.Internal
public import Complexitylib.Circuits.XOR.Restriction.Internal

/-!
# Parity versus finite AC0 formulas -- proof internals
-/


public section

namespace Complexity
namespace AC0Formula

theorem parity_counting_obstruction_internal
    (formula : AC0Formula N)
    (computes :
      ∀ input,
        formula.eval input = Schnorr.xorBool N input)
    (stageCount queryCount q : ℕ)
    (hdepth : formula.depth ≤ stageCount)
    (hquery : 2 ≤ queryCount) (hq : 0 < q) :
    (N * ((2 * q + 1) ^ (N - 1)) ^ stageCount) *
          q ^ queryCount ≤
      (((2 * q + 1) ^ N) ^ stageCount * queryCount) *
          q ^ queryCount +
        formula.gateCount *
          ((2 * q + 1) ^ N) ^ stageCount *
          (4 * (queryCount + 1)) ^ queryCount * N := by
  apply Nat.le_of_not_gt
  intro hnumeric
  obtain ⟨seeds, hshallow, hfree⟩ :=
    exists_shallow_stagedDecisionTree_of_counting_internal
      formula stageCount queryCount q hdepth hquery hq hnumeric
  let stages := RandomRestriction.decodeStages seeds
  let restriction := RandomRestriction.finalRestriction seeds
  let tree := formula.stagedDecisionTree stageCount stages
  have htree :
      ∀ input,
        tree.eval input =
          Schnorr.xorBool N (restriction.applyTo input) := by
    intro input
    change
      (formula.stagedDecisionTree stageCount stages).eval input =
        Schnorr.xorBool N (restriction.applyTo input)
    rw [eval_stagedDecisionTree_internal
      stageCount stages formula hdepth input]
    exact computes _
  have hlower :=
    Schnorr.freeVariables_card_le_depth_of_restricted_xor_internal
      tree restriction htree
  have hfree' :
      queryCount ≤ restriction.freeVariables.card := by
    simpa [restriction] using hfree
  have hshallow' : tree.depth < queryCount := by
    simpa [tree, stages] using hshallow
  exact (not_lt_of_ge (hfree'.trans hlower)) hshallow'

end AC0Formula
end Complexity
