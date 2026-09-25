/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTree

/-!
# Evaluation paths in Boolean decision trees

The evaluation path of a decision tree on an input records exactly the
queries and branch values encountered before reaching a leaf. Its length is
at most the tree depth. More importantly, any second input agreeing on every
coordinate queried along that path produces the same output.

This is an adversary-facing semantic interface. It does not normalize or
optimize decision trees and permits repeated queries.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace DecisionTree

/-- Query transcript followed by `tree` on `input`. -/
def evaluationPath : DecisionTree n ->
    (Fin n -> Bool) -> List (PathStep n)
  | .leaf _, _ => []
  | .query index onFalse onTrue, input =>
      ⟨index, input index⟩ ::
        if input index then
          evaluationPath onTrue input
        else
          evaluationPath onFalse input

/-- An evaluation path cannot be longer than the source tree's depth. -/
theorem evaluationPath_length_le_depth
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    (tree.evaluationPath input).length <= tree.depth := by
  induction tree with
  | leaf value => simp [evaluationPath, depth]
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases inputValue : input index
      · simp [evaluationPath, depth, inputValue, falseHypothesis]
      · simp [evaluationPath, depth, inputValue, trueHypothesis]

/-- Inputs agreeing on all coordinates queried along one evaluation path
produce the same tree output. -/
theorem eval_eq_of_agree_on_evaluationPath
    (tree : DecisionTree n)
    (source target : Fin n -> Bool)
    (agree : forall index,
      index ∈ (PathStep.indices (tree.evaluationPath source)).toFinset ->
        target index = source index) :
    tree.eval target = tree.eval source := by
  induction tree with
  | leaf value => rfl
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases sourceValue : source index with
      | false =>
          have targetValue : target index = false := by
            rw [agree index (by
              simp [evaluationPath, sourceValue, PathStep.indices]),
              sourceValue]
          simp only [eval_query, sourceValue, targetValue,
            Bool.false_eq_true, ite_false]
          apply falseHypothesis
          intro current present
          apply agree current
          rw [evaluationPath, sourceValue]
          simp only [PathStep.indices, List.map_cons,
            List.toFinset_cons, Finset.mem_insert]
          exact Or.inr present
      | true =>
          have targetValue : target index = true := by
            rw [agree index (by
              simp [evaluationPath, sourceValue, PathStep.indices]),
              sourceValue]
          simp only [eval_query, sourceValue, targetValue, ite_true]
          apply trueHypothesis
          intro current present
          apply agree current
          rw [evaluationPath, sourceValue]
          simp only [PathStep.indices, List.map_cons,
            List.toFinset_cons, Finset.mem_insert]
          exact Or.inr present

end DecisionTree
end AC0
end Algebraic
