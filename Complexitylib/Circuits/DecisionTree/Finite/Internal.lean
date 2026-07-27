/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite.Defs
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Finite-arity decision trees -- proof internals
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

theorem eval_toDecisionTree_internal (input : BitString N)
    (tree : DecisionTree.On N) :
    tree.toDecisionTree.eval input.toTotal = tree.eval input := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [toDecisionTree, DecisionTree.eval, eval,
        BitString.toTotal_apply, ihFalse, ihTrue]

theorem depth_toDecisionTree_internal (tree : DecisionTree.On N) :
    tree.toDecisionTree.depth = tree.depth := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [toDecisionTree, DecisionTree.depth, depth, ihFalse, ihTrue]

theorem numLeaves_toDecisionTree_internal (tree : DecisionTree.On N) :
    tree.toDecisionTree.numLeaves = tree.numLeaves := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [toDecisionTree, DecisionTree.numLeaves, numLeaves,
        ihFalse, ihTrue]

theorem numLeaves_le_two_pow_depth_internal
    (tree : DecisionTree.On N) :
    tree.numLeaves ≤ 2 ^ tree.depth := by
  rw [← numLeaves_toDecisionTree_internal,
    ← depth_toDecisionTree_internal]
  exact tree.toDecisionTree.numLeaves_le_two_pow_depth

theorem card_vars_le_arity_internal (tree : DecisionTree.On N) :
    tree.vars.card ≤ N := by
  exact (Finset.card_le_univ tree.vars).trans_eq
    (Fintype.card_fin N)

theorem eval_neg_internal (input : BitString N)
    (tree : DecisionTree.On N) :
    tree.neg.eval input = !(tree.eval input) := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp only [neg, eval, ihFalse, ihTrue]
      cases input index <;> rfl

theorem depth_neg_internal (tree : DecisionTree.On N) :
    tree.neg.depth = tree.depth := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [neg, depth, ihFalse, ihTrue]

theorem numLeaves_neg_internal (tree : DecisionTree.On N) :
    tree.neg.numLeaves = tree.numLeaves := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [neg, numLeaves, ihFalse, ihTrue]

theorem vars_neg_internal (tree : DecisionTree.On N) :
    tree.neg.vars = tree.vars := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [neg, vars, ihFalse, ihTrue]

theorem eval_restrict_internal (restriction : Restriction.On N)
    (input : BitString N) (tree : DecisionTree.On N) :
    (tree.restrict restriction).eval input =
      tree.eval (restriction.applyTo input) := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      cases hvalue : restriction index with
      | none =>
          simp [restrict, eval, Restriction.On.applyTo, hvalue,
            ihFalse, ihTrue]
      | some value =>
          cases value <;>
            simp [restrict, eval, Restriction.On.applyTo, hvalue,
              ihFalse, ihTrue]

theorem depth_restrict_le_internal
    (restriction : Restriction.On N) (tree : DecisionTree.On N) :
    (tree.restrict restriction).depth ≤ tree.depth := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      cases hvalue : restriction index with
      | none =>
          simp only [restrict, hvalue, depth]
          exact Nat.add_le_add_right
            (max_le_max ihFalse ihTrue) 1
      | some value =>
          cases value
          · simp only [restrict, hvalue, depth]
            exact ihFalse.trans
              ((le_max_left _ _).trans (Nat.le_add_right _ _))
          · simp only [restrict, hvalue, depth]
            exact ihTrue.trans
              ((le_max_right _ _).trans (Nat.le_add_right _ _))

theorem vars_restrict_subset_filter_internal
    (restriction : Restriction.On N) (tree : DecisionTree.On N) :
    (tree.restrict restriction).vars ⊆
      tree.vars.filter fun index => restriction index = none := by
  induction tree with
  | leaf value => simp [restrict, vars]
  | node index ifFalse ifTrue ihFalse ihTrue =>
      cases hvalue : restriction index with
      | none =>
          simp only [restrict, hvalue, vars]
          intro queried hqueried
          simp only [Finset.mem_insert, Finset.mem_union] at hqueried
          simp only [Finset.mem_filter, Finset.mem_insert,
            Finset.mem_union]
          rcases hqueried with rfl | hqueried | hqueried
          · exact ⟨Or.inl rfl, hvalue⟩
          · have hchild := ihFalse hqueried
            simp only [Finset.mem_filter] at hchild
            exact ⟨Or.inr (Or.inl hchild.1), hchild.2⟩
          · have hchild := ihTrue hqueried
            simp only [Finset.mem_filter] at hchild
            exact ⟨Or.inr (Or.inr hchild.1), hchild.2⟩
      | some value =>
          cases value
          · simp only [restrict, hvalue]
            intro queried hqueried
            have hchild := ihFalse hqueried
            simp only [Finset.mem_filter] at hchild ⊢
            exact ⟨by simp [vars, hchild.1], hchild.2⟩
          · simp only [restrict, hvalue]
            intro queried hqueried
            have hchild := ihTrue hqueried
            simp only [Finset.mem_filter] at hchild ⊢
            exact ⟨by simp [vars, hchild.1], hchild.2⟩

theorem restrict_empty_internal (tree : DecisionTree.On N) :
    tree.restrict Restriction.On.empty = tree := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      simp [restrict, ihFalse, ihTrue]

theorem restrict_comp_internal (first second : Restriction.On N)
    (tree : DecisionTree.On N) :
    (tree.restrict first).restrict second =
      tree.restrict (Restriction.On.comp first second) := by
  induction tree with
  | leaf value => rfl
  | node index ifFalse ifTrue ihFalse ihTrue =>
      cases hfirst : first index with
      | none =>
          cases hsecond : second index with
          | none =>
              simp [restrict, Restriction.On.comp, hfirst, hsecond,
                ihFalse, ihTrue]
          | some value =>
              cases value <;>
                simp [restrict, Restriction.On.comp, hfirst, hsecond,
                  ihFalse, ihTrue]
      | some value =>
          cases value <;>
            simp [restrict, Restriction.On.comp, hfirst,
              ihFalse, ihTrue]

end DecisionTree.On
end Complexity
