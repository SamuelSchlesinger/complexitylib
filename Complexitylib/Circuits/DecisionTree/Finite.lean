/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite.Defs
public import Complexitylib.Circuits.DecisionTree.Finite.Internal

/-!
# Finite-arity decision trees

`DecisionTree.On N` records the input arity in its query labels. It is the
decision-tree representation used by finite switching and restriction
arguments; no query can silently fall outside the sampled variable set.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- Erasing query bounds preserves evaluation on the canonical total
extension of a bit string. -/
theorem eval_toDecisionTree (input : BitString N)
    (tree : DecisionTree.On N) :
    tree.toDecisionTree.eval input.toTotal = tree.eval input :=
  eval_toDecisionTree_internal input tree

/-- Erasing query bounds preserves depth exactly. -/
theorem depth_toDecisionTree (tree : DecisionTree.On N) :
    tree.toDecisionTree.depth = tree.depth :=
  depth_toDecisionTree_internal tree

/-- Erasing query bounds preserves leaf count exactly. -/
theorem numLeaves_toDecisionTree (tree : DecisionTree.On N) :
    tree.toDecisionTree.numLeaves = tree.numLeaves :=
  numLeaves_toDecisionTree_internal tree

/-- A depth-`d` finite decision tree has at most `2 ^ d` leaves. -/
theorem numLeaves_le_two_pow_depth (tree : DecisionTree.On N) :
    tree.numLeaves ≤ 2 ^ tree.depth :=
  numLeaves_le_two_pow_depth_internal tree

/-- A finite-arity tree queries at most its declared number of variables. -/
theorem card_vars_le_arity (tree : DecisionTree.On N) :
    tree.vars.card ≤ N :=
  card_vars_le_arity_internal tree

/-- Negating every leaf complements the computed function. -/
theorem eval_neg (input : BitString N) (tree : DecisionTree.On N) :
    tree.neg.eval input = !(tree.eval input) :=
  eval_neg_internal input tree

/-- Leaf negation preserves query depth exactly. -/
theorem depth_neg (tree : DecisionTree.On N) :
    tree.neg.depth = tree.depth :=
  depth_neg_internal tree

/-- Leaf negation preserves the number of leaves exactly. -/
theorem numLeaves_neg (tree : DecisionTree.On N) :
    tree.neg.numLeaves = tree.numLeaves :=
  numLeaves_neg_internal tree

/-- Leaf negation preserves the queried-variable set exactly. -/
theorem vars_neg (tree : DecisionTree.On N) :
    tree.neg.vars = tree.vars :=
  vars_neg_internal tree

/-- Restriction commutes with finite-tree evaluation. -/
theorem eval_restrict (restriction : Restriction.On N)
    (input : BitString N) (tree : DecisionTree.On N) :
    (tree.restrict restriction).eval input =
      tree.eval (restriction.applyTo input) :=
  eval_restrict_internal restriction input tree

/-- Restriction cannot increase finite decision-tree depth. -/
theorem depth_restrict_le (restriction : Restriction.On N)
    (tree : DecisionTree.On N) :
    (tree.restrict restriction).depth ≤ tree.depth :=
  depth_restrict_le_internal restriction tree

/-- Every query surviving restriction was queried originally and remains
free. -/
theorem vars_restrict_subset_filter
    (restriction : Restriction.On N) (tree : DecisionTree.On N) :
    (tree.restrict restriction).vars ⊆
      tree.vars.filter fun index => restriction index = none :=
  vars_restrict_subset_filter_internal restriction tree

@[simp] theorem restrict_empty (tree : DecisionTree.On N) :
    tree.restrict Restriction.On.empty = tree :=
  restrict_empty_internal tree

/-- Sequential restriction agrees with left-biased finite composition. -/
theorem restrict_comp (first second : Restriction.On N)
    (tree : DecisionTree.On N) :
    (tree.restrict first).restrict second =
      tree.restrict (Restriction.On.comp first second) :=
  restrict_comp_internal first second tree

end DecisionTree.On
end Complexity
