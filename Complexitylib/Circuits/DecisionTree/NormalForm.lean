/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite
public import Complexitylib.Circuits.DecisionTree.NormalForm.Defs
public import Complexitylib.Circuits.DecisionTree.NormalForm.Internal

/-!
# Compiling finite decision trees to CNF and DNF

An accepting path of length at most `d` becomes a DNF term of width at most
`d`. De Morgan duality gives a CNF with the same bounds. Both normal forms
compute exactly the original tree, have at most one component per leaf, and
therefore have at most `2 ^ d` terms or clauses.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- The accepting-path DNF computes exactly the original decision tree. -/
theorem eval_toDNF
    (tree : DecisionTree.On N) (input : BitString N) :
    tree.toDNF.eval input = tree.eval input :=
  eval_toDNF_internal tree input

/-- The dual CNF computes exactly the original decision tree. -/
theorem eval_toCNF
    (tree : DecisionTree.On N) (input : BitString N) :
    tree.toCNF.eval input = tree.eval input :=
  eval_toCNF_internal tree input

/-- The accepting-path DNF has width at most the tree depth. -/
theorem width_toDNF_le_depth
    (tree : DecisionTree.On N) :
    tree.toDNF.width ≤ tree.depth :=
  width_toDNF_le_depth_internal tree

/-- The dual CNF has width at most the tree depth. -/
theorem width_toCNF_le_depth
    (tree : DecisionTree.On N) :
    tree.toCNF.width ≤ tree.depth :=
  width_toCNF_le_depth_internal tree

/-- The accepting-path DNF has at most one term per decision-tree leaf. -/
theorem complexity_toDNF_le_numLeaves
    (tree : DecisionTree.On N) :
    tree.toDNF.complexity ≤ tree.numLeaves :=
  complexity_toDNF_le_numLeaves_internal tree

/-- The dual CNF has at most one clause per decision-tree leaf. -/
theorem complexity_toCNF_le_numLeaves
    (tree : DecisionTree.On N) :
    tree.toCNF.complexity ≤ tree.numLeaves :=
  complexity_toCNF_le_numLeaves_internal tree

/-- A depth-`d` decision tree compiles to a DNF with at most `2 ^ d` terms. -/
theorem complexity_toDNF_le_two_pow_depth
    (tree : DecisionTree.On N) :
    tree.toDNF.complexity ≤ 2 ^ tree.depth :=
  complexity_toDNF_le_two_pow_depth_internal tree

/-- A depth-`d` decision tree compiles to a CNF with at most `2 ^ d` clauses. -/
theorem complexity_toCNF_le_two_pow_depth
    (tree : DecisionTree.On N) :
    tree.toCNF.complexity ≤ 2 ^ tree.depth :=
  complexity_toCNF_le_two_pow_depth_internal tree

/-- Disjoining a list of trees and compiling to DNF preserves semantics. -/
theorem eval_anyDNF
    (trees : List (DecisionTree.On N))
    (input : BitString N) :
    (anyDNF trees).eval input =
      trees.any fun tree => tree.eval input :=
  eval_anyDNF_internal trees input

/-- Conjoining a list of trees and compiling to CNF preserves semantics. -/
theorem eval_allCNF
    (trees : List (DecisionTree.On N))
    (input : BitString N) :
    (allCNF trees).eval input =
      trees.all fun tree => tree.eval input :=
  eval_allCNF_internal trees input

/-- A disjunction of depth-bounded trees compiles to a DNF under the same
width bound. -/
theorem width_anyDNF_le
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (anyDNF trees).width ≤ bound :=
  width_anyDNF_le_internal trees bound hbound

/-- A conjunction of depth-bounded trees compiles to a CNF under the same
width bound. -/
theorem width_allCNF_le
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (allCNF trees).width ≤ bound :=
  width_allCNF_le_internal trees bound hbound

/-- A disjunction of depth-`d` trees compiles to at most
`number of trees * 2 ^ d` DNF terms. -/
theorem complexity_anyDNF_le
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (anyDNF trees).complexity ≤
      trees.length * 2 ^ bound :=
  complexity_anyDNF_le_internal trees bound hbound

/-- A conjunction of depth-`d` trees compiles to at most
`number of trees * 2 ^ d` CNF clauses. -/
theorem complexity_allCNF_le
    (trees : List (DecisionTree.On N)) (bound : ℕ)
    (hbound :
      ∀ tree ∈ trees, tree.depth ≤ bound) :
    (allCNF trees).complexity ≤
      trees.length * 2 ^ bound :=
  complexity_allCNF_le_internal trees bound hbound

end DecisionTree.On
end Complexity
