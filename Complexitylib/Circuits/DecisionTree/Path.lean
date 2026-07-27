/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Path.Defs
public import Complexitylib.Circuits.DecisionTree.Path.Internal

/-!
# Canonical deepest paths in finite decision trees

Every finite decision tree has a deterministically chosen deepest path whose
length is exactly the tree depth. For path-read-once trees, every prefix of
that path is an embedding into the input coordinates.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- Complementing the leaves preserves the path-read-once property. -/
theorem pathReadOnce_neg (tree : DecisionTree.On N) :
    tree.neg.PathReadOnce ↔ tree.PathReadOnce :=
  pathReadOnce_neg_internal tree

/-- The chosen deepest path has length exactly equal to tree depth. -/
theorem length_deepPath (tree : DecisionTree.On N) :
    tree.deepPath.length = tree.depth :=
  length_deepPath_internal tree

/-- Every query on the chosen path occurs in the tree's variable set. -/
theorem mem_vars_of_mem_deepPath
    (tree : DecisionTree.On N) (query : Fin N × Bool)
    (hquery : query ∈ tree.deepPath) :
    query.1 ∈ tree.vars :=
  mem_vars_of_mem_deepPath_internal tree query hquery

/-- A path-read-once tree has no repeated query on its chosen deepest path. -/
theorem nodup_deepPathVars
    (tree : DecisionTree.On N) (readOnce : tree.PathReadOnce) :
    tree.deepPathVars.Nodup :=
  nodup_deepPathVars_internal tree readOnce

/-- A path-read-once tree has depth at most the number of distinct variables it
queries anywhere. -/
theorem depth_le_card_vars_of_pathReadOnce
    (tree : DecisionTree.On N) (readOnce : tree.PathReadOnce) :
    tree.depth ≤ tree.vars.card :=
  depth_le_card_vars_of_pathReadOnce_internal tree readOnce

end DecisionTree.On
end Complexity
