/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Finite.Defs

/-!
# Canonical deepest paths in finite decision trees -- definitions
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- A deepest root-to-leaf path, recording each query and chosen branch.
Ties are resolved toward the false child. -/
def deepPath : DecisionTree.On N → List (Fin N × Bool)
  | .leaf _ => []
  | .node index ifFalse ifTrue =>
      if ifTrue.depth ≤ ifFalse.depth then
        (index, false) :: ifFalse.deepPath
      else
        (index, true) :: ifTrue.deepPath

/-- The query indices occurring on `deepPath`. -/
def deepPathVars (tree : DecisionTree.On N) : List (Fin N) :=
  tree.deepPath.map Prod.fst

/-- No root-to-leaf path repeats a query. This structural predicate is stronger
than merely having a duplicate-free chosen deepest path. -/
def PathReadOnce : DecisionTree.On N → Prop
  | .leaf _ => True
  | .node index ifFalse ifTrue =>
      index ∉ ifFalse.vars ∧ index ∉ ifTrue.vars ∧
        ifFalse.PathReadOnce ∧ ifTrue.PathReadOnce

end DecisionTree.On
end Complexity
