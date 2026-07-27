/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.DecisionTree
public import Complexitylib.Circuits.Restriction

/-!
# Finite-arity decision trees -- definitions

The original `DecisionTree` syntax uses natural-number query labels. Switching
arguments, however, count restrictions on exactly `N` variables. `DecisionTree.On
N` makes that arity part of the type and prevents out-of-range queries.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree

/-- A Boolean decision tree whose every query is one of exactly `N`
variables. -/
inductive On (N : ℕ) where
  /-- A leaf carrying its Boolean output. -/
  | leaf (value : Bool)
  /-- Query `index`, taking `ifFalse` on zero and `ifTrue` on one. -/
  | node (index : Fin N) (ifFalse ifTrue : On N)
  deriving Repr, DecidableEq

namespace On

/-- Evaluate a finite-arity decision tree. -/
def eval (input : BitString N) : On N → Bool
  | .leaf value => value
  | .node index ifFalse ifTrue =>
      if input index then eval input ifTrue else eval input ifFalse

/-- Maximum number of queries on any root-to-leaf path. -/
def depth : On N → ℕ
  | .leaf _ => 0
  | .node _ ifFalse ifTrue =>
      max ifFalse.depth ifTrue.depth + 1

/-- Number of leaves. -/
def numLeaves : On N → ℕ
  | .leaf _ => 1
  | .node _ ifFalse ifTrue =>
      ifFalse.numLeaves + ifTrue.numLeaves

/-- The finite set of variables queried by the tree. -/
def vars : On N → Finset (Fin N)
  | .leaf _ => ∅
  | .node index ifFalse ifTrue =>
      insert index (ifFalse.vars ∪ ifTrue.vars)

/-- Negate a decision tree by complementing every leaf. -/
def neg : On N → On N
  | .leaf value => .leaf (!value)
  | .node index ifFalse ifTrue =>
      .node index ifFalse.neg ifTrue.neg

/-- Erase the arity proof from every query label. -/
def toDecisionTree : On N → DecisionTree
  | .leaf value => .leaf value
  | .node index ifFalse ifTrue =>
      .node index.val ifFalse.toDecisionTree ifTrue.toDecisionTree

/-- Simplify a finite decision tree under a matching restriction. -/
def restrict (restriction : Restriction.On N) : On N → On N
  | .leaf value => .leaf value
  | .node index ifFalse ifTrue =>
      match restriction index with
      | some false => restrict restriction ifFalse
      | some true => restrict restriction ifTrue
      | none =>
          .node index (restrict restriction ifFalse)
            (restrict restriction ifTrue)

end On
end DecisionTree
end Complexity
