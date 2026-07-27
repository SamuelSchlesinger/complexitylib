/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Path.Defs

/-!
# Complete query blocks in finite decision trees -- definitions

`queryAll queries continuation` builds the complete decision tree that queries
every coordinate in `queries`, in order, and then invokes `continuation` with
the resulting finite restriction. This is the block operation used by the
canonical switching tree.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- The restriction induced by reading `queries` from a total input. Earlier
list entries take precedence, although duplicate queries receive the same value
and therefore do not change the result. -/
def assignmentFor (queries : List (Fin N))
    (input : BitString N) : Restriction.On N :=
  match queries with
  | [] => Restriction.On.empty
  | index :: rest =>
      Restriction.On.comp
        (Restriction.On.single index (input index))
        (assignmentFor rest input)

/-- The finite restriction recorded by a query/value path. Earlier path
entries take precedence if a malformed path repeats a query. -/
def assignmentOfPath :
    List (Fin N × Bool) → Restriction.On N
  | [] => Restriction.On.empty
  | query :: rest =>
      Restriction.On.comp
        (Restriction.On.single query.1 query.2)
        (assignmentOfPath rest)

/-- Query every coordinate in a list before entering a continuation.

The continuation receives exactly the partial assignment collected along the
query block. -/
def queryAll (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    DecisionTree.On N :=
  match queries with
  | [] => continuation Restriction.On.empty
  | index :: rest =>
      .node index
        (queryAll rest fun tail =>
          continuation
            (Restriction.On.comp
              (Restriction.On.single index false) tail))
        (queryAll rest fun tail =>
          continuation
            (Restriction.On.comp
              (Restriction.On.single index true) tail))

/-- The partial assignment selected by the canonical deepest path through a
complete query block. -/
def deepBranch : (queries : List (Fin N)) →
    (Restriction.On N → DecisionTree.On N) →
      Restriction.On N
  | [], _ => Restriction.On.empty
  | index :: rest, continuation =>
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      if (queryAll rest trueContinuation).depth ≤
          (queryAll rest falseContinuation).depth then
        Restriction.On.comp
          (Restriction.On.single index false)
          (deepBranch rest falseContinuation)
      else
        Restriction.On.comp
          (Restriction.On.single index true)
          (deepBranch rest trueContinuation)

/-- The query/value prefix selected by the canonical deepest path through a
complete query block. -/
def deepBlockPath : (queries : List (Fin N)) →
    (Restriction.On N → DecisionTree.On N) →
      List (Fin N × Bool)
  | [], _ => []
  | index :: rest, continuation =>
      let falseContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index false) tail)
      let trueContinuation := fun tail => continuation
        (Restriction.On.comp
          (Restriction.On.single index true) tail)
      if (queryAll rest trueContinuation).depth ≤
          (queryAll rest falseContinuation).depth then
        (index, false) :: deepBlockPath rest falseContinuation
      else
        (index, true) :: deepBlockPath rest trueContinuation

end DecisionTree.On
end Complexity
