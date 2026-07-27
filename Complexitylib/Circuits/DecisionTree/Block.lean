/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DecisionTree.Block.Defs
public import Complexitylib.Circuits.DecisionTree.Block.Internal

/-!
# Complete query blocks in finite decision trees

This module exposes a reusable complete query block: every listed coordinate is
queried before control reaches a continuation indexed by the collected finite
restriction.
-/

@[expose] public section

namespace Complexity
namespace DecisionTree.On

/-- Every listed coordinate is fixed to the value read from the input. -/
theorem assignmentFor_apply_of_mem
    (queries : List (Fin N)) (input : BitString N)
    (index : Fin N) (hmem : index ∈ queries) :
    assignmentFor queries input index = some (input index) :=
  assignmentFor_apply_of_mem_internal queries input index hmem

/-- Every coordinate outside the query list remains free. -/
theorem assignmentFor_apply_of_not_mem
    (queries : List (Fin N)) (input : BitString N)
    (index : Fin N) (hmem : index ∉ queries) :
    assignmentFor queries input index = none :=
  assignmentFor_apply_of_not_mem_internal queries input index hmem

/-- Reapplying values read from an input leaves that input unchanged. -/
theorem assignmentFor_applyTo
    (queries : List (Fin N)) (input : BitString N) :
    (assignmentFor queries input).applyTo input = input :=
  assignmentFor_applyTo_internal queries input

/-- Reading a query block back from any total extension of the induced
restriction recovers the same restriction. -/
theorem assignmentFor_reapply
    (queries : List (Fin N)) (input fallback : BitString N) :
    assignmentFor queries
        ((assignmentFor queries input).applyTo fallback) =
      assignmentFor queries input :=
  assignmentFor_reapply_internal queries input fallback

/-- Concatenating path records composes their induced restrictions. -/
theorem assignmentOfPath_append
    (left right : List (Fin N × Bool)) :
    assignmentOfPath (left ++ right) =
      Restriction.On.comp
        (assignmentOfPath left)
        (assignmentOfPath right) :=
  assignmentOfPath_append_internal left right

/-- A path assignment leaves every unrecorded coordinate free. -/
theorem assignmentOfPath_apply_of_not_mem
    (path : List (Fin N × Bool)) (index : Fin N)
    (hindex : index ∉ path.map Prod.fst) :
    assignmentOfPath path index = none :=
  assignmentOfPath_apply_of_not_mem_internal
    path index hindex

/-- Every coordinate recorded by a duplicate-free path receives a value. -/
theorem assignmentOfPath_apply_eq_some_of_mem
    (path : List (Fin N × Bool))
    (hnodup : (path.map Prod.fst).Nodup)
    (index : Fin N) (hindex : index ∈ path.map Prod.fst) :
    ∃ value, assignmentOfPath path index = some value :=
  assignmentOfPath_apply_eq_some_of_mem_internal
    path hnodup index hindex

/-- A query/value pair in a duplicate-free path is recorded exactly. -/
theorem assignmentOfPath_apply_of_mem
    (path : List (Fin N × Bool))
    (hnodup : (path.map Prod.fst).Nodup)
    (query : Fin N × Bool) (hquery : query ∈ path) :
    assignmentOfPath path query.1 = some query.2 :=
  assignmentOfPath_apply_of_mem_internal
    path hnodup query hquery

/-- The path record selected through a complete block induces exactly the
selected deep-branch restriction. -/
theorem assignmentOfPath_deepBlockPath
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    assignmentOfPath
        (deepBlockPath queries continuation) =
      deepBranch queries continuation :=
  assignmentOfPath_deepBlockPath_internal
    queries continuation

/-- The canonical deepest path through a complete block consists of the block
prefix followed by the deepest path of the selected continuation. -/
theorem deepPath_queryAll
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    (queryAll queries continuation).deepPath =
      deepBlockPath queries continuation ++
        (continuation
          (deepBranch queries continuation)).deepPath :=
  deepPath_queryAll_internal queries continuation

/-- The block portion of the canonical deepest path queries exactly the
listed coordinates, in order. -/
theorem map_fst_deepBlockPath
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N) :
    (deepBlockPath queries continuation).map Prod.fst =
      queries :=
  map_fst_deepBlockPath_internal queries continuation

/-- The selected deep branch leaves every coordinate outside the block free. -/
theorem deepBranch_apply_of_not_mem
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (index : Fin N) (hmem : index ∉ queries) :
    deepBranch queries continuation index = none :=
  deepBranch_apply_of_not_mem_internal
    queries continuation index hmem

/-- Every coordinate in a duplicate-free block is fixed by the selected deep
branch. -/
theorem deepBranch_apply_eq_some_of_mem
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (index : Fin N)
    (hmem : index ∈ queries) :
    ∃ value,
      deepBranch queries continuation index = some value :=
  deepBranch_apply_eq_some_of_mem_internal
    queries continuation hnodup index hmem

/-- The selected restriction records every query/value pair in the canonical
deep block path. -/
theorem deepBranch_apply_of_mem_deepBlockPath
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (query : Fin N × Bool)
    (hquery : query ∈ deepBlockPath queries continuation) :
    deepBranch queries continuation query.1 =
      some query.2 :=
  deepBranch_apply_of_mem_deepBlockPath_internal
    queries continuation hnodup query hquery

/-- Canonicalizing a duplicate-free selected deep branch by reading it back
from any total extension changes nothing. -/
theorem assignmentFor_deepBranch
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup) (fallback : BitString N) :
    assignmentFor queries
        ((deepBranch queries continuation).applyTo fallback) =
      deepBranch queries continuation :=
  assignmentFor_deepBranch_internal
    queries continuation hnodup fallback

/-- Query-block evaluation passes the restriction read from the input to the
continuation. -/
theorem eval_queryAll
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (input : BitString N) :
    (queryAll queries continuation).eval input =
      (continuation (assignmentFor queries input)).eval input :=
  eval_queryAll_internal queries continuation input

/-- A query block adds at most its list length to a uniform continuation-depth
bound. -/
theorem depth_queryAll_le
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (continuationDepth : ℕ)
    (hdepth : ∀ restriction,
      (continuation restriction).depth ≤ continuationDepth) :
    (queryAll queries continuation).depth ≤
      queries.length + continuationDepth :=
  depth_queryAll_le_internal queries continuation
    continuationDepth hdepth

/-- Query-block support consists only of the listed queries and continuation
support. -/
theorem vars_queryAll_subset
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (support : Finset (Fin N))
    (hvars : ∀ restriction,
      (continuation restriction).vars ⊆ support) :
    (queryAll queries continuation).vars ⊆
      queries.toFinset ∪ support :=
  vars_queryAll_subset_internal queries continuation support hvars

/-- Distinct block queries followed by read-once continuations on disjoint
support form a path-read-once decision tree. -/
theorem pathReadOnce_queryAll
    (queries : List (Fin N))
    (continuation : Restriction.On N → DecisionTree.On N)
    (hnodup : queries.Nodup)
    (hreadOnce : ∀ restriction,
      (continuation restriction).PathReadOnce)
    (hdisjoint : ∀ restriction,
      Disjoint queries.toFinset (continuation restriction).vars) :
    (queryAll queries continuation).PathReadOnce :=
  pathReadOnce_queryAll_internal queries continuation
    hnodup hreadOnce hdisjoint

end DecisionTree.On
end Complexity
