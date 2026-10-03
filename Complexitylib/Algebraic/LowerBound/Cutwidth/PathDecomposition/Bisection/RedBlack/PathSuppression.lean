/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Defs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Internal.Counting

/-!
# Suppressing path vertices in forests

Suppressing an independent family of vertices preserves reachability
between all surviving vertices. If the original graph is a forest and
every removed vertex has degree at most two, the result is again a forest.
Thus a tree remains a tree whenever at least one vertex survives.
Isolated vertices and leaves are allowed among the removed vertices.
If the surviving vertices are independent as well, the removed degree-two
vertices correspond bijectively to the surviving edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression

open scoped Classical

variable {V : Type} (B : SimpleGraph V) (S : Finset V)

/-- Suppressing independent vertices preserves exactly the reachability between survivors. -/
theorem reachable_iff (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    {u v : {v // v ∉ S}} : (graph B S).Reachable u v ↔ B.Reachable u.val v.val :=
  Internal.reachable_iff B S independent

/-- A connected graph remains connected when an independent set is suppressed
and at least one vertex survives. -/
theorem connected [Nonempty {v // v ∉ S}] (original : B.Connected)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v) : (graph B S).Connected :=
  Internal.connected B S original independent

variable [Fintype V]

/-- Suppressing vertices of degree at most two in a forest cannot create a cycle. -/
theorem isAcyclic (forest : B.IsAcyclic) (degree : ∀ v ∈ S, B.degree v ≤ 2) :
    (graph B S).IsAcyclic :=
  Internal.isAcyclic B S forest degree

/-- Suppressing independent vertices of degree at most two in a tree leaves a tree,
provided at least one vertex survives. -/
theorem isTree [Nonempty {v // v ∉ S}] (tree : B.IsTree)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) : (graph B S).IsTree :=
  Internal.isTree B S tree independent degree

/-- In a bipartite forest, suppressing one side of degree at most two gives
one distinct edge for each removed degree-two vertex, with its original neighbors. -/
theorem exists_connection_equiv (forest : B.IsAcyclic)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (coreIndependent : ∀ u ∉ S, ∀ v ∉ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) :
    ∃ f : (S.filter (fun v => B.degree v = 2)) ≃ (graph B S).edgeSet,
      ∀ x, ∃ u v : {v // v ∉ S}, (f x).val = s(u, v) ∧
        B.Adj u.val x.val ∧ B.Adj x.val v.val :=
  Internal.exists_connection_equiv B S forest independent coreIndependent degree

/-- The suppressed graph has exactly as many edges as there are removed degree-two
vertices, when both sides of the original forest are independent. -/
theorem edge_ncard_eq_degree_two (forest : B.IsAcyclic)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (coreIndependent : ∀ u ∉ S, ∀ v ∉ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) :
    (graph B S).edgeSet.ncard = (S.filter (fun v => B.degree v = 2)).card :=
  Internal.edge_ncard_eq_degree_two B S forest independent coreIndependent degree

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression
