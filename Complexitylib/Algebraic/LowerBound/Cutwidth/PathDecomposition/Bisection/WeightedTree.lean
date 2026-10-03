/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree.Internal

/-!
# Light adjacent pairs in weighted trees

Monien and Preis's red/black argument contracts parts of a black component
to a weighted tree. When all its leaves are sufficiently heavy, a light
adjacent pair gives the next small candidate for a positive set.

We prove their weighted-tree lemma through a forest inequality: nonnegative
weights at leaves and isolated vertices, together with nonnegative sums
across edges, force a nonnegative total. Shifting weights by a threshold
then gives a light adjacent pair whenever the total lies below that threshold
times the number of vertices. `RedBlack.Restoration` handles one local
edge-restoration step; the global tree reorganization remains unproved.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.WeightedTree

open scoped Classical

/-- A finite forest has nonnegative total weight if its leaves and isolated
vertices have nonnegative weight and every edge has nonnegative endpoint sum. -/
theorem sum_nonneg_of_leaf_nonneg {W : Type} [Fintype W] (H : SimpleGraph W)
    (forest : H.IsAcyclic) (w : W → ℝ)
    (leaves : ∀ v, H.degree v ≤ 1 → 0 ≤ w v)
    (edges : ∀ u v, H.Adj u v → 0 ≤ w u + w v) : 0 ≤ ∑ v, w v :=
  Internal.sum_nonneg_of_leaf_nonneg H forest w leaves edges

/-- If leaves and isolated vertices weigh at least `A`, but the average
weight is below `A`, some adjacent pair weighs less than `2 A`. -/
theorem exists_adjacent_pair_lt_of_sum_lt {W : Type} [Fintype W] (H : SimpleGraph W)
    (forest : H.IsAcyclic) (w : W → ℝ) {A : ℝ}
    (leaves : ∀ v, H.degree v ≤ 1 → A ≤ w v)
    (total : ∑ v, w v < A * Fintype.card W) :
    ∃ u v, H.Adj u v ∧ w u + w v < 2 * A :=
  Internal.exists_adjacent_pair_lt_of_sum_lt H forest w leaves total

/-- Monien and Preis's weighted-tree lemma, with denominators cleared.
In a tree on `n ≥ 2` vertices, if every leaf weighs at least the total
weight divided by `n - 1`, some adjacent pair weighs at most twice that ratio. -/
theorem exists_adjacent_pair_le {W : Type} [Fintype W] (H : SimpleGraph W)
    (tree : H.IsTree) (size : 1 < Fintype.card W) (w : W → Nat)
    (leaves : ∀ v, H.degree v = 1 → ∑ x, w x ≤ (Fintype.card W - 1) * w v) :
    ∃ u v, H.Adj u v ∧ (Fintype.card W - 1) * (w u + w v) ≤ 2 * ∑ x, w x :=
  Internal.exists_adjacent_pair_le H tree size w leaves

end Algebraic.Cutwidth.Bisection.WeightedTree
