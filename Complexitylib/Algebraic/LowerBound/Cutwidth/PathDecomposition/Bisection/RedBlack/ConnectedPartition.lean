/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.ConnectedPartition.Internal

/-!
# Bounded connected partitions of subcubic graphs

A connected subcubic graph on more than `M` vertices can be partitioned
into connected pieces of size at most `3 M`, with at most `2 n / M`
pieces. The proof recursively removes a root, partitions the resulting
components, and joins their small remainders through the root.

This supplies the bounded pieces used by the red/black density argument
in `RedBlack.Clusters`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition

open scoped Classical

/-- Partition a connected subcubic graph into disjoint connected sets of
at most `3 M` vertices. Their number is at most `2 n / M`, with the
positive denominator cleared. -/
theorem exists_partition {V : Type} [Fintype V] (B : SimpleGraph V)
    (connected : B.Connected) (degree : ∀ v, B.degree v ≤ 3)
    (M : Nat) (positive : 0 < M) (large : M < Fintype.card V) :
    ∃ parts : Finset (Finset V), parts.biUnion id = Finset.univ ∧
      (parts : Set (Finset V)).Pairwise Disjoint ∧
      (∀ P ∈ parts, (B.induce {v | v ∈ P}).Connected ∧ P.card ≤ 3 * M) ∧
      M * parts.card ≤ 2 * Fintype.card V :=
  Internal.exists_partition B connected degree M positive large

end Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition
