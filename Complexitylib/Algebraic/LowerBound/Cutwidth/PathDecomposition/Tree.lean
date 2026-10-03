/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Nat.Log
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree.Internal

/-!
# Logarithmic-width decompositions of trees

Repeatedly deleting a centroid gives bags of size at most `⌈log₂ n⌉ + 1`.
This elementary bound suffices for the tree component in Fomin and Høie's
endpoint induction; their sharper logarithmic term is not needed for the
asymptotic coefficient `1/6` in the cubic-graph pathwidth bound.
-/

@[expose] public section

namespace Algebraic.Cutwidth

open scoped Classical

/-- A finite tree has a vertex whose deletion leaves components of size
at most half the original tree. -/
theorem exists_tree_centroid {W : Type} [Fintype W] {H : SimpleGraph W} (tree : H.IsTree) :
    ∃ r : W, ∀ C : (H.induce {w | w ≠ r}).ConnectedComponent,
      2 * Fintype.card C ≤ Fintype.card W :=
  PathDecomposition.Internal.exists_tree_centroid tree

/-- Trees with at most `2 ^ k` vertices admit bags of size at most `k + 1`. -/
theorem PathDecomposition.exists_tree_of_card_le_pow {W : Type} [Fintype W]
    {H : SimpleGraph W} (tree : H.IsTree) {k : Nat} (hcard : Fintype.card W ≤ 2 ^ k) :
    ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ k + 1 :=
  Internal.exists_tree_decomposition_of_card_le_pow k W H tree hcard

/-- A finite tree has pathwidth at most the ceiling of its base-two logarithm. -/
theorem PathDecomposition.exists_tree {W : Type} [Fintype W]
    {H : SimpleGraph W} (tree : H.IsTree) :
    ∃ D : PathDecomposition H,
      ∀ i, (D.bag i).card ≤ Nat.clog 2 (Fintype.card W) + 1 :=
  Internal.exists_tree_decomposition tree

/-- The logarithmic tree bound extends to every finite acyclic graph. -/
theorem PathDecomposition.exists_forest {W : Type} [Fintype W]
    {H : SimpleGraph W} (forest : H.IsAcyclic) :
    ∃ D : PathDecomposition H,
      ∀ i, (D.bag i).card ≤ Nat.clog 2 (Fintype.card W) + 1 :=
  Internal.exists_forest_decomposition forest

end Algebraic.Cutwidth
