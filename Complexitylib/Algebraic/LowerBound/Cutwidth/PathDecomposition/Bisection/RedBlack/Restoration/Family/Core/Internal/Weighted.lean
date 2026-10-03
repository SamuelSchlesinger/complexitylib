/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Structure
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal

/-!
# Positive witnesses from light weighted core pairs

Natural weights that dominate core-piece sizes transfer the weighted-forest
bound to a small positive witness after simultaneous restoration. The forest
version requires heavy leaves and isolated vertices and a strict average
bound. For a nontrivial tree, a total bound by `M` times one fewer than its
number of vertices also suffices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype E] [Fintype ι]
  {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι)

theorem exists_positive_of_light_core_forest (H : SimpleGraph V)
    (kept : F.deletedGraph ≤ H) (original : H ≤ B) (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    (degree : ∀ v, B.degree v ≤ d)
    (f : ι ↪ (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    [Fintype {C // C ∉ Finset.univ.image f}]
    (forest : (PathSuppression.coreGraph H F.region f).IsAcyclic)
    (w : {C // C ∉ Finset.univ.image f} → ℕ)
    (dominates : ∀ u, Fintype.card u.val ≤ w u) (M : ℕ)
    (leaves : ∀ u, (PathSuppression.coreGraph H F.region f).degree u ≤ 1 → M ≤ w u)
    (total : ∑ u, w u < M * Fintype.card {C // C ∉ Finset.univ.image f}) :
    ∃ Y, Y.card ≤ (1 + d * L) * (2 * M) ∧ Positive B R Y := by
  have leafReal (u) (hu : (PathSuppression.coreGraph H F.region f).degree u ≤ 1) :
      (M : ℝ) ≤ w u := by
    exact_mod_cast leaves u hu
  have totalReal : (∑ u, (w u : ℝ)) <
      (M : ℝ) * Fintype.card {C // C ∉ Finset.univ.image f} := by
    exact_mod_cast total
  obtain ⟨u, v, adjacent, light⟩ := WeightedTree.exists_adjacent_pair_lt_of_sum_lt
    (PathSuppression.coreGraph H F.region f) forest (fun u => (w u : ℝ)) leafReal totalReal
  have pairBound : w u + w v < 2 * M := by exact_mod_cast light
  obtain ⟨Y, _, size, positive⟩ :=
    exists_positive_of_core_adj F H kept original L d small degree f support u v adjacent
  exact ⟨Y, size.trans (Nat.mul_le_mul_left _
    ((Nat.add_le_add (dominates u) (dominates v)).trans pairBound.le)), positive⟩

theorem exists_positive_of_light_core_tree (H : SimpleGraph V)
    (kept : F.deletedGraph ≤ H) (original : H ≤ B) (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    (degree : ∀ v, B.degree v ≤ d)
    (f : ι ↪ (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    [Fintype {C // C ∉ Finset.univ.image f}]
    (tree : (PathSuppression.coreGraph H F.region f).IsTree)
    (size : 1 < Fintype.card {C // C ∉ Finset.univ.image f})
    (w : {C // C ∉ Finset.univ.image f} → ℕ)
    (dominates : ∀ u, Fintype.card u.val ≤ w u) (M : ℕ)
    (leaves : ∀ u, (PathSuppression.coreGraph H F.region f).degree u = 1 → M ≤ w u)
    (total : ∑ u, w u ≤ M * (Fintype.card {C // C ∉ Finset.univ.image f} - 1)) :
    ∃ Y, Y.card ≤ (1 + d * L) * (2 * M) ∧ Positive B R Y := by
  have leafBound (u) (hu : (PathSuppression.coreGraph H F.region f).degree u = 1) :
      ∑ v, w v ≤ (Fintype.card {C // C ∉ Finset.univ.image f} - 1) * w u := by
    calc
      ∑ v, w v ≤ M * (Fintype.card {C // C ∉ Finset.univ.image f} - 1) := total
      _ ≤ w u * (Fintype.card {C // C ∉ Finset.univ.image f} - 1) :=
        Nat.mul_le_mul_right _ (leaves u hu)
      _ = _ := Nat.mul_comm _ _
  obtain ⟨u, v, adjacent, light⟩ := WeightedTree.exists_adjacent_pair_le
    (PathSuppression.coreGraph H F.region f) tree size w leafBound
  have scaled :
      (Fintype.card {C // C ∉ Finset.univ.image f} - 1) * (w u + w v) ≤
        (Fintype.card {C // C ∉ Finset.univ.image f} - 1) * (2 * M) := by
    calc
      _ ≤ 2 * ∑ x, w x := light
      _ ≤ 2 * (M * (Fintype.card {C // C ∉ Finset.univ.image f} - 1)) :=
        Nat.mul_le_mul_left 2 total
      _ = _ := by ring
  have pairBound : w u + w v ≤ 2 * M := le_of_mul_le_mul_left scaled (by lia)
  obtain ⟨Y, _, bound, positive⟩ :=
    exists_positive_of_core_adj F H kept original L d small degree f support u v adjacent
  exact ⟨Y, bound.trans (Nat.mul_le_mul_left _
    ((Nat.add_le_add (dominates u) (dominates v)).trans pairBound)), positive⟩

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
