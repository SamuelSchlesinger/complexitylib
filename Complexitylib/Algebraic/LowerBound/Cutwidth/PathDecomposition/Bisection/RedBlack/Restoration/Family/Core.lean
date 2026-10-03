/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Regions.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.WeightedTree
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Weighted

/-!
# Small positive witnesses from the core graph

Adjacent core pieces absorb the whole boundary of their connecting region.
Restoring all incident regions and their chosen attachments therefore gives
a positive witness in the original graph. This includes boundaries deleted
before forming the core graph and charges restoration only once.

Natural weights that dominate the piece sizes can be used to find a small
pair by the weighted-tree lemma. The weight and leaf hypotheses remain
explicit; these theorems do not assert that reorganization has supplied them.
For the constructed thin family, `L = 3 M` and black degree at most three
give a witness of size at most `2 M (1 + 9 M)` from a pair of total size
at most `2 M`.

Source: Burkhard Monien and Robert Preis, *Upper bounds on the bisection
width of 3- and 4-regular graphs*, Journal of Discrete Algorithms 4 (2006),
475–498, https://doi.org/10.1016/j.jda.2005.12.009.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype E] [Fintype ι]
  {B : SimpleGraph V} {R : Multigraph V E} (F : RestorationFamily B R ι)

section Core

variable (H : SimpleGraph V) (kept : F.deletedGraph ≤ H) (original : H ≤ B) (L d : ℕ)
  (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L) (degree : ∀ v, B.degree v ≤ d)
  (f : ι ↪ (H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
  (support : ∀ i, (f i).supp.toFinset = F.region i)

include kept original small degree support

/-- An edge of the core graph gives a positive witness containing both endpoint
pieces, with simultaneous restoration charged to their total size. -/
theorem exists_positive_of_core_adj (u v : {C // C ∉ Finset.univ.image f})
    (adjacent : (PathSuppression.coreGraph H F.region f).Adj u v) :
    ∃ Y, u.val.supp.toFinset ∪ v.val.supp.toFinset ⊆ Y ∧
      Y.card ≤ (1 + d * L) * (Fintype.card u.val + Fintype.card v.val) ∧ Positive B R Y :=
  Internal.exists_positive_of_core_adj F H kept original L d small degree f support u v adjacent

variable [Fintype {C // C ∉ Finset.univ.image f}]

/-- Heavy leaves and isolated vertices, together with a light average weight,
give a small positive witness after restoring all incident regions. -/
theorem exists_positive_of_light_core_forest
    (forest : (PathSuppression.coreGraph H F.region f).IsAcyclic)
    (w : {C // C ∉ Finset.univ.image f} → ℕ)
    (dominates : ∀ u, Fintype.card u.val ≤ w u) (M : ℕ)
    (leaves : ∀ u, (PathSuppression.coreGraph H F.region f).degree u ≤ 1 → M ≤ w u)
    (total : ∑ u, w u < M * Fintype.card {C // C ∉ Finset.univ.image f}) :
    ∃ Y, Y.card ≤ (1 + d * L) * (2 * M) ∧ Positive B R Y :=
  Internal.exists_positive_of_light_core_forest F H kept original L d small degree f support
    forest w dominates M leaves total

/-- In a nontrivial core tree, leaves of weight at least `M` and total weight
at most `M (n - 1)` give a positive witness of the stated size. -/
theorem exists_positive_of_light_core_tree
    (tree : (PathSuppression.coreGraph H F.region f).IsTree)
    (size : 1 < Fintype.card {C // C ∉ Finset.univ.image f})
    (w : {C // C ∉ Finset.univ.image f} → ℕ)
    (dominates : ∀ u, Fintype.card u.val ≤ w u) (M : ℕ)
    (leaves : ∀ u, (PathSuppression.coreGraph H F.region f).degree u = 1 → M ≤ w u)
    (total : ∑ u, w u ≤ M * (Fintype.card {C // C ∉ Finset.univ.image f} - 1)) :
    ∃ Y, Y.card ≤ (1 + d * L) * (2 * M) ∧ Positive B R Y :=
  Internal.exists_positive_of_light_core_tree F H kept original L d small degree f support
    tree size w dominates M leaves total

end Core

/-- Apply core-edge restoration directly after isolating any subfamily, as in
the core forest constructed from shaded thin paths. -/
theorem exists_positive_of_restricted_core_adj (indices : Finset ι) (L d : ℕ)
    (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    (degree : ∀ v, B.degree v ≤ d)
    (f : ι ↪ ((F.restrict indices).deletedGraph.deleteEdges
      (⋃ i, ((F.restrict indices).deletedGraph.cutFinset
        (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    (u v : {C // C ∉ Finset.univ.image f})
    (adjacent : (PathSuppression.coreGraph (F.restrict indices).deletedGraph F.region f).Adj u v) :
    ∃ Y, u.val.supp.toFinset ∪ v.val.supp.toFinset ⊆ Y ∧
      Y.card ≤ (1 + d * L) * (Fintype.card u.val + Fintype.card v.val) ∧ Positive B R Y :=
  Internal.exists_positive_of_restricted_core_adj F indices L d small degree f support u v adjacent

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily
