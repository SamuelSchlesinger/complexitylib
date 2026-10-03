/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Core.Internal.Structure
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Family.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal

/-!
# Positive witnesses from adjacent core pieces

A core edge passes through a region whose two boundary edges join distinct
core components. Their union therefore absorbs the whole region boundary.
It is closed after all region cuts are deleted, even if only some cuts were
deleted before forming the core graph. Simultaneous restoration gives a
positive witness in the original graph, with one size charge per restored
region and attachment.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal

open scoped Classical

variable {V E ι : Type} [Fintype V] [Fintype ι] {B : SimpleGraph V} {R : Multigraph V E}
  (F : RestorationFamily B R ι) (H : SimpleGraph V)

private theorem exists_absorbed_core_cut (original : H ≤ B)
    (f : ι ↪ (H.deleteEdges
      (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    (u v : {C // C ∉ Finset.univ.image f})
    (adjacent : (PathSuppression.coreGraph H F.region f).Adj u v) :
    ∃ i, (B.cutFinset (F.region i)).Nonempty ∧
      B.cutFinset (F.region i) ⊆ B.cutFinset (u.val.supp.toFinset ∪ v.val.supp.toFinset) := by
  obtain ⟨different, i, ⟨_, a, ha, p, hp, ap⟩, ⟨_, q, hq, b, hb, qb⟩⟩ :=
    (core_adj_iff_exists_region F H f support u v).mp adjacent
  have hp' : p ∈ F.region i := by rw [← support]; exact Set.mem_toFinset.mpr hp
  have hq' : q ∈ F.region i := by rw [← support]; exact Set.mem_toFinset.mpr hq
  have outsideA : a ∉ F.region i :=
    Finset.disjoint_left.mp (core_disjoint_region F H f support u i)
      (Set.mem_toFinset.mpr ha)
  have outsideB : b ∉ F.region i :=
    Finset.disjoint_left.mp (core_disjoint_region F H f support v i)
      (Set.mem_toFinset.mpr hb)
  have first : s(a, p) ∈ B.cutFinset (F.region i) :=
    B.mem_cutFinset_mk.mpr ⟨original ap, Or.inr ⟨hp', outsideA⟩⟩
  have second : s(q, b) ∈ B.cutFinset (F.region i) :=
    B.mem_cutFinset_mk.mpr ⟨original qb, Or.inl ⟨hq', outsideB⟩⟩
  have distinct : s(a, p) ≠ s(q, b) := by
    intro same
    rcases Sym2.eq_iff.mp same with ⟨aq, _⟩ | ⟨ab, _⟩
    · exact outsideA (aq.symm ▸ hq')
    · exact different (Subtype.ext
        (SimpleGraph.ConnectedComponent.eq_of_common_vertex (ab ▸ ha) hb))
  have pairSubset : {s(a, p), s(q, b)} ⊆ B.cutFinset (F.region i) := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact first
    · exact second
  have boundary : B.cutFinset (F.region i) = {s(a, p), s(q, b)} :=
    (Finset.eq_of_subset_of_card_le pairSubset (by simpa [distinct] using F.boundary i)).symm
  have outsideUnion (w : V) (hw : w ∈ F.region i) :
      w ∉ u.val.supp.toFinset ∪ v.val.supp.toFinset := by
    intro member
    rcases Finset.mem_union.mp member with member | member
    · exact Finset.disjoint_left.mp (core_disjoint_region F H f support u i) member hw
    · exact Finset.disjoint_left.mp (core_disjoint_region F H f support v i) member hw
  refine ⟨i, ⟨s(a, p), first⟩, ?_⟩
  rw [boundary]
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact B.mem_cutFinset_mk.mpr ⟨original ap, Or.inl
      ⟨Finset.mem_union_left _ (Set.mem_toFinset.mpr ha), outsideUnion p hp'⟩⟩
  · exact B.mem_cutFinset_mk.mpr ⟨original qb, Or.inr
      ⟨Finset.mem_union_right _ (Set.mem_toFinset.mpr hb), outsideUnion q hq'⟩⟩

variable [Fintype E]

theorem exists_positive_of_core_adj (kept : F.deletedGraph ≤ H) (original : H ≤ B)
    (L d : ℕ) (small : ∀ i, (F.region i ∪ F.attachment i).card ≤ L)
    (degree : ∀ v, B.degree v ≤ d)
    (f : ι ↪ (H.deleteEdges
      (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))).ConnectedComponent)
    (support : ∀ i, (f i).supp.toFinset = F.region i)
    (u v : {C // C ∉ Finset.univ.image f})
    (adjacent : (PathSuppression.coreGraph H F.region f).Adj u v) :
    ∃ Y, u.val.supp.toFinset ∪ v.val.supp.toFinset ⊆ Y ∧
      Y.card ≤ (1 + d * L) * (Fintype.card u.val + Fintype.card v.val) ∧ Positive B R Y := by
  let X := u.val.supp.toFinset ∪ v.val.supp.toFinset
  let K := H.deleteEdges (⋃ i, (H.cutFinset (F.region i) : Set (Sym2 V)))
  have fresh (i : ι) : Disjoint X (F.region i) := by
    exact Finset.disjoint_union_left.mpr
      ⟨core_disjoint_region F H f support u i, core_disjoint_region F H f support v i⟩
  have closedK : K.cutFinset X = ∅ := by
    apply Finset.subset_empty.mp
    simpa only [RedBlack.Internal.cut_component_eq_empty K u.val] using
      RedBlack.Internal.cut_union_subset_of_empty K u.val.supp.toFinset
        (RedBlack.Internal.cut_component_eq_empty K v.val)
  have closed : F.deletedGraph.cutFinset X = ∅ :=
    (congrArg (fun G : SimpleGraph V => G.cutFinset X)
      (delete_region_cuts_eq F H kept original)).symm.trans closedK
  obtain ⟨i, nonempty, absorbed⟩ := exists_absorbed_core_cut F H original f support u v adjacent
  obtain ⟨Y, subset, size, positive⟩ := exists_positive_of_closed_core_of_degree F L d small fresh
    closed (fun w _ => degree w) nonempty absorbed
  have cardUnion := Finset.card_union_le u.val.supp.toFinset v.val.supp.toFinset
  simp only [Set.toFinset_card] at cardUnion
  change X.card ≤ Fintype.card u.val + Fintype.card v.val at cardUnion
  exact ⟨Y, subset, size.trans (Nat.mul_le_mul_left _ cardUnion), positive⟩

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
  exists_positive_of_core_adj F (F.restrict indices).deletedGraph
    (deletedGraph_le_restrict F indices) (SimpleGraph.deleteEdges_le _)
    L d small degree f support u v adjacent

end Algebraic.Cutwidth.Bisection.RedBlack.RestorationFamily.Internal
