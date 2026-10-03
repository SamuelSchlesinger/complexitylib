/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations

/-!
# Adding a boundary to all bags

An induced copy of a graph has a path decomposition. Add a fixed vertex set
to every bag and as both endpoint bags. If the fixed set covers the vertices
outside the copy, the enlarged bags decompose the whole graph.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

private noncomputable def padBag (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (i : Fin (D.length + 2)) : Finset W :=
  X ∪ if hi : 0 < i.val ∧ i.val ≤ D.length then
    (D.bag ⟨i.val - 1, by lia⟩).map f.toEmbedding else ∅

private theorem mem_padBag {D : PathDecomposition G} {f : G ↪g H} {X : Finset W}
    {i : Fin (D.length + 2)} {w : W} :
    w ∈ padBag D f X i ↔ w ∈ X ∨
      ∃ (hi : 0 < i.val ∧ i.val ≤ D.length) (v : V),
        v ∈ D.bag ⟨i.val - 1, by lia⟩ ∧ f v = w := by
  by_cases hi : 0 < i.val ∧ i.val ≤ D.length
  · simp only [padBag, dite_eq_left hi, Finset.mem_union, Finset.mem_map]
    constructor
    · rintro (hw | ⟨v, hv, hf⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨hi, v, hv, hf⟩
    · rintro (hw | ⟨_, v, hv, hf⟩)
      · exact Or.inl hw
      · exact Or.inr ⟨v, hv, hf⟩
  · simp only [padBag, dite_eq_right hi, Finset.union_empty]
    exact ⟨Or.inl, fun h => h.elim id (fun h => (hi h.choose).elim)⟩

private theorem padBag_middle (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (i : Fin D.length) :
    padBag D f X ⟨i.val + 1, by have := i.isLt; lia⟩ =
      X ∪ (D.bag i).map f.toEmbedding := by
  have hi : i.val + 1 ≤ D.length := i.isLt
  simp [padBag, hi]

private noncomputable def pad (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ X) : PathDecomposition H where
  length := D.length + 2
  bag := padBag D f X
  vertex_mem w := by
    rcases cover w with ⟨v, rfl⟩ | hw
    · obtain ⟨i, hi⟩ := D.vertex_mem v
      refine ⟨⟨i.val + 1, by have := i.isLt; lia⟩, ?_⟩
      rw [padBag_middle]
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v, hi, rfl⟩)
    · exact ⟨⟨0, by lia⟩, mem_padBag.mpr (Or.inl hw)⟩
  edge_mem u v hadj := by
    rcases cover u with ⟨u, rfl⟩ | hu <;> rcases cover v with ⟨v, rfl⟩ | hv
    · obtain ⟨i, hiu, hiv⟩ := D.edge_mem u v (f.map_adj_iff.mp hadj)
      refine ⟨⟨i.val + 1, by have := i.isLt; lia⟩, ?_, ?_⟩
      · rw [padBag_middle]
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨u, hiu, rfl⟩)
      · rw [padBag_middle]
        exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v, hiv, rfl⟩)
    · obtain ⟨i, hi⟩ := D.vertex_mem u
      refine ⟨⟨i.val + 1, by have := i.isLt; lia⟩, ?_, mem_padBag.mpr (Or.inl hv)⟩
      rw [padBag_middle]
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨u, hi, rfl⟩)
    · obtain ⟨i, hi⟩ := D.vertex_mem v
      refine ⟨⟨i.val + 1, by have := i.isLt; lia⟩, mem_padBag.mpr (Or.inl hu), ?_⟩
      rw [padBag_middle]
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨v, hi, rfl⟩)
    · exact ⟨⟨0, by lia⟩, mem_padBag.mpr (Or.inl hu), mem_padBag.mpr (Or.inl hv)⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hw : w ∈ X
    · exact mem_padBag.mpr (Or.inl hw)
    · obtain ⟨hi, u, hui, hu⟩ := (mem_padBag.mp hwi).resolve_left hw
      obtain ⟨hk, v, hvk, hv⟩ := (mem_padBag.mp hwk).resolve_left hw
      have huv : u = v := f.injective (hu.trans hv.symm)
      subst v
      have hj : 0 < j.val ∧ j.val ≤ D.length :=
        ⟨lt_of_lt_of_le hi.1 hij, le_trans hjk hk.2⟩
      refine mem_padBag.mpr (Or.inr ⟨hj, u, ?_, hu⟩)
      exact D.consecutive u _ _ _ (Nat.sub_le_sub_right hij _)
        (Nat.sub_le_sub_right hjk _) hui hvk

theorem exists_pad (D : PathDecomposition G) (f : G ↪g H) (X : Finset W)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ X) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ E : PathDecomposition H, E.StartsAt X ∧ E.EndsAt X ∧
      ∀ i, (E.bag i).card ≤ X.card + b := by
  refine ⟨pad D f X cover, ?_, ?_, ?_⟩
  · exact ⟨⟨0, by simp [pad]⟩, fun _ => Nat.zero_le _, by simp [pad, padBag]⟩
  · refine ⟨⟨D.length + 1, by simp [pad]⟩, ?_, by simp [pad, padBag]⟩
    intro i
    have hi := i.isLt
    change i.val < D.length + 2 at hi
    change i.val ≤ D.length + 1
    lia
  · intro i
    change (padBag D f X i).card ≤ X.card + b
    unfold padBag
    apply (Finset.card_union_le _ _).trans
    split
    · simpa only [Finset.card_map] using Nat.add_le_add_left (bound _) X.card
    · simp

end Algebraic.Cutwidth.PathDecomposition.Internal
