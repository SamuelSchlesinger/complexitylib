/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Data.Finset.Prod

/-!
# Proof of the boundary transition lemma

Scan the left side of a cut, introducing each vertex's right neighbors before
forgetting it. Charge every bag vertex except the vertex being forgotten to
a distinct crossing edge. This is the middle decomposition in Fomin and
Høie's proof of their cubic-graph pathwidth theorem (Theorem 5, 2006).
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W) (S : Finset W)

private noncomputable def crossingPairs : Finset (W × W) :=
  (S ×ˢ Sᶜ).filter fun uv => H.Adj uv.1 uv.2

private theorem mem_crossingPairs {u v : W} :
    (u, v) ∈ crossingPairs H S ↔ u ∈ S ∧ v ∉ S ∧ H.Adj u v := by
  simp only [crossingPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_compl]
  tauto

private theorem card_crossingPairs :
    (crossingPairs H S).card = (H.cutFinset S).card := by
  apply Finset.card_bij (fun uv _ => s(uv.1, uv.2))
  · intro uv huv
    obtain ⟨hu, hv, hadj⟩ := (mem_crossingPairs H S).mp huv
    exact H.mem_cutFinset_mk.mpr ⟨hadj, Or.inl ⟨hu, hv⟩⟩
  · intro uv huv xy hxy heq
    obtain ⟨hu, hv, _⟩ := (mem_crossingPairs H S).mp huv
    obtain ⟨hx, hy, _⟩ := (mem_crossingPairs H S).mp hxy
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Prod.ext h.1 h.2
    · exact False.elim (hy (h.1 ▸ hu))
  · intro e he
    obtain ⟨hadj, u, v, rfl, hu, hv⟩ := H.mem_cutFinset.mp he
    exact ⟨(u, v), (mem_crossingPairs H S).mpr ⟨hu, hv, hadj⟩, rfl⟩

private noncomputable def rank (v : W) : Nat := (Fintype.equivFin W v).val

private theorem rank_lt (v : W) : rank v < Fintype.card W :=
  (Fintype.equivFin W v).isLt

private theorem rank_injective : Function.Injective (rank (W := W)) := by
  intro u v h
  exact (Fintype.equivFin W).injective (Fin.ext h)

private noncomputable def leftBag (i : Nat) : Finset W :=
  S.filter fun v => i ≤ rank v + 1

private noncomputable def rightBag (i : Nat) : Finset W :=
  Sᶜ.filter fun v => ∃ u ∈ S, H.Adj u v ∧ rank u + 1 ≤ i

private noncomputable def transitionBag (i : Nat) : Finset W :=
  leftBag S i ∪ rightBag H S i

private theorem mem_transitionBag {i : Nat} {v : W} :
    v ∈ transitionBag H S i ↔
      (v ∈ S ∧ i ≤ rank v + 1) ∨
        (v ∉ S ∧ ∃ u ∈ S, H.Adj u v ∧ rank u + 1 ≤ i) := by
  simp [transitionBag, leftBag, rightBag]

private theorem transitionBag_zero : transitionBag H S 0 = S := by
  ext v
  simp [mem_transitionBag]

private theorem transitionBag_last
    (right : ∀ v ∉ S, ∃ u ∈ S, H.Adj u v) :
    transitionBag H S (Fintype.card W + 1) = Sᶜ := by
  ext v
  rw [mem_transitionBag, Finset.mem_compl]
  have hv := rank_lt v
  constructor
  · rintro (⟨_, hi⟩ | ⟨hvS, _⟩)
    · lia
    · exact hvS
  · intro hvS
    obtain ⟨u, hu, hadj⟩ := right v hvS
    exact Or.inr ⟨hvS, u, hu, hadj, by have := rank_lt u; lia⟩

private noncomputable def transition
    (right : ∀ v ∉ S, ∃ u ∈ S, H.Adj u v) : PathDecomposition H where
  length := Fintype.card W + 2
  bag i := transitionBag H S i.val
  vertex_mem v := by
    by_cases hv : v ∈ S
    · exact ⟨⟨0, by lia⟩, (transitionBag_zero H S).symm ▸ hv⟩
    · exact ⟨⟨Fintype.card W + 1, by lia⟩,
        (transitionBag_last H S right).symm ▸ Finset.mem_compl.mpr hv⟩
  edge_mem u v hadj := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact ⟨⟨0, by lia⟩, (transitionBag_zero H S).symm ▸ hu,
        (transitionBag_zero H S).symm ▸ hv⟩
    · refine ⟨⟨rank u + 1, by have := rank_lt u; lia⟩,
        (mem_transitionBag H S).mpr (Or.inl ⟨hu, le_rfl⟩), ?_⟩
      exact (mem_transitionBag H S).mpr (Or.inr ⟨hv, u, hu, hadj, le_rfl⟩)
    · refine ⟨⟨rank v + 1, by have := rank_lt v; lia⟩, ?_,
        (mem_transitionBag H S).mpr (Or.inl ⟨hv, le_rfl⟩)⟩
      exact (mem_transitionBag H S).mpr (Or.inr ⟨hu, v, hv, hadj.symm, le_rfl⟩)
    · exact ⟨⟨Fintype.card W + 1, by lia⟩,
        (transitionBag_last H S right).symm ▸ Finset.mem_compl.mpr hu,
        (transitionBag_last H S right).symm ▸ Finset.mem_compl.mpr hv⟩
  consecutive v i j k hij hjk hvi hvk := by
    rw [mem_transitionBag] at hvi hvk ⊢
    rcases hvi with ⟨hv, _⟩ | ⟨hv, u, hu, hadj, hi⟩
    · rcases hvk with ⟨_, hk⟩ | ⟨h, _⟩
      · exact Or.inl ⟨hv, Nat.le_trans hjk hk⟩
      · exact (h hv).elim
    · exact Or.inr ⟨hv, u, hu, hadj, Nat.le_trans hi hij⟩

private theorem card_transitionBag_le (i : Nat)
    (left : ∀ u ∈ S, ∃ v ∉ S, H.Adj u v) :
    (transitionBag H S i).card ≤ (H.cutFinset S).card + 1 := by
  let E := crossingPairs H S
  let high := E.filter fun uv => i < rank uv.1 + 1
  let low := E.filter fun uv => ¬ i < rank uv.1 + 1
  let active := Finset.univ.filter fun v : W => rank v + 1 = i
  have hactive : active.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    apply rank_injective
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    lia
  have hleft : leftBag S i ⊆ high.image Prod.fst ∪ active := by
    intro u hu
    obtain ⟨huS, hi⟩ := Finset.mem_filter.mp hu
    by_cases heq : rank u + 1 = i
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    · obtain ⟨v, hv, hadj⟩ := left u huS
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨(u, v), Finset.mem_filter.mpr
        ⟨(mem_crossingPairs H S).mpr ⟨huS, hv, hadj⟩, by lia⟩, rfl⟩
  have hright : rightBag H S i ⊆ low.image Prod.snd := by
    intro v hv
    obtain ⟨hvS, u, huS, hadj, hi⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_image.mpr
    exact ⟨(u, v), Finset.mem_filter.mpr
      ⟨(mem_crossingPairs H S).mpr ⟨huS, Finset.mem_compl.mp hvS, hadj⟩, by lia⟩, rfl⟩
  have hl : (leftBag S i).card ≤ high.card + 1 :=
    (Finset.card_le_card hleft).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_image_le hactive))
  have hr : (rightBag H S i).card ≤ low.card :=
    (Finset.card_le_card hright).trans Finset.card_image_le
  have he : high.card + low.card = (H.cutFinset S).card := by
    rw [← card_crossingPairs H S]
    exact Finset.card_filter_add_card_filter_not _
  have hb := Finset.card_union_le (leftBag S i) (rightBag H S i)
  change (leftBag S i ∪ rightBag H S i).card ≤ _
  lia

theorem exists_boundaryTransition
    (left : ∀ u ∈ S, ∃ v ∉ S, H.Adj u v)
    (right : ∀ v ∉ S, ∃ u ∈ S, H.Adj u v) :
    ∃ (D : PathDecomposition H) (first last : Fin D.length),
      (∀ i, first ≤ i ∧ i ≤ last) ∧ D.bag first = S ∧ D.bag last = Sᶜ ∧
        ∀ i, (D.bag i).card ≤ (H.cutFinset S).card + 1 := by
  refine ⟨transition H S right, ⟨0, by simp [transition]⟩,
    ⟨Fintype.card W + 1, by simp [transition]⟩, ?_,
    transitionBag_zero H S, transitionBag_last H S right, ?_⟩
  · intro i
    constructor
    · exact Nat.zero_le _
    · have := i.isLt
      change i.val ≤ Fintype.card W + 1
      change i.val < Fintype.card W + 2 at this
      lia
  · exact fun i => card_transitionBag_le H S i.val left

end Algebraic.Cutwidth.PathDecomposition.Internal
