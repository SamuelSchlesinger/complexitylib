/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Prescribed endpoint bags

`PathDecomposition.EndsAt` specifies the last bag, including the requirement
that the decomposition has at least one bag. It is used in the induction for
Fomin and Høie's endpoint-prescribed decomposition lemma. `StartsAt` specifies
the first bag; reversing the order of bags exchanges the two endpoints.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

/-- The decomposition has a last bag, and that bag is exactly `X`. -/
def EndsAt (D : PathDecomposition H) (X : Finset W) : Prop :=
  ∃ last : Fin D.length, (∀ i, i ≤ last) ∧ D.bag last = X

/-- The decomposition has a first bag, and that bag is exactly `X`. -/
def StartsAt (D : PathDecomposition H) (X : Finset W) : Prop :=
  ∃ first : Fin D.length, (∀ i, first ≤ i) ∧ D.bag first = X

/-- Reverse the order of all bags. -/
def reverse (D : PathDecomposition H) : PathDecomposition H where
  length := D.length
  bag i := D.bag i.rev
  vertex_mem w := by
    obtain ⟨i, hi⟩ := D.vertex_mem w
    exact ⟨i.rev, by simpa only [Fin.rev_rev] using hi⟩
  edge_mem u v hadj := by
    obtain ⟨i, hu, hv⟩ := D.edge_mem u v hadj
    exact ⟨i.rev, by simpa only [Fin.rev_rev] using hu,
      by simpa only [Fin.rev_rev] using hv⟩
  consecutive w i j k hij hjk hwi hwk :=
    D.consecutive w k.rev j.rev i.rev (Fin.rev_le_rev.mpr hjk)
      (Fin.rev_le_rev.mpr hij) hwk hwi

/-- Relabel vertices along a graph isomorphism, preserving the bag indices. -/
noncomputable def relabel {V : Type} {G : SimpleGraph V}
    (D : PathDecomposition G) (e : G ≃g H) : PathDecomposition H where
  length := D.length
  bag i := (D.bag i).map e.toEquiv.toEmbedding
  vertex_mem w := by
    obtain ⟨i, hi⟩ := D.vertex_mem (e.symm w)
    exact ⟨i, Finset.mem_map.mpr ⟨e.symm w, hi, e.apply_symm_apply w⟩⟩
  edge_mem u v hadj := by
    obtain ⟨i, hu, hv⟩ := D.edge_mem (e.symm u) (e.symm v) (e.symm.map_adj_iff.mpr hadj)
    exact ⟨i, Finset.mem_map.mpr ⟨e.symm u, hu, e.apply_symm_apply u⟩,
      Finset.mem_map.mpr ⟨e.symm v, hv, e.apply_symm_apply v⟩⟩
  consecutive w i j k hij hjk hwi hwk := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hwi
    obtain ⟨v, hv, h⟩ := Finset.mem_map.mp hwk
    have hvu : v = u := e.injective h
    subst v
    exact Finset.mem_map.mpr ⟨u, D.consecutive u i j k hij hjk hu hv, rfl⟩

end Algebraic.Cutwidth.PathDecomposition
