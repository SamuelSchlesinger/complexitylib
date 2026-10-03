/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Sigma.Order

/-!
# Joining decompositions of connected components

Order the components arbitrarily, put each component's bags in a consecutive
block, and enumerate that finite linear order by `Fin`. No bag grows.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

theorem exists_of_ordered_bags {I : Type} [Fintype I] [LinearOrder I]
    (bag : I → Finset W) (vertices : ∀ w, ∃ i, w ∈ bag i)
    (edges : ∀ u v, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i)
    (intervals : ∀ w (i j k : I), i ≤ j → j ≤ k → w ∈ bag i → w ∈ bag k → w ∈ bag j)
    {b : Nat} (bound : ∀ i, (bag i).card ≤ b) :
    ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ b := by
  let e := Fintype.orderIsoFinOfCardEq I rfl
  refine ⟨⟨Fintype.card I, fun i => bag (e i), ?_, ?_, ?_⟩, fun i => bound (e i)⟩
  · intro w
    obtain ⟨i, hi⟩ := vertices w
    exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hi⟩
  · intro u v hadj
    obtain ⟨i, hu, hv⟩ := edges u v hadj
    exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using hu,
      by simpa only [e.apply_symm_apply] using hv⟩
  · intro w i j k hij hjk hwi hwk
    exact intervals w (e i) (e j) (e k) (e.monotone hij) (e.monotone hjk) hwi hwk

private theorem lex_fst_le {ι : Type} [LinearOrder ι] {β : ι → Type}
    [∀ i, LinearOrder (β i)] {i j : Σₗ c, β c} (h : i ≤ j) : i.1 ≤ j.1 := by
  rcases Sigma.Lex.le_def.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact le_of_eq h

private theorem lex_snd_le {ι : Type} [LinearOrder ι] {β : ι → Type}
    [∀ i, LinearOrder (β i)] {i : ι} {a b : β i}
    (h : toLex (⟨i, a⟩ : Σ c, β c) ≤ toLex ⟨i, b⟩) : a ≤ b := by
  rcases Sigma.Lex.le_def.mp h with h | ⟨_, h⟩
  · exact (lt_irrefl _ h).elim
  · exact h

theorem exists_of_components [Fintype W] {b : Nat}
    (parts : ∀ C : H.ConnectedComponent,
      ∃ D : PathDecomposition C.toSimpleGraph, ∀ i, (D.bag i).card ≤ b) :
    ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ b := by
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let : LinearOrder H.ConnectedComponent :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  choose D bound using parts
  let I := Σₗ C : H.ConnectedComponent, Fin (D C).length
  let bags (i : I) : Finset W := (D i.1).bag i.2 |>.map (.subtype (· ∈ i.1.supp))
  have member (w : W) (i : I) : w ∈ bags i ↔
      ∃ hw : w ∈ i.1.supp, (⟨w, hw⟩ : i.1) ∈ (D i.1).bag i.2 := by
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
      exact ⟨v.property, hv⟩
    · rintro ⟨hw, hv⟩
      exact Finset.mem_map.mpr ⟨⟨w, hw⟩, hv, rfl⟩
  apply exists_of_ordered_bags bags
  · intro w
    let C := H.connectedComponentMk w
    obtain ⟨i, hi⟩ := (D C).vertex_mem ⟨w, rfl⟩
    exact ⟨⟨C, i⟩, (member w _).mpr ⟨rfl, hi⟩⟩
  · intro u v hadj
    let C := H.connectedComponentMk u
    have hu : u ∈ C.supp := rfl
    have hv : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hu hadj
    obtain ⟨i, hiu, hiv⟩ := (D C).edge_mem ⟨u, hu⟩ ⟨v, hv⟩ hadj
    exact ⟨⟨C, i⟩, (member u _).mpr ⟨hu, hiu⟩, (member v _).mpr ⟨hv, hiv⟩⟩
  · rintro w ⟨Ci, i⟩ ⟨Cj, j⟩ ⟨Ck, k⟩ hij hjk hwi hwk
    obtain ⟨hiC, hwi⟩ := (member w _).mp hwi
    obtain ⟨hkC, hwk⟩ := (member w _).mp hwk
    change H.connectedComponentMk w = Ci at hiC
    change H.connectedComponentMk w = Ck at hkC
    subst Ci Ck
    have hji : Cj = H.connectedComponentMk w :=
      le_antisymm (lex_fst_le hjk) (lex_fst_le hij)
    subst Cj
    exact (member w _).mpr ⟨rfl, (D _).consecutive ⟨w, rfl⟩ i j k
      (lex_snd_le (β := fun C => Fin (D C).length) hij)
      (lex_snd_le (β := fun C => Fin (D C).length) hjk) hwi hwk⟩
  · rintro ⟨C, i⟩
    simpa only [bags, Finset.card_map] using bound C i

end Algebraic.Cutwidth.PathDecomposition.Internal
