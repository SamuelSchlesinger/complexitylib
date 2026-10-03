/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations.Defs

/-!
# Endpoint operations for path decompositions

Appending a subset of the last bag preserves the interval property. A vertex
deleted from the graph can be restored in a new last bag when that bag already
contains all its neighbors. These are the deletion steps in Fomin and Høie's
endpoint decomposition argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} {H : SimpleGraph W}

private noncomputable def appendBag (D : PathDecomposition H) (X : Finset W)
    (i : Fin (D.length + 1)) : Finset W :=
  if hi : i.val < D.length then D.bag ⟨i.val, hi⟩ else X

private noncomputable def appendSubset (D : PathDecomposition H) (last : Fin D.length)
    (hlast : ∀ i, i ≤ last) (X : Finset W) (hX : X ⊆ D.bag last) :
    PathDecomposition H where
  length := D.length + 1
  bag := appendBag D X
  vertex_mem w := by
    obtain ⟨i, hi⟩ := D.vertex_mem w
    exact ⟨i.castSucc, by simpa [appendBag, i.isLt] using hi⟩
  edge_mem u v hadj := by
    obtain ⟨i, hu, hv⟩ := D.edge_mem u v hadj
    exact ⟨i.castSucc, by simpa [appendBag, i.isLt] using hu,
      by simpa [appendBag, i.isLt] using hv⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hk : k.val < D.length
    · have hj : j.val < D.length := Nat.lt_of_le_of_lt hjk hk
      have hi : i.val < D.length := Nat.lt_of_le_of_lt hij hj
      simp only [appendBag, dite_eq_left hi, dite_eq_left hk] at hwi hwk
      simp only [appendBag, dite_eq_left hj]
      exact D.consecutive w ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk hwi hwk
    · simp only [appendBag, dite_eq_right hk] at hwk
      by_cases hj : j.val < D.length
      · have hi : i.val < D.length := Nat.lt_of_le_of_lt hij hj
        simp only [appendBag, dite_eq_left hi] at hwi
        simp only [appendBag, dite_eq_left hj]
        exact D.consecutive w ⟨i.val, hi⟩ ⟨j.val, hj⟩ last hij (hlast _) hwi (hX hwk)
      · simpa only [appendBag, dite_eq_right hj] using hwk

theorem exists_endsAt_subset (D : PathDecomposition H) {X Y : Finset W}
    (hend : D.EndsAt Y) (hXY : X ⊆ Y) {b : Nat}
    (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b := by
  obtain ⟨last, hlast, hY⟩ := hend
  have hX : X ⊆ D.bag last := hY.symm ▸ hXY
  refine ⟨appendSubset D last hlast X hX, ?_, ?_⟩
  · refine ⟨⟨D.length, by simp [appendSubset]⟩, ?_, ?_⟩
    · intro i
      have hi := i.isLt
      change i.val < D.length + 1 at hi
      change i.val ≤ D.length
      lia
    · simp [appendSubset, appendBag]
  · intro i
    change (appendBag D X i).card ≤ b
    unfold appendBag
    split
    · exact bound _
    · exact (Finset.card_le_card hX).trans (bound last)

private noncomputable def liftBag (v : W) (Y : Finset {w : W // w ≠ v}) : Finset W :=
  Y.map (.subtype (· ≠ v))

private theorem mem_liftBag {v w : W} {Y : Finset {w : W // w ≠ v}} :
    w ∈ liftBag v Y ↔ ∃ h : w ≠ v, ⟨w, h⟩ ∈ Y := by
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    exact ⟨u.property, hu⟩
  · rintro ⟨h, hw⟩
    exact Finset.mem_map.mpr ⟨⟨w, h⟩, hw, rfl⟩

private noncomputable def restoreBag (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v})) (last : Fin D.length)
    (i : Fin (D.length + 1)) : Finset W :=
  if hi : i.val < D.length then liftBag v (D.bag ⟨i.val, hi⟩)
  else insert v (liftBag v (D.bag last))

private noncomputable def restoreVertex (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v})) (last : Fin D.length)
    (hlast : ∀ i, i ≤ last)
    (neighbors : ∀ w, H.Adj v w → w ∈ liftBag v (D.bag last)) :
    PathDecomposition H where
  length := D.length + 1
  bag := restoreBag v D last
  vertex_mem w := by
    by_cases hw : w = v
    · subst w
      exact ⟨⟨D.length, by lia⟩, by simp [restoreBag]⟩
    · obtain ⟨i, hi⟩ := D.vertex_mem ⟨w, hw⟩
      refine ⟨i.castSucc, ?_⟩
      simp only [restoreBag, Fin.val_castSucc, dite_eq_left i.isLt]
      exact mem_liftBag.mpr ⟨hw, hi⟩
  edge_mem u w hadj := by
    by_cases hu : u = v
    · subst u
      exact ⟨⟨D.length, by lia⟩, by simp [restoreBag],
        by simpa [restoreBag] using Finset.mem_insert_of_mem (neighbors w hadj)⟩
    · by_cases hw : w = v
      · subst w
        exact ⟨⟨D.length, by lia⟩,
          by simpa [restoreBag] using Finset.mem_insert_of_mem (neighbors u hadj.symm),
          by simp [restoreBag]⟩
      · obtain ⟨i, hiu, hiw⟩ := D.edge_mem ⟨u, hu⟩ ⟨w, hw⟩ hadj
        refine ⟨i.castSucc, ?_, ?_⟩
        · simp only [restoreBag, Fin.val_castSucc, dite_eq_left i.isLt]
          exact mem_liftBag.mpr ⟨hu, hiu⟩
        · simp only [restoreBag, Fin.val_castSucc, dite_eq_left i.isLt]
          exact mem_liftBag.mpr ⟨hw, hiw⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hk : k.val < D.length
    · have hj : j.val < D.length := Nat.lt_of_le_of_lt hjk hk
      have hi : i.val < D.length := Nat.lt_of_le_of_lt hij hj
      simp only [restoreBag, dite_eq_left hi, dite_eq_left hk] at hwi hwk
      obtain ⟨hw, hwi⟩ := mem_liftBag.mp hwi
      obtain ⟨_, hwk⟩ := mem_liftBag.mp hwk
      simp only [restoreBag, dite_eq_left hj]
      exact mem_liftBag.mpr ⟨hw,
        D.consecutive ⟨w, hw⟩ ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk hwi hwk⟩
    · simp only [restoreBag, dite_eq_right hk] at hwk
      by_cases hj : j.val < D.length
      · have hi : i.val < D.length := Nat.lt_of_le_of_lt hij hj
        simp only [restoreBag, dite_eq_left hi] at hwi
        obtain ⟨hw, hwi⟩ := mem_liftBag.mp hwi
        have hwlast := (Finset.mem_insert.mp hwk).resolve_left hw
        obtain ⟨_, hwlast⟩ := mem_liftBag.mp hwlast
        simp only [restoreBag, dite_eq_left hj]
        exact mem_liftBag.mpr ⟨hw,
          D.consecutive ⟨w, hw⟩ ⟨i.val, hi⟩ ⟨j.val, hj⟩ last hij (hlast _) hwi hwlast⟩
      · simpa only [restoreBag, dite_eq_right hj] using hwk

theorem exists_restoreVertex (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    {Y : Finset {w : W // w ≠ v}} (hend : D.EndsAt Y)
    (neighbors : ∀ w, H.Adj v w → w ∈ Y.map (.subtype (· ≠ v)))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card + 1 ≤ b) :
    ∃ D' : PathDecomposition H,
      D'.EndsAt (insert v (Y.map (.subtype (· ≠ v)))) ∧
        ∀ i, (D'.bag i).card ≤ b := by
  obtain ⟨last, hlast, rfl⟩ := hend
  refine ⟨restoreVertex v D last hlast neighbors, ?_, ?_⟩
  · refine ⟨⟨D.length, by simp [restoreVertex]⟩, ?_, ?_⟩
    · intro i
      have hi := i.isLt
      change i.val < D.length + 1 at hi
      change i.val ≤ D.length
      lia
    · simp [restoreVertex, restoreBag, liftBag]
  · intro i
    change (restoreBag v D last i).card ≤ b
    unfold restoreBag
    split
    · simpa only [liftBag, Finset.card_map] using bound _
    · exact (Finset.card_insert_le _ _).trans (by simpa only [liftBag, Finset.card_map] using hY)

theorem exists_endsAt_of_delete (v : W) {X Y : Finset W} (hv : v ∈ Y)
    (D : PathDecomposition (H.induce {w | w ≠ v}))
    (hend : D.EndsAt (Y.subtype (· ≠ v)))
    (neighbors : ∀ w, H.Adj v w → w ∈ Y) (hXY : X ⊆ Y)
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) (hY : Y.card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt X ∧ ∀ i, (D'.bag i).card ≤ b := by
  have hmap : (Y.subtype (· ≠ v)).map (.subtype (· ≠ v)) = Y.erase v := by
    rw [Finset.subtype_map]
    ext w
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  have card : (Y.subtype (· ≠ v)).card + 1 ≤ b := by
    rw [← Finset.card_map (.subtype (· ≠ v)), hmap, Finset.card_erase_add_one hv]
    exact hY
  have adjacent (w : W) (hadj : H.Adj v w) :
      w ∈ (Y.subtype (· ≠ v)).map (.subtype (· ≠ v)) := by
    rw [hmap]
    exact Finset.mem_erase.mpr ⟨hadj.ne.symm, neighbors w hadj⟩
  obtain ⟨D', end', bound'⟩ := exists_restoreVertex v D hend adjacent bound card
  rw [hmap, Finset.insert_erase hv] at end'
  exact exists_endsAt_subset D' end' hXY bound'

private noncomputable def addVertexBag (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v})) (i : Fin (D.length + 1)) : Finset W :=
  insert v (if hi : i.val < D.length then liftBag v (D.bag ⟨i.val, hi⟩) else ∅)

private theorem mem_addVertexBag {v w : W}
    {D : PathDecomposition (H.induce {w | w ≠ v})} {i : Fin (D.length + 1)} :
    w ∈ addVertexBag v D i ↔ w = v ∨
      ∃ (hi : i.val < D.length) (hw : w ≠ v), ⟨w, hw⟩ ∈ D.bag ⟨i.val, hi⟩ := by
  by_cases hi : i.val < D.length <;> simp [addVertexBag, hi, mem_liftBag]

private noncomputable def addVertex (v : W)
    (D : PathDecomposition (H.induce {w | w ≠ v})) : PathDecomposition H where
  length := D.length + 1
  bag := addVertexBag v D
  vertex_mem w := by
    by_cases hw : w = v
    · exact ⟨⟨D.length, by lia⟩, mem_addVertexBag.mpr (Or.inl hw)⟩
    · obtain ⟨i, hi⟩ := D.vertex_mem ⟨w, hw⟩
      exact ⟨i.castSucc, mem_addVertexBag.mpr (Or.inr ⟨i.isLt, hw, hi⟩)⟩
  edge_mem u w hadj := by
    by_cases hu : u = v
    · subst u
      have hw : w ≠ v := hadj.ne.symm
      obtain ⟨i, hi⟩ := D.vertex_mem ⟨w, hw⟩
      exact ⟨i.castSucc, mem_addVertexBag.mpr (Or.inl rfl),
        mem_addVertexBag.mpr (Or.inr ⟨i.isLt, hw, hi⟩)⟩
    · by_cases hw : w = v
      · subst w
        obtain ⟨i, hi⟩ := D.vertex_mem ⟨u, hu⟩
        exact ⟨i.castSucc, mem_addVertexBag.mpr (Or.inr ⟨i.isLt, hu, hi⟩),
          mem_addVertexBag.mpr (Or.inl rfl)⟩
      · obtain ⟨i, hiu, hiw⟩ := D.edge_mem ⟨u, hu⟩ ⟨w, hw⟩ hadj
        exact ⟨i.castSucc, mem_addVertexBag.mpr (Or.inr ⟨i.isLt, hu, hiu⟩),
          mem_addVertexBag.mpr (Or.inr ⟨i.isLt, hw, hiw⟩)⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hw : w = v
    · exact mem_addVertexBag.mpr (Or.inl hw)
    · obtain ⟨hi, _, hwi⟩ := (mem_addVertexBag.mp hwi).resolve_left hw
      obtain ⟨hk, _, hwk⟩ := (mem_addVertexBag.mp hwk).resolve_left hw
      have hj : j.val < D.length := lt_of_le_of_lt hjk hk
      exact mem_addVertexBag.mpr (Or.inr ⟨hj, hw,
        D.consecutive ⟨w, hw⟩ ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk hwi hwk⟩)

theorem exists_addVertex (v : W) (D : PathDecomposition (H.induce {w | w ≠ v}))
    {b : Nat} (bound : ∀ i, (D.bag i).card ≤ b) :
    ∃ D' : PathDecomposition H, D'.EndsAt {v} ∧ ∀ i, (D'.bag i).card ≤ b + 1 := by
  refine ⟨addVertex v D, ?_, ?_⟩
  · refine ⟨⟨D.length, by simp [addVertex]⟩, ?_, ?_⟩
    · intro i
      have hi := i.isLt
      change i.val < D.length + 1 at hi
      change i.val ≤ D.length
      lia
    · simp [addVertex, addVertexBag]
  · intro i
    change (addVertexBag v D i).card ≤ b + 1
    unfold addVertexBag
    apply (Finset.card_insert_le _ _).trans
    split
    · simpa only [liftBag, Finset.card_map] using Nat.add_le_add_right (bound _) 1
    · simp

end Algebraic.Cutwidth.PathDecomposition.Internal
