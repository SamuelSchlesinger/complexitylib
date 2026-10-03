/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.Card

/-!
# Charging reverse extensions to disjoint configurations

Give each selected boundary vertex of a processed configuration four units
of credit, and each selected center one. Reversing a configuration removes
its credits. They pay for at most four new vertices, without selecting a
center of an earlier configuration. The resulting potential
telescopes over the entire normalization sequence.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal

open scoped Classical

variable {W : Type}

/-- Size plus the credits attached to selected boundary vertices and centers. -/
noncomputable def charge (B P X : Finset W) : ℕ :=
  X.card + 4 * (X ∩ B).card + (X ∩ P).card

theorem charge_empty (X : Finset W) : charge ∅ ∅ X = X.card := by
  simp [charge]

theorem charge_mono {B D P Q X : Finset W} (hBD : B ⊆ D) (hPQ : P ⊆ Q) :
    charge B P X ≤ charge D Q X := by
  have boundaryCount := Finset.card_le_card (show X ∩ B ⊆ X ∩ D from
    fun _ h => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hBD (Finset.mem_inter.mp h).2⟩)
  have centerCount := Finset.card_le_card (show X ∩ P ⊆ X ∩ Q from
    fun _ h => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1, hPQ (Finset.mem_inter.mp h).2⟩)
  dsimp [charge]
  lia

theorem charge_le_five {B P : Finset W} (disjoint : Disjoint B P) (X : Finset W) :
    charge B P X ≤ 5 * X.card := by
  have subset : X ∩ P ⊆ X \ B := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).1,
      fun hb => Finset.disjoint_left.mp disjoint hb (Finset.mem_inter.mp hv).2⟩
  have count := Finset.card_le_card subset
  have split := Finset.card_sdiff_add_card_inter X B
  dsimp [charge]
  lia

/-- Selecting the missing boundary endpoint costs one vertex, paid for by
the selected center whose configuration is being reversed. -/
theorem charge_restore_center {B P T X Y : Finset W} {a b : W}
    (fresh : a ∉ P) (selected : a ∈ X) (hbB : b ∉ B) (hbP : b ∉ P)
    (support : Y ⊆ insert b X) :
    charge B P Y ≤ charge (T ∪ B) (insert a P) X := by
  have size := (Finset.card_le_card support).trans (Finset.card_insert_le b X)
  have boundary : Y ∩ B ⊆ X ∩ B := by
    intro v hv
    obtain eq | old := Finset.mem_insert.mp (support (Finset.mem_inter.mp hv).1)
    · exact (hbB (eq ▸ (Finset.mem_inter.mp hv).2)).elim
    · exact Finset.mem_inter.mpr ⟨old, (Finset.mem_inter.mp hv).2⟩
  have centers : Y ∩ P ⊆ X ∩ P := by
    intro v hv
    obtain eq | old := Finset.mem_insert.mp (support (Finset.mem_inter.mp hv).1)
    · exact (hbP (eq ▸ (Finset.mem_inter.mp hv).2)).elim
    · exact Finset.mem_inter.mpr ⟨old, (Finset.mem_inter.mp hv).2⟩
  have addedCenter : (X ∩ P).card + 1 ≤ (X ∩ insert a P).card := by
    have subset : insert a (X ∩ P) ⊆ X ∩ insert a P := by
      apply Finset.insert_subset
      · exact Finset.mem_inter.mpr ⟨selected, Finset.mem_insert_self _ _⟩
      · intro v hv
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
          Finset.mem_insert_of_mem (Finset.mem_inter.mp hv).2⟩
    have count := Finset.card_le_card subset
    rwa [Finset.card_insert_of_notMem
      (fun h => fresh (Finset.mem_inter.mp h).2)] at count
  have moreBoundary := Finset.card_le_card (show X ∩ B ⊆ X ∩ (T ∪ B) from
    fun _ h => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
      Finset.mem_union_right _ (Finset.mem_inter.mp h).2⟩)
  have boundaryCount := Finset.card_le_card boundary
  have centerCount := Finset.card_le_card centers
  dsimp [charge]
  lia

/-- A selected boundary endpoint supplies four credits. All added vertices
are outside earlier configurations, so they require no further credit. -/
theorem charge_restore_boundary {B P T X Y : Finset W} {a b c : W}
    (haB : a ∉ B) (haP : a ∉ P) (hcB : c ∉ B) (hcP : c ∉ P)
    (separate : Disjoint T B) (interior : Disjoint T P)
    (selected : b ∈ X) (hb : b ∈ T) (size : Y.card ≤ X.card + 4)
    (support : Y ⊆ insert c (insert a (X ∪ T))) :
    charge B P Y ≤ charge (T ∪ B) (insert a P) X := by
  have boundary : Y ∩ B ⊆ X ∩ B := by
    intro v hv
    have vb := (Finset.mem_inter.mp hv).2
    obtain vc | va | old | star := by
      simpa only [Finset.mem_insert, Finset.mem_union] using support (Finset.mem_inter.mp hv).1
    · exact (hcB (vc ▸ vb)).elim
    · exact (haB (va ▸ vb)).elim
    · exact Finset.mem_inter.mpr ⟨old, vb⟩
    · exact (Finset.disjoint_left.mp separate star vb).elim
  have centers : Y ∩ P ⊆ X ∩ P := by
    intro v hv
    have vp := (Finset.mem_inter.mp hv).2
    obtain vc | va | old | star := by
      simpa only [Finset.mem_insert, Finset.mem_union] using support (Finset.mem_inter.mp hv).1
    · exact (hcP (vc ▸ vp)).elim
    · exact (haP (va ▸ vp)).elim
    · exact Finset.mem_inter.mpr ⟨old, vp⟩
    · exact (Finset.disjoint_left.mp interior star vp).elim
  have addedBoundary : (X ∩ B).card + 1 ≤ (X ∩ (T ∪ B)).card := by
    have subset : insert b (X ∩ B) ⊆ X ∩ (T ∪ B) := by
      apply Finset.insert_subset
      · exact Finset.mem_inter.mpr ⟨selected, Finset.mem_union_left _ hb⟩
      · intro v hv
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
          Finset.mem_union_right _ (Finset.mem_inter.mp hv).2⟩
    have count := Finset.card_le_card subset
    rwa [Finset.card_insert_of_notMem
      (fun h => Finset.disjoint_left.mp separate hb (Finset.mem_inter.mp h).2)] at count
  have moreCenters := Finset.card_le_card (show X ∩ P ⊆ X ∩ insert a P from
    fun _ h => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
      Finset.mem_insert_of_mem (Finset.mem_inter.mp h).2⟩)
  have boundaryCount := Finset.card_le_card boundary
  have centerCount := Finset.card_le_card centers
  dsimp [charge]
  lia

end Algebraic.Cutwidth.Bisection.NeighborNormalization.Internal
