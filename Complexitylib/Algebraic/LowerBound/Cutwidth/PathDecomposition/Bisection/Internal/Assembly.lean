/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Boundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.CutBoundary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations

/-!
# Assembly across a graph cut

The two side decompositions meet the decomposition on their vertex
boundaries. Their three bag sequences concatenate without enlarging bags.
This is the assembly step in Fomin and Høie's Theorem 5.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W) (S : Finset W)

theorem exists_between_cutBoundaries :
    let T := {w | w ∈ cutBoundary H S ∨ w ∈ cutBoundary H Sᶜ}
    ∃ D : PathDecomposition (H.induce T),
      D.StartsAt ((cutBoundary H S).subtype (· ∈ T)) ∧
      D.EndsAt ((cutBoundary H Sᶜ).subtype (· ∈ T)) ∧
      ∀ i, (D.bag i).card ≤ (H.cutFinset S).card + 1 := by
  let X := cutBoundary H S
  let Y := cutBoundary H Sᶜ
  let T := {w | w ∈ X ∨ w ∈ Y}
  change ∃ D : PathDecomposition (H.induce T),
    D.StartsAt (X.subtype (· ∈ T)) ∧ D.EndsAt (Y.subtype (· ∈ T)) ∧
      ∀ i, (D.bag i).card ≤ (H.cutFinset S).card + 1
  have left (u : T) (hu : u ∈ S.subtype (· ∈ T)) :
      ∃ v : T, v ∉ S.subtype (· ∈ T) ∧ (H.induce T).Adj u v := by
    have huS : u.val ∈ S := Finset.mem_subtype.mp hu
    have huX : u.val ∈ X := u.property.resolve_right
      (fun h => (Finset.mem_compl.mp (cutBoundary_subset H Sᶜ h)) huS)
    obtain ⟨_, v, hv, hadj⟩ := (mem_cutBoundary H).mp huX
    have hvY : v ∈ Y := (mem_cutBoundary H).mpr
      ⟨Finset.mem_compl.mpr hv, u, by simpa using huS, hadj.symm⟩
    exact ⟨⟨v, Or.inr hvY⟩, fun h => hv (Finset.mem_subtype.mp h), hadj⟩
  have right (u : T) (hu : u ∉ S.subtype (· ∈ T)) :
      ∃ v ∈ S.subtype (· ∈ T), (H.induce T).Adj v u := by
    have huS : u.val ∉ S := fun h => hu (Finset.mem_subtype.mpr h)
    have huY : u.val ∈ Y := u.property.resolve_left
      (fun h => huS (cutBoundary_subset H S h))
    obtain ⟨_, v, hv, hadj⟩ := (mem_cutBoundary H).mp huY
    have hvS : v ∈ S := by simpa using hv
    have hvX : v ∈ X := (mem_cutBoundary H).mpr ⟨hvS, u, huS, hadj.symm⟩
    exact ⟨⟨v, Or.inl hvX⟩, Finset.mem_subtype.mpr hvS, hadj.symm⟩
  have firstEq : S.subtype (· ∈ T) = X.subtype (· ∈ T) := by
    ext u
    simp only [Finset.mem_subtype]
    exact ⟨fun hu => u.property.resolve_right
      (fun h => (Finset.mem_compl.mp (cutBoundary_subset H Sᶜ h)) hu),
      fun h => cutBoundary_subset H S h⟩
  obtain ⟨D, first, last, indices, firstBag, lastBag, bound⟩ :=
    exists_between_of_crossing (H.induce T) (S.subtype (· ∈ T)) left right
  refine ⟨D, ⟨first, fun i => (indices i).1, firstBag.trans firstEq⟩,
    ⟨last, fun i => (indices i).2, ?_⟩,
    fun i => (bound i).trans (Nat.add_le_add_right (card_cutFinset_induce_le H S T) 1)⟩
  rw [lastBag]
  ext u
  simp only [Finset.mem_compl, Finset.mem_subtype]
  exact ⟨fun hu => u.property.resolve_left (fun h => hu (cutBoundary_subset H S h)),
    fun h => Finset.mem_compl.mp (cutBoundary_subset H Sᶜ h)⟩

theorem exists_assemble_cut
    (DL : PathDecomposition (H.induce {w | w ∈ S}))
    (DM : PathDecomposition
      (H.induce {w | w ∈ cutBoundary H S ∨ w ∈ cutBoundary H Sᶜ}))
    (DR : PathDecomposition (H.induce {w | w ∉ S}))
    (leftEnd : DL.EndsAt ((cutBoundary H S).subtype (· ∈ S)))
    (middleStart : DM.StartsAt ((cutBoundary H S).subtype
      (fun w => w ∈ cutBoundary H S ∨ w ∈ cutBoundary H Sᶜ)))
    (middleEnd : DM.EndsAt ((cutBoundary H Sᶜ).subtype
      (fun w => w ∈ cutBoundary H S ∨ w ∈ cutBoundary H Sᶜ)))
    (rightStart : DR.StartsAt ((cutBoundary H Sᶜ).subtype (· ∉ S)))
    {b : Nat} (leftBound : ∀ i, (DL.bag i).card ≤ b)
    (middleBound : ∀ i, (DM.bag i).card ≤ b)
    (rightBound : ∀ i, (DR.bag i).card ≤ b) :
    ∃ D : PathDecomposition H, ∀ i, (D.bag i).card ≤ b := by
  let X := cutBoundary H S
  let Y := cutBoundary H Sᶜ
  let T := {w | w ∈ X ∨ w ∈ Y}
  let M := {w | w ∈ S ∨ w ∈ Y}
  let leftInc : H.induce {w | w ∈ S} ↪g H.induce M :=
    H.induceHomOfLE (fun _ h => Or.inl h)
  let middleInc : H.induce T ↪g H.induce M :=
    H.induceHomOfLE (fun _ h => h.elim (fun hx => Or.inl (cutBoundary_subset H S hx)) Or.inr)
  have inLeft (w : M) : w ∈ Set.range leftInc ↔ w.val ∈ S := by
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hw
      exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩
  have inMiddle (w : M) : w ∈ Set.range middleInc ↔ w.val ∈ T := by
    constructor
    · rintro ⟨v, rfl⟩
      exact v.property
    · intro hw
      exact ⟨⟨w.val, hw⟩, Subtype.ext rfl⟩
  have cover (w : M) : w ∈ Set.range leftInc ∨ w ∈ Set.range middleInc := by
    rcases w.property with hw | hw
    · exact Or.inl ((inLeft w).mpr hw)
    · exact Or.inr ((inMiddle w).mpr (Or.inr hw))
  have edges (u v : M) (hadj : (H.induce M).Adj u v) :
      (u ∈ Set.range leftInc ∧ v ∈ Set.range leftInc) ∨
        (u ∈ Set.range middleInc ∧ v ∈ Set.range middleInc) := by
    by_cases hu : u.val ∈ S <;> by_cases hv : v.val ∈ S
    · exact Or.inl ⟨(inLeft u).mpr hu, (inLeft v).mpr hv⟩
    · have huX : u.val ∈ X := (mem_cutBoundary H).mpr ⟨hu, v, hv, hadj⟩
      exact Or.inr ⟨(inMiddle u).mpr (Or.inl huX),
        (inMiddle v).mpr (Or.inr (v.property.resolve_left hv))⟩
    · have hvX : v.val ∈ X := (mem_cutBoundary H).mpr ⟨hv, u, hu, hadj.symm⟩
      exact Or.inr ⟨(inMiddle u).mpr (Or.inr (u.property.resolve_left hu)),
        (inMiddle v).mpr (Or.inl hvX)⟩
    · exact Or.inr ⟨(inMiddle u).mpr (Or.inr (u.property.resolve_left hu)),
        (inMiddle v).mpr (Or.inr (v.property.resolve_left hv))⟩
  have overlap (u : {w | w ∈ S}) (v : T) (heq : leftInc u = middleInc v) :
      u ∈ X.subtype (· ∈ S) ∧ v ∈ X.subtype (· ∈ T) := by
    have hv : u.val = v.val := congrArg (fun w : M => w.val) heq
    have hvS : v.val ∈ S := hv ▸ u.property
    have hvX : v.val ∈ X := v.property.resolve_right
      (fun h => (Finset.mem_compl.mp (cutBoundary_subset H Sᶜ h)) hvS)
    exact ⟨Finset.mem_subtype.mpr (hv.symm ▸ hvX), Finset.mem_subtype.mpr hvX⟩
  obtain ⟨F, endF, boundF⟩ := exists_glue_embeddings DL DM leftInc middleInc cover edges
    leftEnd middleStart middleEnd overlap leftBound middleBound
  have endF' : F.EndsAt (Y.subtype (· ∈ M)) := by
    obtain ⟨last, hlast, hbag⟩ := endF
    refine ⟨last, hlast, hbag.trans ?_⟩
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
      simp only [Finset.mem_subtype] at hv ⊢
      exact hv
    · intro hw
      simp only [Finset.mem_subtype] at hw
      refine Finset.mem_map.mpr ⟨⟨w.val, Or.inr hw⟩, ?_, Subtype.ext rfl⟩
      simpa only [Finset.mem_subtype] using hw
  let middleOut : H.induce M ↪g H := SimpleGraph.Embedding.induce M
  let rightOut : H.induce {w | w ∉ S} ↪g H := SimpleGraph.Embedding.induce _
  have inM (w : W) (hw : w ∈ M) : w ∈ Set.range middleOut := ⟨⟨w, hw⟩, rfl⟩
  have inR (w : W) (hw : w ∉ S) : w ∈ Set.range rightOut := ⟨⟨w, hw⟩, rfl⟩
  have cover' (w : W) : w ∈ Set.range middleOut ∨ w ∈ Set.range rightOut := by
    by_cases hw : w ∈ S
    · exact Or.inl (inM w (Or.inl hw))
    · exact Or.inr (inR w hw)
  have edges' (u v : W) (hadj : H.Adj u v) :
      (u ∈ Set.range middleOut ∧ v ∈ Set.range middleOut) ∨
        (u ∈ Set.range rightOut ∧ v ∈ Set.range rightOut) := by
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact Or.inl ⟨inM u (Or.inl hu), inM v (Or.inl hv)⟩
    · have hvY : v ∈ Y := (mem_cutBoundary H).mpr
        ⟨Finset.mem_compl.mpr hv, u, by simpa using hu, hadj.symm⟩
      exact Or.inl ⟨inM u (Or.inl hu), inM v (Or.inr hvY)⟩
    · have huY : u ∈ Y := (mem_cutBoundary H).mpr
        ⟨Finset.mem_compl.mpr hu, v, by simpa using hv, hadj⟩
      exact Or.inl ⟨inM u (Or.inr huY), inM v (Or.inl hv)⟩
    · exact Or.inr ⟨inR u hu, inR v hv⟩
  have overlap' (u : M) (v : {w | w ∉ S}) (heq : middleOut u = rightOut v) :
      u ∈ Y.subtype (· ∈ M) ∧ v ∈ Y.subtype (· ∉ S) := by
    have hv : u.val = v.val := heq
    have huS : u.val ∉ S := fun h => v.property (hv ▸ h)
    have huY : u.val ∈ Y := u.property.resolve_left huS
    exact ⟨Finset.mem_subtype.mpr huY, Finset.mem_subtype.mpr (hv ▸ huY)⟩
  obtain ⟨Z, endR⟩ := rightStart.exists_endsAt
  obtain ⟨D, _, boundD⟩ := exists_glue_embeddings F DR middleOut rightOut cover' edges'
    endF' rightStart endR overlap' boundF rightBound
  exact ⟨D, boundD⟩

end Algebraic.Cutwidth.PathDecomposition.Internal
