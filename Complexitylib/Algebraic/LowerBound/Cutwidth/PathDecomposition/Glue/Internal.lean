/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Padding

/-!
# Concatenating overlapping induced decompositions

Two induced graphs cover the vertices and edges. Their path decompositions
can be concatenated if every shared vertex belongs to the adjoining bags.
The last bag of the right decomposition is retained, and no bag grows.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

variable {W : Type} {H : SimpleGraph W} {A B : Set W}

private noncomputable def ambientBag {S : Set W} (X : Finset S) : Finset W :=
  X.map (.subtype (· ∈ S))

private theorem mem_ambientBag {S : Set W} {X : Finset S} {w : W} :
    w ∈ ambientBag X ↔ ∃ hw : w ∈ S, (⟨w, hw⟩ : S) ∈ X := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact ⟨v.property, hv⟩
  · rintro ⟨hw, hv⟩
    exact Finset.mem_map.mpr ⟨⟨w, hw⟩, hv, rfl⟩

private noncomputable def glueBag (D : PathDecomposition (H.induce A))
    (E : PathDecomposition (H.induce B)) (i : Fin (D.length + E.length)) : Finset W :=
  if hi : i.val < D.length then ambientBag (D.bag ⟨i.val, hi⟩)
  else ambientBag (E.bag ⟨i.val - D.length, by have := i.isLt; lia⟩)

private theorem glueBag_left (D : PathDecomposition (H.induce A))
    (E : PathDecomposition (H.induce B)) (i : Fin D.length) :
    glueBag D E (Fin.castAdd E.length i) = ambientBag (D.bag i) := by
  simp [glueBag, i.isLt]

private theorem glueBag_right (D : PathDecomposition (H.induce A))
    (E : PathDecomposition (H.induce B)) (i : Fin E.length) :
    glueBag D E (Fin.natAdd D.length i) = ambientBag (E.bag i) := by
  simp [glueBag]

private noncomputable def glue (D : PathDecomposition (H.induce A))
    (E : PathDecomposition (H.induce B))
    (cover : ∀ w, w ∈ A ∨ w ∈ B)
    (edges : ∀ u v, H.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    (last : Fin D.length) (hlast : ∀ i, i ≤ last)
    (first : Fin E.length) (hfirst : ∀ i, first ≤ i)
    (overlap : ∀ w (ha : w ∈ A) (hb : w ∈ B),
      (⟨w, ha⟩ : A) ∈ D.bag last ∧ (⟨w, hb⟩ : B) ∈ E.bag first) :
    PathDecomposition H where
  length := D.length + E.length
  bag := glueBag D E
  vertex_mem w := by
    rcases cover w with hw | hw
    · obtain ⟨i, hi⟩ := D.vertex_mem ⟨w, hw⟩
      exact ⟨Fin.castAdd E.length i, (glueBag_left D E i).symm ▸
        mem_ambientBag.mpr ⟨hw, hi⟩⟩
    · obtain ⟨i, hi⟩ := E.vertex_mem ⟨w, hw⟩
      exact ⟨Fin.natAdd D.length i, (glueBag_right D E i).symm ▸
        mem_ambientBag.mpr ⟨hw, hi⟩⟩
  edge_mem u v hadj := by
    rcases edges u v hadj with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · obtain ⟨i, hiu, hiv⟩ := D.edge_mem ⟨u, hu⟩ ⟨v, hv⟩ hadj
      exact ⟨Fin.castAdd E.length i, (glueBag_left D E i).symm ▸
        mem_ambientBag.mpr ⟨hu, hiu⟩, (glueBag_left D E i).symm ▸
        mem_ambientBag.mpr ⟨hv, hiv⟩⟩
    · obtain ⟨i, hiu, hiv⟩ := E.edge_mem ⟨u, hu⟩ ⟨v, hv⟩ hadj
      exact ⟨Fin.natAdd D.length i, (glueBag_right D E i).symm ▸
        mem_ambientBag.mpr ⟨hu, hiu⟩, (glueBag_right D E i).symm ▸
        mem_ambientBag.mpr ⟨hv, hiv⟩⟩
  consecutive w i j k hij hjk hwi hwk := by
    by_cases hk : k.val < D.length
    · have hj : j.val < D.length := lt_of_le_of_lt hjk hk
      have hi : i.val < D.length := lt_of_le_of_lt hij hj
      simp only [glueBag, dite_eq_left hi, dite_eq_left hk] at hwi hwk
      obtain ⟨hw, hwi⟩ := mem_ambientBag.mp hwi
      obtain ⟨_, hwk⟩ := mem_ambientBag.mp hwk
      simp only [glueBag, dite_eq_left hj]
      exact mem_ambientBag.mpr ⟨hw,
        D.consecutive ⟨w, hw⟩ ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨k.val, hk⟩ hij hjk hwi hwk⟩
    · simp only [glueBag, dite_eq_right hk] at hwk
      obtain ⟨hwB, hwk⟩ := mem_ambientBag.mp hwk
      by_cases hi : i.val < D.length
      · simp only [glueBag, dite_eq_left hi] at hwi
        obtain ⟨hwA, hwi⟩ := mem_ambientBag.mp hwi
        obtain ⟨hwlast, hwfirst⟩ := overlap w hwA hwB
        by_cases hj : j.val < D.length
        · simp only [glueBag, dite_eq_left hj]
          exact mem_ambientBag.mpr ⟨hwA,
            D.consecutive ⟨w, hwA⟩ ⟨i.val, hi⟩ ⟨j.val, hj⟩ last hij (hlast _) hwi hwlast⟩
        · simp only [glueBag, dite_eq_right hj]
          exact mem_ambientBag.mpr ⟨hwB,
            E.consecutive ⟨w, hwB⟩ first _ _ (hfirst _) (Nat.sub_le_sub_right hjk _)
              hwfirst hwk⟩
      · have hj : ¬ j.val < D.length := by change i.val ≤ j.val at hij; lia
        simp only [glueBag, dite_eq_right hi] at hwi
        obtain ⟨_, hwi⟩ := mem_ambientBag.mp hwi
        simp only [glueBag, dite_eq_right hj]
        exact mem_ambientBag.mpr ⟨hwB,
          E.consecutive ⟨w, hwB⟩ _ _ _ (Nat.sub_le_sub_right hij _)
            (Nat.sub_le_sub_right hjk _) hwi hwk⟩

theorem exists_glue (D : PathDecomposition (H.induce A))
    (E : PathDecomposition (H.induce B))
    (cover : ∀ w, w ∈ A ∨ w ∈ B)
    (edges : ∀ u v, H.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B))
    {X : Finset A} (hend : D.EndsAt X) {Y Z : Finset B}
    (hstart : E.StartsAt Y) (hend' : E.EndsAt Z)
    (overlap : ∀ w (ha : w ∈ A) (hb : w ∈ B),
      (⟨w, ha⟩ : A) ∈ X ∧ (⟨w, hb⟩ : B) ∈ Y)
    {b : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ b) :
    ∃ F : PathDecomposition H,
      F.EndsAt (Z.map (.subtype (· ∈ B))) ∧ ∀ i, (F.bag i).card ≤ b := by
  obtain ⟨last, hlast, rfl⟩ := hend
  obtain ⟨first, hfirst, rfl⟩ := hstart
  obtain ⟨last', hlast', rfl⟩ := hend'
  refine ⟨glue D E cover edges last hlast first hfirst overlap, ?_, ?_⟩
  · refine ⟨Fin.natAdd D.length last', ?_, glueBag_right D E last'⟩
    intro i
    change i.val ≤ D.length + last'.val
    by_cases hi : i.val < D.length
    · lia
    · have hi' : i.val - D.length < E.length := by
        have h := i.isLt
        change i.val < D.length + E.length at h
        lia
      have h := hlast' ⟨i.val - D.length, hi'⟩
      change i.val - D.length ≤ last'.val at h
      lia
  · intro i
    change (glueBag D E i).card ≤ b
    unfold glueBag
    split
    · simpa only [ambientBag, Finset.card_map] using leftBound _
    · simpa only [ambientBag, Finset.card_map] using rightBound _

theorem exists_glue_embeddings {U V : Type} {G : SimpleGraph U} {J : SimpleGraph V}
    (D : PathDecomposition G) (E : PathDecomposition J) (f : G ↪g H) (g : J ↪g H)
    (cover : ∀ w, w ∈ Set.range f ∨ w ∈ Set.range g)
    (edges : ∀ u v, H.Adj u v →
      (u ∈ Set.range f ∧ v ∈ Set.range f) ∨ (u ∈ Set.range g ∧ v ∈ Set.range g))
    {X : Finset U} (hend : D.EndsAt X) {Y Z : Finset V}
    (hstart : E.StartsAt Y) (hend' : E.EndsAt Z)
    (overlap : ∀ u v, f u = g v → u ∈ X ∧ v ∈ Y)
    {b : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ b) :
    ∃ F : PathDecomposition H,
      F.EndsAt (Z.map g.toEmbedding) ∧ ∀ i, (F.bag i).card ≤ b := by
  have shared (w : W) (hf : w ∈ Set.range f) (hg : w ∈ Set.range g) :
      (⟨w, hf⟩ : Set.range f) ∈ X.map f.isoInduceRange.toEquiv.toEmbedding ∧
        (⟨w, hg⟩ : Set.range g) ∈ Y.map g.isoInduceRange.toEquiv.toEmbedding := by
    obtain ⟨u, rfl⟩ := hf
    obtain ⟨v, hv⟩ := hg
    obtain ⟨huX, hvY⟩ := overlap u v hv.symm
    exact ⟨Finset.mem_map.mpr ⟨u, huX, Subtype.ext rfl⟩,
      Finset.mem_map.mpr ⟨v, hvY, Subtype.ext hv⟩⟩
  obtain ⟨F, endF, boundF⟩ := exists_glue
    (b := b) (D.relabel f.isoInduceRange) (E.relabel g.isoInduceRange) cover edges
    (hend.relabel _) (hstart.relabel _) (hend'.relabel _) shared
    (fun i => by
      change ((D.bag i).map f.isoInduceRange.toEquiv.toEmbedding).card ≤ b
      simpa only [Finset.card_map] using leftBound i)
    (fun i => by
      change ((E.bag i).map g.isoInduceRange.toEquiv.toEmbedding).card ≤ b
      simpa only [Finset.card_map] using rightBound i)
  have hmap : (Z.map g.isoInduceRange.toEquiv.toEmbedding).map
      (.subtype (· ∈ Set.range g)) = Z.map g.toEmbedding := by
    rw [Finset.map_map]
    congr 1
  exact ⟨F, hmap ▸ endF, boundF⟩

theorem exists_attach {V : Type} {G : SimpleGraph V} (f : G ↪g H) (X : Finset W)
    (D : PathDecomposition (H.induce {w | w ∉ Set.range f}))
    (E : PathDecomposition G) (hend : D.EndsAt (X.subtype (· ∉ Set.range f)))
    (neighbors : ∀ u v, H.Adj (f u) v → v ∈ Set.range f ∨ v ∈ X)
    {b c : Nat} (leftBound : ∀ i, (D.bag i).card ≤ b)
    (rightBound : ∀ i, (E.bag i).card ≤ c) :
    ∃ F : PathDecomposition H, F.EndsAt X ∧
      ∀ i, (F.bag i).card ≤ max b (X.card + c) := by
  let B : Set W := Set.range f ∪ (X : Set W)
  let fB : G ↪g H.induce B :=
    { toEmbedding :=
        ⟨fun v => ⟨f v, Or.inl ⟨v, rfl⟩⟩,
          fun u v h => f.injective (congrArg Subtype.val h)⟩
      map_rel_iff' := by intro u v; exact f.map_adj_iff }
  let XB : Finset B := X.subtype (· ∈ B)
  have coverB (w : B) : w ∈ Set.range fB ∨ w ∈ XB := by
    rcases w.property with ⟨v, hv⟩ | hw
    · exact Or.inl ⟨v, Subtype.ext hv⟩
    · exact Or.inr (Finset.mem_subtype.mpr hw)
  obtain ⟨P, startP, endP, boundP⟩ := exists_pad E fB XB coverB rightBound
  have mapXB : XB.map (.subtype (· ∈ B)) = X :=
    Finset.subtype_map_of_mem (fun _ hw => Or.inr hw)
  have cardXB : XB.card = X.card := by
    rw [← Finset.card_map (.subtype (· ∈ B)), mapXB]
  have cover (w : W) : w ∉ Set.range f ∨ w ∈ B := by
    by_cases hw : w ∈ Set.range f
    · exact Or.inr (Or.inl hw)
    · exact Or.inl hw
  have edges (u v : W) (hadj : H.Adj u v) :
      (u ∉ Set.range f ∧ v ∉ Set.range f) ∨ (u ∈ B ∧ v ∈ B) := by
    by_cases hu : u ∈ Set.range f
    · obtain ⟨u, rfl⟩ := hu
      exact Or.inr ⟨Or.inl ⟨u, rfl⟩, neighbors u v hadj⟩
    · by_cases hv : v ∈ Set.range f
      · obtain ⟨v, rfl⟩ := hv
        exact Or.inr ⟨neighbors v u hadj.symm, Or.inl ⟨v, rfl⟩⟩
      · exact Or.inl ⟨hu, hv⟩
  have overlap (w : W) (ha : w ∉ Set.range f) (hb : w ∈ B) :
      (⟨w, ha⟩ : {w | w ∉ Set.range f}) ∈ X.subtype (· ∉ Set.range f) ∧
        (⟨w, hb⟩ : B) ∈ XB := by
    have hw : w ∈ X := hb.resolve_left ha
    exact ⟨Finset.mem_subtype.mpr hw, Finset.mem_subtype.mpr hw⟩
  obtain ⟨F, endF, boundF⟩ := exists_glue D P cover edges hend startP endP overlap
    (fun i => (leftBound i).trans (le_max_left _ _))
    (fun i => (boundP i).trans (by rw [cardXB]; exact le_max_right _ _))
  exact ⟨F, mapXB ▸ endF, boundF⟩

end Algebraic.Cutwidth.PathDecomposition.Internal
