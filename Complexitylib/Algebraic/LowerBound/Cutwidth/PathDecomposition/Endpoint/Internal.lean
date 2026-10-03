/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Glue
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Operations
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Tree
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.TreeComponent

/-!
# The subcubic endpoint induction

This proves the prescribed-endpoint decomposition in Fomin and Høie's
Lemma 4, using the elementary base-two tree bound. The resulting bags have
size at most `max |X| (n / 3 + 1) + ceil(log₂ n) + 1`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

private theorem induced_degree_le {W : Type} [Fintype W] (H : SimpleGraph W)
    (S : Set W) [Fintype S] (v : S) : (H.induce S).degree v ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  apply Fintype.card_le_of_injective
    (fun w : (H.induce S).neighborSet v => (⟨w.val.val, w.property⟩ : H.neighborSet v))
  intro u w h
  have hval : u.val.val = w.val.val := congrArg (fun t : H.neighborSet v => t.val) h
  exact Subtype.ext (Subtype.ext hval)

private theorem endpoint_bound_mono {n' n x y : Nat}
    (hn : n' ≤ n) (hx : x ≤ y) (hy : n / 3 + 1 ≤ y) :
    max x (n' / 3 + 1) + Nat.clog 2 n' + 1 ≤ y + Nat.clog 2 n + 1 := by
  have hdiv := Nat.div_le_div_right (c := 3) hn
  have hlog := Nat.clog_mono_right 2 hn
  have hmax : max x (n' / 3 + 1) ≤ y := max_le hx (by lia)
  lia

private theorem exists_subcubic_endpoint_aux (n : Nat) :
    ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W = n →
      (∀ v, H.degree v ≤ 3) → ∀ X : Finset W,
      ∃ D : PathDecomposition H, D.EndsAt X ∧
        ∀ i, (D.bag i).card ≤ max X.card (n / 3 + 1) + Nat.clog 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcard degree X
    by_cases hn : n = 0
    · apply (trivial_endsAt (H := H)).exists_subset X.subset_univ
      intro i
      change Fintype.card W ≤ max X.card (n / 3 + 1) + Nat.clog 2 n + 1
      lia
    have htarget : max X.card (n / 3 + 1) ≤ Fintype.card W := by
      apply max_le (Finset.card_le_univ X)
      have hdiv : n / 3 < n := Nat.div_lt_self (by lia) (by lia)
      lia
    obtain ⟨Y, hXY, _, hY⟩ := Finset.exists_subsuperset_card_eq X.subset_univ
      (le_max_left X.card (n / 3 + 1)) (by simpa only [Finset.card_univ] using htarget)
    have hfloor : n / 3 + 1 ≤ Y.card := by rw [hY]; exact le_max_right _ _
    have hlarge : Fintype.card W < 3 * Y.card := by lia
    have forY : ∃ D : PathDecomposition H, D.EndsAt Y ∧
        ∀ i, (D.bag i).card ≤ Y.card + Nat.clog 2 n + 1 := by
      rcases boundary_reduction H Y degree hlarge with ⟨v, hv, small⟩ | ⟨C, tree⟩
      · let Z := Y ∪ (H.neighborFinset v \ Y)
        have hvZ : v ∈ Z := Finset.mem_union_left _ hv
        have hYZ : Y ⊆ Z := Finset.subset_union_left
        have hZ : Z.card ≤ Y.card + 1 :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left small _)
        have neighbors (w : W) (hadj : H.Adj v w) : w ∈ Z := by
          by_cases hw : w ∈ Y
          · exact Finset.mem_union_left _ hw
          · exact Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset v w).mpr hadj, hw⟩)
        let W' := {w : W // w ≠ v}
        have hsmall : Fintype.card W' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := v) (by simp)
        have degree' (w : W') : (H.induce {w | w ≠ v}).degree w ≤ 3 :=
          (induced_degree_le H {w | w ≠ v} w).trans (degree w)
        obtain ⟨D, endD, boundD⟩ := ih (Fintype.card W') hsmall W'
          (H.induce {w | w ≠ v}) rfl degree' (Z.subtype (· ≠ v))
        have mapZ : (Z.subtype (· ≠ v)).map (.subtype (· ≠ v)) = Z.erase v := by
          rw [Finset.subtype_map]
          ext w
          simp only [Finset.mem_filter, Finset.mem_erase]
          tauto
        have sizeZ : (Z.subtype (· ≠ v)).card ≤ Y.card := by
          have hc : (Z.subtype (· ≠ v)).card + 1 = Z.card := by
            rw [← Finset.card_map (.subtype (· ≠ v)), mapZ,
              Finset.card_erase_add_one hvZ]
          lia
        apply exists_endsAt_of_delete v hvZ D endD neighbors hYZ
        · exact fun i => (boundD i).trans (endpoint_bound_mono hsmall.le sizeZ hfloor)
        · lia
      · let f : C.toSimpleGraph ↪g H :=
          { toEmbedding :=
              ⟨fun v => v.val.val, fun u v h => Subtype.ext (Subtype.ext h)⟩
            map_rel_iff' := Iff.rfl }
        have : Nonempty C := C.connected_toSimpleGraph.nonempty
        obtain ⟨u⟩ := ‹Nonempty C›
        let W' := {w : W // w ∉ Set.range f}
        have hsmall : Fintype.card W' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := f u) (not_not.mpr ⟨u, rfl⟩)
        have degree' (w : W') : (H.induce {w | w ∉ Set.range f}).degree w ≤ 3 :=
          (induced_degree_le H {w | w ∉ Set.range f} w).trans (degree w)
        obtain ⟨D, endD, boundD⟩ := ih (Fintype.card W') hsmall W'
          (H.induce {w | w ∉ Set.range f}) rfl degree' (Y.subtype (· ∉ Set.range f))
        have sizeY : (Y.subtype (· ∉ Set.range f)).card ≤ Y.card := by
          rw [Finset.card_subtype]
          exact Finset.card_filter_le _ _
        have boundD' (i) : (D.bag i).card ≤ Y.card + Nat.clog 2 n + 1 :=
          (boundD i).trans (endpoint_bound_mono hsmall.le sizeY hfloor)
        obtain ⟨E, boundE⟩ := PathDecomposition.exists_tree tree
        have sourceSize : Fintype.card C ≤ n := by
          rw [← hcard]
          exact Fintype.card_le_of_injective f f.injective
        have boundE' (i) : (E.bag i).card ≤ Nat.clog 2 n + 1 :=
          (boundE i).trans (Nat.add_le_add_right (Nat.clog_mono_right 2 sourceSize) 1)
        have neighbors (a : C) (w : W) (hadj : H.Adj (f a) w) :
            w ∈ Set.range f ∨ w ∈ Y := by
          by_cases hw : w ∈ Y
          · exact Or.inr hw
          · have hC : (⟨w, hw⟩ : {w : W // w ∉ Y}) ∈ C.supp :=
              C.mem_supp_of_adj_mem_supp a.property hadj
            exact Or.inl ⟨⟨⟨w, hw⟩, hC⟩, rfl⟩
        obtain ⟨F, endF, boundF⟩ := PathDecomposition.exists_attach
          (G := C.toSimpleGraph) (H := H) (b := Y.card + Nat.clog 2 n + 1)
          (c := Nat.clog 2 n + 1) f Y D E (by
            obtain ⟨last, hlast, hbag⟩ := endD
            refine ⟨last, hlast, ?_⟩
            rw [hbag]
            ext w
            simp only [Finset.mem_subtype]) neighbors boundD' boundE'
        refine ⟨F, endF, fun i => ?_⟩
        simpa only [Nat.add_assoc, max_self] using boundF i
    obtain ⟨D, endD, boundD⟩ := forY
    apply endD.exists_subset hXY
    simpa only [hY] using boundD

theorem exists_subcubic_endpoint {W : Type} [Fintype W] (H : SimpleGraph W)
    (degree : ∀ v, H.degree v ≤ 3) (X : Finset W) :
    ∃ D : PathDecomposition H, D.EndsAt X ∧ ∀ i,
      (D.bag i).card ≤
        max X.card (Fintype.card W / 3 + 1) + Nat.clog 2 (Fintype.card W) + 1 :=
  exists_subcubic_endpoint_aux _ W H rfl degree X

end Algebraic.Cutwidth.PathDecomposition.Internal
