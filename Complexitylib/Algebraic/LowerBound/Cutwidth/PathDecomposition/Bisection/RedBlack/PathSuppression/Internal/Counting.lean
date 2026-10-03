/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSuppression.Internal

/-!
# Counting the connections left by path suppression

In a forest, two different intermediate vertices cannot give paths between
the same endpoints. For a bipartition with degree at most two on the removed
side, each removed degree-two vertex therefore gives exactly one distinct
edge of the suppressed graph. Isolated vertices and leaves give no edges.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal

open scoped Classical

variable {V : Type} (B : SimpleGraph V)

private theorem middle_unique (forest : B.IsAcyclic) {u v x y : V} (different : u ≠ v)
    (ux : B.Adj u x) (xv : B.Adj x v) (uy : B.Adj u y) (yv : B.Adj y v) : x = y := by
  let p : B.Walk u v := .cons ux (.cons xv .nil)
  let q : B.Walk u v := .cons uy (.cons yv .nil)
  have pathP : p.IsPath := by
    simp [p, SimpleGraph.Walk.cons_isPath_iff, ux.ne, xv.ne, different]
  have pathQ : q.IsPath := by
    simp [q, SimpleGraph.Walk.cons_isPath_iff, uy.ne, yv.ne, different]
  have equal : (⟨p, pathP⟩ : B.Path u v) = ⟨q, pathQ⟩ :=
    (forest.subsingleton_path u v).elim _ _
  have atOne := congrArg (fun p : B.Path u v => p.val.getVert 1) equal
  simpa [p, q] using atOne

variable [Fintype V] (S : Finset V)

theorem exists_connection_equiv (forest : B.IsAcyclic)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (coreIndependent : ∀ u ∉ S, ∀ v ∉ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) :
    ∃ f : (S.filter (fun v => B.degree v = 2)) ≃ (graph B S).edgeSet,
      ∀ x, ∃ u v : {v // v ∉ S}, (f x).val = s(u, v) ∧
        B.Adj u.val x.val ∧ B.Adj x.val v.val := by
  let active := S.filter (fun v => B.degree v = 2)
  have neighbors (x : active) : ∃ u v : {v // v ∉ S}, u ≠ v ∧
      B.Adj u.val x.val ∧ B.Adj x.val v.val ∧ B.neighborFinset x.val = {u.val, v.val} := by
    have hx := Finset.mem_filter.mp x.property
    have two : (B.neighborFinset x.val).card = 2 := by
      rw [B.card_neighborFinset_eq_degree, hx.2]
    obtain ⟨a, b, different, pair⟩ := Finset.card_eq_two.mp two
    have ha : B.Adj x.val a := (B.mem_neighborFinset _ _).mp (by rw [pair]; simp)
    have hb : B.Adj x.val b := (B.mem_neighborFinset _ _).mp (by rw [pair]; simp)
    have outsideA : a ∉ S := fun h => independent x.val hx.1 a h ha
    have outsideB : b ∉ S := fun h => independent x.val hx.1 b h hb
    exact ⟨⟨a, outsideA⟩, ⟨b, outsideB⟩, fun h => different (congrArg Subtype.val h),
      ha.symm, hb, pair⟩
  choose left right different adjacentL adjacentR pair using neighbors
  let f : active → (graph B S).edgeSet := fun x => ⟨s(left x, right x),
    (graph B S).mem_edgeSet.mpr ⟨different x, Or.inr
      ⟨x.val, (Finset.mem_filter.mp x.property).1, adjacentL x, adjacentR x⟩⟩⟩
  have injective : Function.Injective f := by
    intro x y equal
    have edge : s(left x, right x) = s(left y, right y) := congrArg Subtype.val equal
    have distinct : (left x).val ≠ (right x).val := fun h => different x (Subtype.ext h)
    apply Subtype.ext
    rcases Sym2.eq_iff.mp edge with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact middle_unique B forest distinct (adjacentL x) (adjacentR x)
        (by rw [hl]; exact adjacentL y) (by rw [hr]; exact adjacentR y)
    · exact middle_unique B forest distinct (adjacentL x) (adjacentR x)
        (by rw [hl]; exact (adjacentR y).symm) (by rw [hr]; exact (adjacentL y).symm)
  have surjective : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨u, v⟩ := e
    obtain ⟨differentUV, edge | ⟨x, hx, ux, xv⟩⟩ := (graph B S).mem_edgeSet.mp he
    · exact (coreIndependent u.val u.property v.val v.property edge).elim
    · have distinct : u.val ≠ v.val := fun h => differentUV (Subtype.ext h)
      have subset : {u.val, v.val} ⊆ B.neighborFinset x := by
        intro a ha
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using ha) with rfl | rfl
        · exact (B.mem_neighborFinset _ _).mpr ux.symm
        · exact (B.mem_neighborFinset _ _).mpr xv
      have lower := Finset.card_le_card subset
      rw [Finset.card_pair distinct, B.card_neighborFinset_eq_degree] at lower
      have two : B.degree x = 2 := Nat.le_antisymm (degree x hx) lower
      let a : active := ⟨x, Finset.mem_filter.mpr ⟨hx, two⟩⟩
      have hu : u = left a ∨ u = right a := by
        have member := (B.mem_neighborFinset _ _).mpr ux.symm
        rw [pair a] at member
        have cases : u.val = (left a).val ∨ u.val = (right a).val := by simpa using member
        exact cases.imp Subtype.ext Subtype.ext
      have hv : v = left a ∨ v = right a := by
        have member := (B.mem_neighborFinset _ _).mpr xv
        rw [pair a] at member
        have cases : v.val = (left a).val ∨ v.val = (right a).val := by simpa using member
        exact cases.imp Subtype.ext Subtype.ext
      refine ⟨a, Subtype.ext ?_⟩
      change s(left a, right a) = s(u, v)
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (differentUV rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (differentUV rfl).elim
  refine ⟨Equiv.ofBijective f ⟨injective, surjective⟩, fun x => ?_⟩
  exact ⟨left x, right x, rfl, adjacentL x, adjacentR x⟩

theorem edge_ncard_eq_degree_two (forest : B.IsAcyclic)
    (independent : ∀ u ∈ S, ∀ v ∈ S, ¬ B.Adj u v)
    (coreIndependent : ∀ u ∉ S, ∀ v ∉ S, ¬ B.Adj u v)
    (degree : ∀ v ∈ S, B.degree v ≤ 2) :
    (graph B S).edgeSet.ncard = (S.filter (fun v => B.degree v = 2)).card := by
  obtain ⟨f, _⟩ := exists_connection_equiv B S forest independent coreIndependent degree
  have count := Fintype.card_congr f
  rw [Fintype.card_coe, Set.fintypeCard_eq_ncard] at count
  exact count.symm

end Algebraic.Cutwidth.Bisection.RedBlack.PathSuppression.Internal
