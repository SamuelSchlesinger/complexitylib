/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Internal

/-!+# Small helpful configurations before normalization

Monien and Preis exclude several bounded configurations before switching
edges to normalize a side. The proofs below grow a set through adjacent
boundary vertices and count shared neighbors without assuming they are
distinct across different stars.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical symmDiff

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem helpfulness_insert {S X : Finset W} (hX : X ⊆ S) {v : W}
    (hv : v ∈ S) (fresh : v ∉ X) :
    helpfulness H S (insert v X) = helpfulness H S X +
      2 * ((H.neighborFinset v \ S).card : ℤ) - H.degree v +
      2 * ((H.neighborFinset v ∩ X).card : ℤ) := by
  have disjoint : Disjoint X {v} := Finset.disjoint_singleton_right.mpr fresh
  have move := helpfulness_add H S X {v}
  rw [Finset.symmDiff_eq_union disjoint, Finset.union_singleton,
    symmDiff_comm S X, symmDiff_of_le hX,
    helpfulness_singleton H (Finset.mem_sdiff.mpr ⟨hv, fresh⟩)] at move
  have partition : H.neighborFinset v \ (S \ X) =
      (H.neighborFinset v \ S) ∪ (H.neighborFinset v ∩ X) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  have separate : Disjoint (H.neighborFinset v \ S) (H.neighborFinset v ∩ X) :=
    Finset.disjoint_left.mpr (fun _ hw hx => (Finset.mem_sdiff.mp hw).2
      (hX (Finset.mem_inter.mp hx).2))
  rw [partition, Finset.card_union_of_disjoint separate] at move
  push_cast at move
  lia

private theorem outside_pos_of_boundary {S : Finset W} {c : W}
    (hc : c ∈ cutBoundary H S) : 1 ≤ (H.neighborFinset c \ S).card := by
  obtain ⟨_, w, hw, adj⟩ := (mem_cutBoundary H).mp hc
  exact Finset.card_pos.mpr ⟨w,
    Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset c w).mpr adj, hw⟩⟩

theorem helpfulness_insert_boundary {S X : Finset W} (hX : X ⊆ S) {c : W}
    (hc : c ∈ cutBoundary H S) (fresh : c ∉ X) (degree : H.degree c ≤ 3)
    (adjacent : ∃ x ∈ X, H.Adj c x) :
    helpfulness H S X + 1 ≤ helpfulness H S (insert c X) := by
  rw [helpfulness_insert H hX (cutBoundary_subset H S hc) fresh]
  have outside := outside_pos_of_boundary H hc
  have inside : 1 ≤ (H.neighborFinset c ∩ X).card := by
    obtain ⟨x, hx, adj⟩ := adjacent
    exact Finset.card_pos.mpr ⟨x,
      Finset.mem_inter.mpr ⟨(H.mem_neighborFinset c x).mpr adj, hx⟩⟩
  lia

private theorem helpfulness_union_boundary_disjoint {S X A : Finset W}
    (hX : X ⊆ S) (hA : A ⊆ cutBoundary H S) (disjoint : Disjoint X A)
    (degree : ∀ c ∈ A, H.degree c ≤ 3)
    (adjacent : ∀ c ∈ A, ∃ x ∈ X, H.Adj c x) :
    helpfulness H S X + A.card ≤ helpfulness H S (X ∪ A) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert c A fresh ih =>
      have subset : A ⊆ insert c A := Finset.subset_insert _ _
      have ih := ih (subset.trans hA) (disjoint.mono_right subset)
        (fun a ha => degree a (subset ha)) (fun a ha => adjacent a (subset ha))
      have hXA : X ∪ A ⊆ S :=
        Finset.union_subset hX ((subset.trans hA).trans (cutBoundary_subset H S))
      have new : c ∉ X ∪ A := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun hx => Finset.disjoint_left.mp disjoint hx (Finset.mem_insert_self _ _), fresh⟩
      have step := helpfulness_insert_boundary H hXA (hA (Finset.mem_insert_self _ _))
        new (degree c (Finset.mem_insert_self _ _)) (by
          obtain ⟨x, hx, adj⟩ := adjacent c (Finset.mem_insert_self _ _)
          exact ⟨x, Finset.mem_union_left _ hx, adj⟩)
      rw [Finset.union_insert, Finset.card_insert_of_notMem fresh]
      push_cast
      lia

theorem helpfulness_union_boundary {S X A : Finset W}
    (hX : X ⊆ S) (hA : A ⊆ cutBoundary H S)
    (degree : ∀ c ∈ A, H.degree c ≤ 3)
    (adjacent : ∀ c ∈ A, ∃ x ∈ X, H.Adj c x) :
    helpfulness H S X + (A \ X).card ≤ helpfulness H S (X ∪ A) := by
  have disjoint : Disjoint X (A \ X) :=
    Finset.disjoint_left.mpr (fun _ hx ha => (Finset.mem_sdiff.mp ha).2 hx)
  have result := helpfulness_union_boundary_disjoint H hX
    (Finset.sdiff_subset.trans hA) disjoint
    (fun c hc => degree c (Finset.mem_sdiff.mp hc).1)
    (fun c hc => adjacent c (Finset.mem_sdiff.mp hc).1)
  have same : X ∪ (A \ X) = X ∪ A := by ext c; simp
  simpa only [same] using result

theorem helpfulness_insert_boundary_neighbors {S X : Finset W} (hX : X ⊆ S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W} (hv : v ∈ S) (fresh : v ∉ X) :
    helpfulness H S X + 2 * ((H.neighborFinset v ∩ X).card : ℤ) - 3 +
      (((H.neighborFinset v ∩ cutBoundary H S) \ X).card : ℤ) ≤
        helpfulness H S (insert v (X ∪ (H.neighborFinset v ∩ cutBoundary H S))) := by
  have hInsert : insert v X ⊆ S := Finset.insert_subset hv hX
  have attached := helpfulness_union_boundary H hInsert
    (A := H.neighborFinset v ∩ cutBoundary H S) Finset.inter_subset_right
    (fun c hc => degree c (cutBoundary_subset H S (Finset.mem_inter.mp hc).2)) (by
      intro c hc
      exact ⟨v, Finset.mem_insert_self _ _,
        ((H.mem_neighborFinset v c).mp (Finset.mem_inter.mp hc).1).symm⟩)
  have same : (H.neighborFinset v ∩ cutBoundary H S) \ insert v X =
      (H.neighborFinset v ∩ cutBoundary H S) \ X := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_inter]
    constructor
    · tauto
    · rintro ⟨⟨adj, hc⟩, hx⟩
      refine ⟨⟨adj, hc⟩, ?_⟩
      rintro (rfl | hx')
      · exact H.loopless.irrefl _ ((H.mem_neighborFinset _ _).mp adj)
      · exact hx hx'
  rw [same, Finset.insert_union] at attached
  rw [helpfulness_insert H hX hv fresh] at attached
  have bound := degree v hv
  lia

theorem three_boundary_neighbors_extension {S X : Finset W} (hX : X ⊆ S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W} (hv : v ∈ S) (fresh : v ∉ X)
    (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3)
    (overlap : ((H.neighborFinset v ∩ cutBoundary H S) ∩ X).Nonempty) :
    (insert v (X ∪ (H.neighborFinset v ∩ cutBoundary H S))).card ≤ X.card + 3 ∧
      helpfulness H S X + 1 ≤
        helpfulness H S (insert v (X ∪ (H.neighborFinset v ∩ cutBoundary H S))) := by
  have gain := helpfulness_insert_boundary_neighbors H hX degree hv fresh
  have partition := Finset.card_sdiff_add_card_inter
    (H.neighborFinset v ∩ cutBoundary H S) X
  have nonempty := Finset.card_pos.mpr overlap
  have inside := Finset.card_le_card (show
      (H.neighborFinset v ∩ cutBoundary H S) ∩ X ⊆ H.neighborFinset v ∩ X from
    fun _ h => Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp h).1).1, (Finset.mem_inter.mp h).2⟩)
  have unionCount := Finset.card_union_add_card_inter X
    (H.neighborFinset v ∩ cutBoundary H S)
  rw [Finset.inter_comm X] at unionCount
  have size := Finset.card_insert_le v (X ∪ (H.neighborFinset v ∩ cutBoundary H S))
  constructor <;> lia

private theorem boundary_singleton_lower {S : Finset W} {c : W}
    (hc : c ∈ cutBoundary H S) (degree : H.degree c ≤ 3) :
    -1 ≤ helpfulness H S {c} := by
  rw [helpfulness_singleton H (cutBoundary_subset H S hc)]
  have outside := outside_pos_of_boundary H hc
  lia

theorem nonneg_helpfulness_boundary_pair {S : Finset W} {c d : W}
    (hc : c ∈ cutBoundary H S) (hd : d ∈ cutBoundary H S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) (adjacent : H.Adj c d) :
    0 ≤ helpfulness H S {c, d} := by
  have single := boundary_singleton_lower H hd (degree d (cutBoundary_subset H S hd))
  have step := helpfulness_insert_boundary H
    (Finset.singleton_subset_iff.mpr (cutBoundary_subset H S hd)) hc
    (by simpa only [Finset.mem_singleton] using adjacent.ne)
    (degree c (cutBoundary_subset H S hc)) ⟨d, Finset.mem_singleton_self _, adjacent⟩
  lia

theorem exists_helpful_of_boundary_pair_three_neighbors {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {c d v : W}
    (hc : c ∈ cutBoundary H S) (hd : d ∈ cutBoundary H S) (pair : H.Adj c d)
    (hv : v ∈ S \ cutBoundary H S) (adjacent : H.Adj v c)
    (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    ∃ X ⊆ S, X.card ≤ 5 ∧ 1 ≤ helpfulness H S X := by
  have seed : {c, d} ⊆ cutBoundary H S :=
    Finset.insert_subset hc (Finset.singleton_subset_iff.mpr hd)
  have fresh : v ∉ ({c, d} : Finset W) := fun h => (Finset.mem_sdiff.mp hv).2 (seed h)
  have extension := three_boundary_neighbors_extension H
    (seed.trans (cutBoundary_subset H S)) degree (Finset.mem_sdiff.mp hv).1 fresh three
    ⟨c, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v c).mpr adjacent, hc⟩,
        Finset.mem_insert_self _ _⟩⟩
  have neutral := nonneg_helpfulness_boundary_pair H hc hd degree pair
  have pairSize : ({c, d} : Finset W).card ≤ 2 := Finset.card_le_two
  refine ⟨insert v ({c, d} ∪ (H.neighborFinset v ∩ cutBoundary H S)), ?_, by lia, by lia⟩
  exact Finset.insert_subset (Finset.mem_sdiff.mp hv).1
    (Finset.union_subset (seed.trans (cutBoundary_subset H S))
      (Finset.inter_subset_right.trans (cutBoundary_subset H S)))

theorem exists_helpful_of_shared_boundary_neighbor {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {u v c : W}
    (hu : u ∈ S \ cutBoundary H S) (hv : v ∈ S \ cutBoundary H S) (distinct : u ≠ v)
    (hc : c ∈ cutBoundary H S) (adjU : H.Adj u c) (adjV : H.Adj v c)
    (threeU : (H.neighborFinset u ∩ cutBoundary H S).card = 3)
    (threeV : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    ∃ X ⊆ S, X.card ≤ 7 ∧ 1 ≤ helpfulness H S X := by
  have seed : {c} ⊆ cutBoundary H S := Finset.singleton_subset_iff.mpr hc
  have freshU : u ∉ ({c} : Finset W) := fun h => (Finset.mem_sdiff.mp hu).2 (seed h)
  let Y := insert u ({c} ∪ (H.neighborFinset u ∩ cutBoundary H S))
  have extensionU := three_boundary_neighbors_extension H
    (seed.trans (cutBoundary_subset H S)) degree (Finset.mem_sdiff.mp hu).1 freshU threeU
    ⟨c, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨(H.mem_neighborFinset u c).mpr adjU, hc⟩,
        Finset.mem_singleton_self _⟩⟩
  have location : Y ⊆ insert u (cutBoundary H S) :=
    Finset.insert_subset_insert u (Finset.union_subset seed Finset.inter_subset_right)
  have hY : Y ⊆ S := location.trans
    (Finset.insert_subset (Finset.mem_sdiff.mp hu).1 (cutBoundary_subset H S))
  have freshV : v ∉ Y := by
    intro h
    obtain eq | boundary := Finset.mem_insert.mp (location h)
    · exact distinct eq.symm
    · exact (Finset.mem_sdiff.mp hv).2 boundary
  have cY : c ∈ Y := Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  have extensionV := three_boundary_neighbors_extension H hY degree
    (Finset.mem_sdiff.mp hv).1 freshV threeV
    ⟨c, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v c).mpr adjV, hc⟩, cY⟩⟩
  have lower := boundary_singleton_lower H hc (degree c (cutBoundary_subset H S hc))
  change Y.card ≤ ({c} : Finset W).card + 3 ∧
    helpfulness H S {c} + 1 ≤ helpfulness H S Y at extensionU
  simp only [Finset.card_singleton] at extensionU
  refine ⟨insert v (Y ∪ (H.neighborFinset v ∩ cutBoundary H S)), ?_, by lia, by lia⟩
  exact Finset.insert_subset (Finset.mem_sdiff.mp hv).1
    (Finset.union_subset hY (Finset.inter_subset_right.trans (cutBoundary_subset H S)))

private theorem helpfulness_strict_mono_of_new_nonneg {S X Y : Finset W}
    (hX : X ⊆ S) (hY : Y ⊆ S) (inclusion : X ⊆ Y)
    (new : ∀ v ∈ Y \ X, (H.neighborFinset v \ Y).card ≤
      2 * (H.neighborFinset v \ S).card)
    (touch : ∃ x ∈ X, ∃ y ∈ Y \ X, H.Adj x y) :
    helpfulness H S X + 1 ≤ helpfulness H S Y := by
  let f (A : Finset W) (v : W) : ℤ :=
    2 * ((H.neighborFinset v \ S).card : ℤ) - (H.neighborFinset v \ A).card
  have decrease (v : W) : H.neighborFinset v \ Y ⊆ H.neighborFinset v \ X :=
    fun _ hw => Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp hw).1, fun hx => (Finset.mem_sdiff.mp hw).2 (inclusion hx)⟩
  have old : ∑ v ∈ X, f X v < ∑ v ∈ X, f Y v := by
    apply Finset.sum_lt_sum
    · intro v _
      have bound := Finset.card_le_card (decrease v)
      dsimp [f]
      lia
    · obtain ⟨x, hx, y, hy, adjacent⟩ := touch
      have strict : H.neighborFinset x \ Y ⊂ H.neighborFinset x \ X := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨decrease x, ?_⟩
        intro same
        have member : y ∈ H.neighborFinset x \ X := Finset.mem_sdiff.mpr
          ⟨(H.mem_neighborFinset x y).mpr adjacent, (Finset.mem_sdiff.mp hy).2⟩
        rw [← same] at member
        exact (Finset.mem_sdiff.mp member).2 (Finset.mem_sdiff.mp hy).1
      have bound := Finset.card_lt_card strict
      exact ⟨x, hx, by dsimp [f]; lia⟩
  have extra : 0 ≤ ∑ v ∈ Y \ X, f Y v := Finset.sum_nonneg (by
    intro v hv
    have bound := new v hv
    dsimp [f]
    lia)
  have total := Finset.sum_sdiff (f := f Y) inclusion
  rw [helpfulness_eq_sum_neighbors H hX, helpfulness_eq_sum_neighbors H hY]
  change (∑ v ∈ X, f X v) + 1 ≤ ∑ v ∈ Y, f Y v
  lia

theorem helpfulness_union_boundaryLift_of_closed {S X Z : Finset W}
    (hX : X ⊆ S) (hZ : Z ⊆ S \ cutBoundary H S)
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (closed : ∀ z ∈ Z, H.neighborFinset z ⊆ (X ∪ Z) ∪ cutBoundary H S)
    (touch : ∃ x ∈ X, ∃ z ∈ Z \ X, H.Adj x z) :
    helpfulness H S X + 1 ≤ helpfulness H S (X ∪ boundaryLift H S Z) := by
  let Y := X ∪ boundaryLift H S Z
  have hY : Y ⊆ S := Finset.union_subset hX
    (boundaryLift_subset H (hZ.trans Finset.sdiff_subset))
  have zY : Z ⊆ Y := fun z hz =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hz)
  apply helpfulness_strict_mono_of_new_nonneg H hX hY Finset.subset_union_left
  · intro v hv
    have member := Finset.mem_sdiff.mp hv
    have lift : v ∈ boundaryLift H S Z :=
      (Finset.mem_union.mp member.1).resolve_left member.2
    obtain interior | boundary := Finset.mem_union.mp lift
    · have neighbors : H.neighborFinset v ⊆ Y := by
        intro w hw
        obtain hxz | hc := Finset.mem_union.mp (closed v interior hw)
        · obtain hx | hz := Finset.mem_union.mp hxz
          · exact Finset.mem_union_left _ hx
          · exact zY hz
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hc, v, interior,
              ((H.mem_neighborFinset v w).mp hw).symm⟩))
      rw [Finset.sdiff_eq_empty_iff_subset.mpr neighbors, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨hc, z, hz, adjacent⟩ := Finset.mem_filter.mp boundary
      have outside := outside_pos_of_boundary H hc
      have inside : 1 ≤ (H.neighborFinset v ∩ Y).card := Finset.card_pos.mpr
        ⟨z, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v z).mpr adjacent, zY hz⟩⟩
      have count := Finset.card_sdiff_add_card_inter (H.neighborFinset v) Y
      rw [H.card_neighborFinset_eq_degree] at count
      have bound := degree v (cutBoundary_subset H S hc)
      lia
  · obtain ⟨x, hx, z, hz, adjacent⟩ := touch
    exact ⟨x, hx, z, Finset.mem_sdiff.mpr
      ⟨zY (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩, adjacent⟩

private theorem boundary_neighbors_of_adj_nonboundary {S : Finset W} {p v : W}
    (degree : H.degree p ≤ 3) (adjacent : H.Adj p v) (hv : v ∉ cutBoundary H S) :
    (H.neighborFinset p ∩ cutBoundary H S).card ≤ 2 ∧
      (2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card →
        H.neighborFinset p ⊆ insert v (cutBoundary H S)) := by
  let A := H.neighborFinset p ∩ cutBoundary H S
  have fresh : v ∉ A := fun h => hv (Finset.mem_inter.mp h).2
  have subset : insert v A ⊆ H.neighborFinset p :=
    Finset.insert_subset ((H.mem_neighborFinset p v).mpr adjacent) Finset.inter_subset_left
  have count := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem fresh, H.card_neighborFinset_eq_degree] at count
  refine ⟨by lia, ?_⟩
  intro two
  have same : insert v A = H.neighborFinset p :=
    Finset.eq_of_subset_of_card_le subset (by
      rw [Finset.card_insert_of_notMem fresh, H.card_neighborFinset_eq_degree]
      lia)
  rw [← same]
  exact Finset.insert_subset_insert v Finset.inter_subset_right

theorem exists_helpful_extension_of_neighbor_types {S X : Finset W}
    (hX : X ⊆ S) (neutral : 0 ≤ helpfulness H S X)
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W}
    (hv : v ∈ S \ cutBoundary H S) (fresh : v ∉ X)
    (touch : ∃ x ∈ X, H.Adj v x)
    (neighbors : ∀ p, H.Adj v p → p ∉ X → p ∈ cutBoundary H S ∨
      (p ∈ S \ cutBoundary H S ∧ 2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card)) :
    ∃ Y ⊆ S, Y.card ≤ X.card + 7 ∧ 1 ≤ helpfulness H S Y := by
  let N := H.neighborFinset v \ X
  let Z := insert v (N \ cutBoundary H S)
  let Y := X ∪ boundaryLift H S Z
  have typeN (p : W) (hp : p ∈ N) := neighbors p
    ((H.mem_neighborFinset v p).mp (Finset.mem_sdiff.mp hp).1) (Finset.mem_sdiff.mp hp).2
  have hNS (p : W) (hp : p ∈ N) : p ∈ S := by
    obtain hc | hi := typeN p hp
    · exact cutBoundary_subset H S hc
    · exact (Finset.mem_sdiff.mp hi.1).1
  have hZ : Z ⊆ S \ cutBoundary H S := by
    apply Finset.insert_subset hv
    intro p hp
    exact ((typeN p (Finset.mem_sdiff.mp hp).1).resolve_left (Finset.mem_sdiff.mp hp).2).1
  have boundaryCount (p : W) (hp : p ∈ N) := boundary_neighbors_of_adj_nonboundary H
    (degree p (hNS p hp))
    ((H.mem_neighborFinset v p).mp (Finset.mem_sdiff.mp hp).1).symm
    (Finset.mem_sdiff.mp hv).2
  have closed (z : W) (hz : z ∈ Z) :
      H.neighborFinset z ⊆ (X ∪ Z) ∪ cutBoundary H S := by
    obtain rfl | hz := Finset.mem_insert.mp hz
    · intro p hp
      by_cases old : p ∈ X
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ old)
      by_cases boundary : p ∈ cutBoundary H S
      · exact Finset.mem_union_right _ boundary
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨hp, old⟩, boundary⟩)))
    · obtain ⟨hzN, hzC⟩ := Finset.mem_sdiff.mp hz
      have two := ((typeN z hzN).resolve_left hzC).2
      intro p hp
      obtain rfl | hc := Finset.mem_insert.mp ((boundaryCount z hzN).2 two hp)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      · exact Finset.mem_union_right _ hc
  have gain := helpfulness_union_boundaryLift_of_closed H hX hZ degree closed (by
    obtain ⟨x, hx, adjacent⟩ := touch
    exact ⟨x, hx, v, Finset.mem_sdiff.mpr
      ⟨Finset.mem_insert_self _ _, fresh⟩, adjacent.symm⟩)
  have hY : Y ⊆ S := Finset.union_subset hX
    (boundaryLift_subset H (hZ.trans Finset.sdiff_subset))
  have smallN : N.card ≤ 2 := by
    obtain ⟨x, hx, adjacent⟩ := touch
    have inside : 1 ≤ (H.neighborFinset v ∩ X).card := Finset.card_pos.mpr
      ⟨x, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset v x).mpr adjacent, hx⟩⟩
    have count := Finset.card_sdiff_add_card_inter (H.neighborFinset v) X
    rw [H.card_neighborFinset_eq_degree] at count
    have bound := degree v (Finset.mem_sdiff.mp hv).1
    dsimp [N]
    lia
  let A (p : W) := insert p (H.neighborFinset p ∩ cutBoundary H S)
  have smallA (p : W) (hp : p ∈ N) : (A p).card ≤ 3 := by
    have count := Finset.card_insert_le p (H.neighborFinset p ∩ cutBoundary H S)
    have two := (boundaryCount p hp).1
    dsimp [A]
    lia
  have pA (p : W) (hp : p ∈ N) : p ∈ N.biUnion A :=
    Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_insert_self _ _⟩
  have cover : Y ⊆ insert v (X ∪ N.biUnion A) := by
    intro w hw
    obtain hx | lift := Finset.mem_union.mp hw
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    obtain hz | hc := Finset.mem_union.mp lift
    · obtain rfl | hz := Finset.mem_insert.mp hz
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (pA w (Finset.mem_sdiff.mp hz).1))
    · obtain ⟨hc, z, hz, adjacent⟩ := Finset.mem_filter.mp hc
      obtain rfl | hz := Finset.mem_insert.mp hz
      · by_cases old : w ∈ X
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ old)
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (pA w (Finset.mem_sdiff.mpr
            ⟨(H.mem_neighborFinset _ _).mpr adjacent.symm, old⟩)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨z, (Finset.mem_sdiff.mp hz).1,
            Finset.mem_insert_of_mem (Finset.mem_inter.mpr
              ⟨(H.mem_neighborFinset z w).mpr adjacent.symm, hc⟩)⟩))
  have coverCount := Finset.card_le_card cover
  have insertCount := Finset.card_insert_le v (X ∪ N.biUnion A)
  have unionCount := Finset.card_union_le X (N.biUnion A)
  have biUnionCount := Finset.card_biUnion_le (s := N) (t := A)
  have sumCount := Finset.sum_le_sum smallA
  simp only [Finset.sum_const, nsmul_eq_mul] at sumCount
  exact ⟨Y, hY, by lia, by lia⟩

theorem nonneg_helpfulness_boundary_star {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v : W} (hv : v ∈ S)
    (three : (H.neighborFinset v ∩ cutBoundary H S).card = 3) :
    0 ≤ helpfulness H S (insert v (H.neighborFinset v ∩ cutBoundary H S)) := by
  have gain := helpfulness_insert_boundary_neighbors H (Finset.empty_subset S) degree hv
    (Finset.notMem_empty v)
  have empty : helpfulness H S ∅ = 0 := by simp [helpfulness, SimpleGraph.cutFinset]
  simpa [empty, three] using gain

theorem exists_helpful_of_boundary_neighbor_configuration {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3) {v c : W}
    (hv : v ∈ S \ cutBoundary H S) (hc : c ∈ cutBoundary H S) (adjacent : H.Adj v c)
    (anchor : (∃ d ∈ cutBoundary H S, H.Adj c d) ∨
      ∃ u ∈ S \ cutBoundary H S, u ≠ v ∧ H.Adj c u ∧
        (H.neighborFinset u ∩ cutBoundary H S).card = 3)
    (neighbors : ∀ p, H.Adj v p → p ≠ c → p ∈ cutBoundary H S ∨
      (p ∈ S \ cutBoundary H S ∧ 2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card)) :
    ∃ Y ⊆ S, Y.card ≤ 11 ∧ 1 ≤ helpfulness H S Y := by
  obtain pair | star := anchor
  · obtain ⟨d, hd, pair⟩ := pair
    have seed : {c, d} ⊆ cutBoundary H S :=
      Finset.insert_subset hc (Finset.singleton_subset_iff.mpr hd)
    have fresh : v ∉ ({c, d} : Finset W) := fun h => (Finset.mem_sdiff.mp hv).2 (seed h)
    obtain ⟨Y, hY, size, gain⟩ := exists_helpful_extension_of_neighbor_types H
      (seed.trans (cutBoundary_subset H S))
      (nonneg_helpfulness_boundary_pair H hc hd degree pair) degree hv fresh
      ⟨c, Finset.mem_insert_self _ _, adjacent⟩ (by
        intro p adj hp
        exact neighbors p adj (fun eq => hp (eq ▸ Finset.mem_insert_self _ _)))
    have seedSize : ({c, d} : Finset W).card ≤ 2 := Finset.card_le_two
    exact ⟨Y, hY, by lia, gain⟩
  · obtain ⟨u, hu, distinct, cu, three⟩ := star
    let X := insert u (H.neighborFinset u ∩ cutBoundary H S)
    have hX : X ⊆ S := Finset.insert_subset (Finset.mem_sdiff.mp hu).1
      (Finset.inter_subset_right.trans (cutBoundary_subset H S))
    have cX : c ∈ X := Finset.mem_insert_of_mem
      (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset u c).mpr cu.symm, hc⟩)
    have fresh : v ∉ X := by
      intro h
      obtain eq | boundary := Finset.mem_insert.mp h
      · exact distinct eq.symm
      · exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp boundary).2
    have neutral := nonneg_helpfulness_boundary_star H degree (Finset.mem_sdiff.mp hu).1 three
    obtain ⟨Y, hY, size, gain⟩ := exists_helpful_extension_of_neighbor_types H hX neutral
      degree hv fresh ⟨c, cX, adjacent⟩ (by
        intro p adj hp
        exact neighbors p adj (fun eq => hp (eq ▸ cX)))
    have seedSize := Finset.card_insert_le u (H.neighborFinset u ∩ cutBoundary H S)
    change Y.card ≤ X.card + 7 at size
    dsimp [X] at size
    exact ⟨Y, hY, by lia, gain⟩

theorem exists_switch_neighbor {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0) {v c : W}
    (hv : v ∈ S \ cutBoundary H S) (hc : c ∈ cutBoundary H S) (adjacent : H.Adj v c)
    (anchor : (∃ d ∈ cutBoundary H S, H.Adj c d) ∨
      ∃ u ∈ S \ cutBoundary H S, u ≠ v ∧ H.Adj c u ∧
        (H.neighborFinset u ∩ cutBoundary H S).card = 3) :
    ∃ p, H.Adj v p ∧ p ≠ c ∧ p ∈ S \ cutBoundary H S ∧
      (H.neighborFinset p ∩ cutBoundary H S).card ≤ 1 := by
  by_contra absent
  have neighbors (p : W) (adj : H.Adj v p) (distinct : p ≠ c) :
      p ∈ cutBoundary H S ∨
        (p ∈ S \ cutBoundary H S ∧ 2 ≤ (H.neighborFinset p ∩ cutBoundary H S).card) := by
    by_cases boundary : p ∈ cutBoundary H S
    · exact Or.inl boundary
    have inside : p ∈ S := by
      by_contra outside
      exact (Finset.mem_sdiff.mp hv).2 ((mem_cutBoundary H).mpr
        ⟨(Finset.mem_sdiff.mp hv).1, p, outside, adj⟩)
    have interior := Finset.mem_sdiff.mpr ⟨inside, boundary⟩
    have many : ¬ (H.neighborFinset p ∩ cutBoundary H S).card ≤ 1 :=
      fun small => absent ⟨p, adj, distinct, interior, small⟩
    exact Or.inr ⟨interior, by lia⟩
  obtain ⟨Y, hY, size, gain⟩ :=
    exists_helpful_of_boundary_neighbor_configuration H degree hv hc adjacent anchor neighbors
  have bound := noHelpful Y hY size
  lia

theorem outside_eq_one_of_no_small_helpful {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {c : W} (hc : c ∈ cutBoundary H S) : (H.neighborFinset c \ S).card = 1 := by
  have positive := outside_pos_of_boundary H hc
  by_contra different
  have two : 2 ≤ (H.neighborFinset c \ S).card := by lia
  have hcS := cutBoundary_subset H S hc
  have gain := one_le_helpfulness_singleton H hcS (degree c hcS) two
  have bound := noHelpful {c} (Finset.singleton_subset_iff.mpr hcS) (by simp)
  lia

theorem boundary_degree_le_one_of_no_small_helpful {S : Finset W}
    (degree : ∀ v ∈ S, H.degree v ≤ 3)
    (noHelpful : ∀ X ⊆ S, X.card ≤ 11 → helpfulness H S X ≤ 0)
    {c : W} (hc : c ∈ cutBoundary H S) :
    (H.neighborFinset c ∩ cutBoundary H S).card ≤ 1 := by
  by_contra many
  obtain ⟨p, hp, q, hq, distinct⟩ := Finset.one_lt_card.mp (by lia :
    1 < (H.neighborFinset c ∩ cutBoundary H S).card)
  have cp := (H.mem_neighborFinset c p).mp (Finset.mem_inter.mp hp).1
  have cq := (H.mem_neighborFinset c q).mp (Finset.mem_inter.mp hq).1
  have hpC := (Finset.mem_inter.mp hp).2
  have hqC := (Finset.mem_inter.mp hq).2
  have seed : {c, p} ⊆ cutBoundary H S :=
    Finset.insert_subset hc (Finset.singleton_subset_iff.mpr hpC)
  have fresh : q ∉ ({c, p} : Finset W) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨cq.ne.symm, distinct.symm⟩
  have neutral := nonneg_helpfulness_boundary_pair H hc hpC degree cp
  have gain := helpfulness_insert_boundary H (seed.trans (cutBoundary_subset H S)) hqC fresh
    (degree q (cutBoundary_subset H S hqC)) ⟨c, Finset.mem_insert_self _ _, cq.symm⟩
  have bound := noHelpful {q, c, p}
    (Finset.insert_subset (cutBoundary_subset H S hqC) (seed.trans (cutBoundary_subset H S)))
    (Finset.card_le_three.trans (by decide))
  lia

end Algebraic.Cutwidth.Bisection.Internal
