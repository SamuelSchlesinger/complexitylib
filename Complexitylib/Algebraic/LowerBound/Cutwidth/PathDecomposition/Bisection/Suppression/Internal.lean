/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Suppression.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.BoundaryLift.Internal

/-!
# Constructing and counting the suppressed red graph

The two-neighbor lemma constructs each red edge. Incidence bijections
identify its degree and internal-edge counts with the boundary counts in
the helpfulness lift.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.Internal

open scoped Classical

variable {W : Type} [Fintype W] (H : SimpleGraph W)

theorem exists_boundarySuppression {S : Finset W} (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d) :
    Nonempty (BoundarySuppression H S) := by
  let D := S \ cutBoundary H S
  let N (c : {c : W // c ∈ cutBoundary H S}) :=
    (H.neighborFinset c.val).subtype (fun v => v ∈ D)
  have two (c : {c : W // c ∈ cutBoundary H S}) : (N c).card = 2 := by
    dsimp only [N]
    rw [Finset.card_subtype]
    have same : (H.neighborFinset c.val).filter (fun v => v ∈ D) =
        H.neighborFinset c.val ∩ D := by ext v; simp
    rw [same]
    exact card_boundary_interior_neighbors H regular outside independent c.property
  have pairs (c : {c : W // c ∈ cutBoundary H S}) :
      ∃ a b, a ≠ b ∧ N c = {a, b} := Finset.card_eq_two.mp (two c)
  choose a b distinct pair using pairs
  refine ⟨⟨⟨a, b⟩, distinct, ?_⟩⟩
  intro v c
  change (a c = v ∨ b c = v) ↔ H.Adj c.val v.val
  have neighbors : v ∈ N c ↔ H.Adj c.val v.val := by
    simp only [N, Finset.mem_subtype, SimpleGraph.mem_neighborFinset]
  rw [pair c] at neighbors
  simp only [Finset.mem_insert, Finset.mem_singleton] at neighbors
  exact (or_congr eq_comm eq_comm).trans neighbors

theorem BoundarySuppression.red_degree {S : Finset W} (Q : BoundarySuppression H S)
    (v : {v : W // v ∈ S \ cutBoundary H S}) :
    Q.red.degree v = (H.neighborFinset v.val ∩ cutBoundary H S).card := by
  have same : (Q.red.edgesAt v).map (Function.Embedding.subtype _) =
      H.neighborFinset v.val ∩ cutBoundary H S := by
    ext c
    constructor
    · intro hc
      obtain ⟨c, hcEdge, rfl⟩ := Finset.mem_map.mp hc
      exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr
        ((Q.incident_iff v c).mp ((Q.red.mem_edgesAt).mp hcEdge)).symm, c.property⟩
    · intro hc
      obtain ⟨adj, hcC⟩ := Finset.mem_inter.mp hc
      refine Finset.mem_map.mpr ⟨⟨c, hcC⟩, ?_, rfl⟩
      exact Q.red.mem_edgesAt.mpr ((Q.incident_iff _ _).mpr
        ((H.mem_neighborFinset _ _).mp adj).symm)
  have count := congrArg Finset.card same
  rwa [Finset.card_map] at count

theorem boundaryInterior_degree {S : Finset W} (v : {v : W // v ∈ S \ cutBoundary H S}) :
    (H.induce {v | v ∈ S \ cutBoundary H S}).degree v =
      (H.neighborFinset v.val ∩ (S \ cutBoundary H S)).card := by
  have count := congrArg Finset.card
    (H.map_neighborFinset_induce (s := {v | v ∈ S \ cutBoundary H S}) v)
  rw [Finset.card_map] at count
  change ((H.induce {v | v ∈ S \ cutBoundary H S}).neighborFinset v).card = _
  convert count using 1 <;> congr 1 <;> ext w <;> simp

theorem BoundarySuppression.degree_sum {S : Finset W} (Q : BoundarySuppression H S)
    (regular : H.IsRegularOfDegree 3) (v : {v : W // v ∈ S \ cutBoundary H S}) :
    (H.induce {v | v ∈ S \ cutBoundary H S}).degree v + Q.red.degree v = 3 := by
  rw [BoundarySuppression.red_degree H Q, boundaryInterior_degree H]
  have count := card_interior_neighbors H regular v.property
  lia

private theorem two_le_card_filter_incident_iff {V E : Type} (R : Multigraph V E)
    (loopless : R.Loopless) (X : Finset V) (e : E) :
    2 ≤ (X.filter (fun v => R.Incident v e)).card ↔ R.fst e ∈ X ∧ R.snd e ∈ X := by
  have same : X.filter (fun v => R.Incident v e) = X ∩ {R.fst e, R.snd e} := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvX, h | h⟩ := Finset.mem_filter.mp hv
      · exact Finset.mem_inter.mpr ⟨hvX, Finset.mem_insert.mpr (Or.inl h.symm)⟩
      · exact Finset.mem_inter.mpr ⟨hvX,
          Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h.symm))⟩
    · intro hv
      obtain ⟨hvX, hvPair⟩ := Finset.mem_inter.mp hv
      refine Finset.mem_filter.mpr ⟨hvX, ?_⟩
      obtain h | h := Finset.mem_insert.mp hvPair
      · exact Or.inl h.symm
      · exact Or.inr (Finset.mem_singleton.mp h).symm
  rw [same]
  by_cases hfst : R.fst e ∈ X <;> by_cases hsnd : R.snd e ∈ X <;>
    simp [hfst, hsnd, loopless e]

theorem BoundarySuppression.internalEdges_card {S : Finset W} (Q : BoundarySuppression H S)
    (X : Finset {v : W // v ∈ S \ cutBoundary H S}) :
    (RedBlack.internalEdges Q.red X).card =
      (sharedBoundary H S (X.map (Function.Embedding.subtype _))).card := by
  let Y := X.map (Function.Embedding.subtype _)
  have count (c : {c : W // c ∈ cutBoundary H S}) :
      (X.filter (fun v => Q.red.Incident v c)).card = (H.neighborFinset c.val ∩ Y).card := by
    have same : (X.filter (fun v => Q.red.Incident v c)).map (Function.Embedding.subtype _) =
        H.neighborFinset c.val ∩ Y := by
      ext w
      constructor
      · intro hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
        obtain ⟨hvX, incident⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr
          ((Q.incident_iff v c).mp incident), Finset.mem_map.mpr ⟨v, hvX, rfl⟩⟩
      · intro hw
        obtain ⟨adj, hwY⟩ := Finset.mem_inter.mp hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hwY
        exact Finset.mem_map.mpr ⟨v, Finset.mem_filter.mpr ⟨hv,
          (Q.incident_iff v c).mpr ((H.mem_neighborFinset _ _).mp adj)⟩, rfl⟩
    simpa only [Finset.card_map] using congrArg Finset.card same
  have membership (c : {c : W // c ∈ cutBoundary H S}) :
      c ∈ RedBlack.internalEdges Q.red X ↔ c.val ∈ sharedBoundary H S Y := by
    rw [RedBlack.Internal.mem_internalEdges]
    have two := two_le_card_filter_incident_iff Q.red Q.loopless X c
    rw [count c] at two
    exact ⟨fun h => Finset.mem_filter.mpr ⟨c.property, two.mpr h⟩,
      fun h => two.mp (Finset.mem_filter.mp h).2⟩
  have same : (RedBlack.internalEdges Q.red X).map (Function.Embedding.subtype _) =
      sharedBoundary H S Y := by
    ext c
    constructor
    · intro hc
      obtain ⟨c, hcEdge, rfl⟩ := Finset.mem_map.mp hc
      exact (membership c).mp hcEdge
    · intro hc
      have hcC := (Finset.mem_filter.mp hc).1
      exact Finset.mem_map.mpr ⟨⟨c, hcC⟩, (membership ⟨c, hcC⟩).mpr hc, rfl⟩
  simpa only [Finset.card_map] using congrArg Finset.card same

theorem boundaryInterior_cut_card {S : Finset W}
    (X : Finset {v : W // v ∈ S \ cutBoundary H S}) :
    ((H.induce {v | v ∈ S \ cutBoundary H S}).cutFinset X).card =
      (H.cutFinset (X.map (Function.Embedding.subtype _)) \
        H.cutFinset (cutBoundary H S)).card := by
  let C := cutBoundary H S
  let D := S \ C
  let G := H.induce {v | v ∈ D}
  let Y := X.map (Function.Embedding.subtype _)
  have subset : Y ⊆ D := fun _ hw => X.property_of_mem_map_subtype hw
  have disjoint : Disjoint Y C := Finset.disjoint_left.mpr
    (fun _ hw hc => (Finset.mem_sdiff.mp (subset hw)).2 hc)
  have count (v : {v : W // v ∈ D}) :
      (G.neighborFinset v \ X).card = (H.neighborFinset v.val \ (Y ∪ C)).card := by
    have neighbors : (G.neighborFinset v).map (Function.Embedding.subtype _) =
        H.neighborFinset v.val ∩ D := by
      ext w
      constructor
      · intro hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
        exact Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr
          ((G.mem_neighborFinset v u).mp hu), u.property⟩
      · intro hw
        obtain ⟨adj, hwD⟩ := Finset.mem_inter.mp hw
        exact Finset.mem_map.mpr ⟨⟨w, hwD⟩,
          (G.mem_neighborFinset v ⟨w, hwD⟩).mpr ((H.mem_neighborFinset _ _).mp adj), rfl⟩
    have inside : H.neighborFinset v.val ⊆ S := by
      intro w hw
      by_contra hwS
      exact (Finset.mem_sdiff.mp v.property).2 ((mem_cutBoundary H).mpr
        ⟨(Finset.mem_sdiff.mp v.property).1, w, hwS, (H.mem_neighborFinset _ _).mp hw⟩)
    have same : (G.neighborFinset v \ X).map (Function.Embedding.subtype _) =
        H.neighborFinset v.val \ (Y ∪ C) := by
      rw [Finset.map_sdiff, neighbors]
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union, D]
      constructor
      · rintro ⟨⟨hw, hwS, hwC⟩, hwY⟩
        exact ⟨hw, by tauto⟩
      · rintro ⟨hw, hn⟩
        exact ⟨⟨hw, inside hw, fun hc => hn (Or.inr hc)⟩, fun hy => hn (Or.inl hy)⟩
    simpa only [Finset.card_map] using congrArg Finset.card same
  change (G.cutFinset X).card = (H.cutFinset Y \ H.cutFinset C).card
  rw [card_cutFinset_eq_sum_neighbors, card_cut_sdiff_cut_eq_sum H disjoint]
  dsimp only [Y]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v _
  convert count v using 1 <;> congr 1
  ext w
  simp

theorem BoundarySuppression.exists_helpful_set_of_positive {S : Finset W}
    (Q : BoundarySuppression H S) (regular : H.IsRegularOfDegree 3)
    (outside : ∀ c ∈ cutBoundary H S, (H.neighborFinset c \ S).card = 1)
    (independent : ∀ c ∈ cutBoundary H S, ∀ d ∈ cutBoundary H S, ¬ H.Adj c d)
    {X : Finset {v : W // v ∈ S \ cutBoundary H S}}
    (positive : RedBlack.Positive (H.induce {v | v ∈ S \ cutBoundary H S}) Q.red X) :
    ∃ Y ⊆ S, Y.card ≤ 4 * X.card ∧ 1 ≤ helpfulness H S Y := by
  have subset : X.map (Function.Embedding.subtype _) ⊆ S \ cutBoundary H S :=
    fun _ hw => X.property_of_mem_map_subtype hw
  have surplus : (H.cutFinset (X.map (Function.Embedding.subtype _)) \
      H.cutFinset (cutBoundary H S)).card <
        (sharedBoundary H S (X.map (Function.Embedding.subtype _))).card := by
    rw [← boundaryInterior_cut_card H X, ← BoundarySuppression.internalEdges_card H Q X]
    exact positive
  simpa only [Finset.card_map] using
    exists_helpful_set_of_red_surplus H regular outside independent subset surplus

end Algebraic.Cutwidth.Bisection.Internal
