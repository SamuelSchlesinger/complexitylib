/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal.SpanningPath
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Improvement.Internal

/-!
# Constructing the degree-two regions

Induced connected components partition the eligible vertices, with no
black edges between distinct regions. Their boundary cuts are therefore
pairwise disjoint. Degree at most two gives a spanning path and at most
two boundary edges; degree exactly two makes the boundary size even.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V : Type} (B : SimpleGraph V) (U : Finset V)

theorem mem_region (C : (B.induce {v | v ∈ U}).ConnectedComponent) {v : V} :
    v ∈ region B U C ↔ ∃ h : v ∈ U, (⟨v, h⟩ : {v // v ∈ U}) ∈ C.supp := by
  constructor
  · intro hv
    obtain ⟨w, member, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨w.property, Set.mem_toFinset.mp member⟩
  · rintro ⟨h, member⟩
    exact Finset.mem_image.mpr ⟨⟨v, h⟩, Set.mem_toFinset.mpr member, rfl⟩

theorem region_subset (C : (B.induce {v | v ∈ U}).ConnectedComponent) : region B U C ⊆ U :=
  fun _ hv => ((mem_region B U C).mp hv).choose

theorem region_connected (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.induce {v | v ∈ region B U C}).Connected := by
  let hom : C.toSimpleGraph →g B.induce {v | v ∈ region B U C} :=
    ⟨fun v => ⟨v.val.val, (mem_region B U C).mpr ⟨v.val.property, v.property⟩⟩, fun h => h⟩
  apply C.connected_toSimpleGraph.map hom
  intro v
  obtain ⟨hv, member⟩ := (mem_region B U C).mp v.property
  exact ⟨⟨⟨v.val, hv⟩, member⟩, rfl⟩

theorem exists_mem_region {v : V} :
    (∃ C : (B.induce {v | v ∈ U}).ConnectedComponent, v ∈ region B U C) ↔ v ∈ U := by
  constructor
  · rintro ⟨C, member⟩
    exact region_subset B U C member
  · intro hv
    refine ⟨(B.induce {v | v ∈ U}).connectedComponentMk ⟨v, hv⟩,
      (mem_region B U _).mpr ⟨hv, ?_⟩⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem region_disjoint : Pairwise
    (fun C D : (B.induce {v | v ∈ U}).ConnectedComponent =>
      Disjoint (region B U C) (region B U D)) := by
  intro C D different
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨_, hc⟩ := (mem_region B U C).mp hv
  obtain ⟨_, hd⟩ := (mem_region B U D).mp hw
  exact different (SimpleGraph.ConnectedComponent.eq_of_common_vertex hc hd)

theorem eq_of_adj {C D : (B.induce {v | v ∈ U}).ConnectedComponent} {v w : V}
    (hv : v ∈ region B U C) (hw : w ∈ region B U D) (adjacent : B.Adj v w) : C = D := by
  obtain ⟨hv, hc⟩ := (mem_region B U C).mp hv
  obtain ⟨hw, hd⟩ := (mem_region B U D).mp hw
  exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
    (C.mem_supp_of_adj_mem_supp hc (show (B.induce {v | v ∈ U}).Adj ⟨v, hv⟩ ⟨w, hw⟩ from
      adjacent)) hd

variable [Fintype V]

theorem cut_disjoint : Pairwise
    (fun C D : (B.induce {v | v ∈ U}).ConnectedComponent =>
      Disjoint (B.cutFinset (region B U C)) (B.cutFinset (region B U D))) := by
  intro C D different
  apply Finset.disjoint_left.mpr
  intro e
  induction e using Sym2.ind with
  | _ a b =>
    intro hc hd
    rcases B.mem_cutFinset_mk.mp hc with ⟨adjacent, ⟨ha, _⟩ | ⟨hb, _⟩⟩ <;>
      rcases (B.mem_cutFinset_mk.mp hd).2 with ⟨ha', _⟩ | ⟨hb', _⟩
    · exact Finset.disjoint_left.mp (region_disjoint B U different) ha ha'
    · exact different (eq_of_adj B U ha hb' adjacent)
    · exact different (eq_of_adj B U hb ha' adjacent.symm)
    · exact Finset.disjoint_left.mp (region_disjoint B U different) hb hb'

theorem exists_distinct_boundary_edges
    (components : Finset (B.induce {v | v ∈ U}).ConnectedComponent)
    (boundary : ∀ C ∈ components, (B.cutFinset (region B U C)).Nonempty) :
    ∃ chosen : components → Sym2 V, Function.Injective chosen ∧
      ∀ C : components, chosen C ∈ B.cutFinset (region B U C.val) := by
  choose chosen member using fun C : components => boundary C C.property
  refine ⟨chosen, fun C D equal => ?_, member⟩
  apply Subtype.ext
  by_contra different
  exact Finset.disjoint_left.mp (cut_disjoint B U different) (member C)
    (by rw [equal]; exact member D)

theorem region_spanning_path (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    ∃ (u v : V) (p : B.Walk u v), p.IsPath ∧ p.support.toFinset = region B U C :=
  exists_spanning_path_in_region B (region_connected B U C)
    (fun v hv => degree v (region_subset B U C hv))

theorem card_cut_le_two (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.cutFinset (region B U C)).card ≤ 2 :=
  card_cut_le_two_of_connected B (region_connected B U C)
    (fun v hv => degree v (region_subset B U C hv))

theorem card_cut_eq_zero_or_two (degree : ∀ v ∈ U, B.degree v = 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent) :
    (B.cutFinset (region B U C)).card = 0 ∨ (B.cutFinset (region B U C)).card = 2 := by
  have bound := card_cut_le_two B U (fun v hv => (degree v hv).le) C
  have count := Bisection.Internal.degree_sum_cut B (region B U C)
  have sum : (∑ v ∈ region B U C, B.degree v) = 2 * (region B U C).card := by
    calc
      _ = ∑ _v ∈ region B U C, 2 := Finset.sum_congr rfl
        (fun v hv => degree v (region_subset B U C hv))
      _ = _ := by simp [Nat.mul_comm]
  rw [sum] at count
  lia

theorem region_isTree (degree : ∀ v ∈ U, B.degree v ≤ 2)
    (C : (B.induce {v | v ∈ U}).ConnectedComponent)
    (boundary : (B.cutFinset (region B U C)).Nonempty) :
    (B.induce {v | v ∈ region B U C}).IsTree := by
  have connected := region_connected B U C
  have lower := connected.card_vert_le_card_edgeSet_add_one
  have count := Bisection.Internal.degree_sum_cut B (region B U C)
  have positive := Finset.card_pos.mpr boundary
  have sum : (∑ v ∈ region B U C, B.degree v) ≤ 2 * (region B U C).card := by
    calc
      _ ≤ ∑ _v ∈ region B U C, 2 := Finset.sum_le_sum
        (fun v hv => degree v (region_subset B U C hv))
      _ = _ := by simp [Nat.mul_comm]
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  have vertices : Fintype.card {v | v ∈ region B U C} = (region B U C).card :=
    Fintype.card_of_finset' _ (fun _ => Iff.rfl)
  simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at lower ⊢
  rw [vertices] at lower ⊢
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
