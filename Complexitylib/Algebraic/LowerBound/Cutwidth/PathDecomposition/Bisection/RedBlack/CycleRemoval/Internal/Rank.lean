/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Reserving cycle rank for untouched cyclic components

Each cyclic connected component needs at least one edge beyond a spanning
tree. Reachability-preserving deletions and untouched cyclic components
therefore use disjoint portions of the original cycle rank. In the
thin-path argument, paths are shaded only inside large components, leaving
every small cyclic component available for this reservation.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

theorem card_vertices_add_cyclic_le (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic) :
    Fintype.card V + cyclic.card ≤ B.edgeFinset.card + Nat.card B.ConnectedComponent := by
  let : Fintype B.ConnectedComponent := Fintype.ofFinite _
  have localCount (C : B.ConnectedComponent) :
      2 * Fintype.card C + (if C ∈ cyclic then 2 else 0) ≤ (∑ v : C, B.degree v) + 2 := by
    have connected := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    simp only [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card] at connected
    have degrees : (∑ v : C, B.degree v) = 2 * C.toSimpleGraph.edgeFinset.card := by
      rw [← C.toSimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl
      intro v _
      exact (B.degree_induce_of_neighborSet_subset (v := v)
        (fun w hw => C.mem_supp_of_adj_mem_supp v.property hw)).symm
    rw [degrees]
    split_ifs with member
    · have distinct : C.toSimpleGraph.edgeFinset.card + 1 ≠ Fintype.card C := by
        intro equal
        apply cycles C member
        exact (SimpleGraph.isTree_iff_connected_and_card.mpr
          ⟨C.connected_toSimpleGraph, by simpa only [Nat.card_eq_fintype_card,
            ← SimpleGraph.edgeFinset_card] using equal⟩).isAcyclic
      lia
    · lia
  have total := Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) => localCount C)
  have vertices : (∑ C : B.ConnectedComponent, 2 * Fintype.card C) = 2 * Fintype.card V := by
    calc
      (∑ C : B.ConnectedComponent, 2 * Fintype.card C) =
          ∑ C : B.ConnectedComponent, ∑ _v : C, 2 := by simp [Nat.mul_comm]
      _ = ∑ _v : V, 2 := Fintype.sum_fiberwise B.connectedComponentMk (fun _ => 2)
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have degrees : (∑ C : B.ConnectedComponent, ∑ v : C, B.degree v) = ∑ v, B.degree v :=
    Fintype.sum_fiberwise B.connectedComponentMk (fun v : V => B.degree v)
  have reserved : (∑ C : B.ConnectedComponent, if C ∈ cyclic then 2 else 0) =
      2 * cyclic.card := by simp [Nat.mul_comm]
  simp only [Finset.sum_add_distrib] at total
  rw [vertices, reserved, degrees, B.sum_degrees_eq_twice_card_edges] at total
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at total
  rw [Nat.card_eq_fintype_card]
  lia

theorem card_removed_add_untouched_cyclic_le (removed : Finset (Sym2 V))
    (edges : removed ⊆ B.edgeFinset)
    (reachable : (B.deleteEdges (removed : Set (Sym2 V))).Reachable = B.Reachable)
    (cyclic : Finset B.ConnectedComponent)
    (cycles : ∀ C ∈ cyclic, ¬ C.toSimpleGraph.IsAcyclic)
    (kept : ∀ C ∈ cyclic, ∀ {u v}, u ∈ C.supp → v ∈ C.supp →
      B.Adj u v → s(u, v) ∉ removed) :
    removed.card + cyclic.card + Fintype.card V ≤
      B.edgeFinset.card + Nat.card B.ConnectedComponent := by
  let G := B.deleteEdges (removed : Set (Sym2 V))
  let component (C : B.ConnectedComponent) := G.connectedComponentMk C.out
  have support (C : B.ConnectedComponent) : (component C).supp = C.supp := by
    ext v
    rw [(component C).mem_supp_iff, C.mem_supp_iff]
    change G.connectedComponentMk v = G.connectedComponentMk C.out ↔ B.connectedComponentMk v = C
    calc
      _ ↔ G.Reachable v C.out := SimpleGraph.ConnectedComponent.eq
      _ ↔ B.Reachable v C.out := by rw [reachable]
      _ ↔ B.connectedComponentMk v = B.connectedComponentMk C.out :=
        SimpleGraph.ConnectedComponent.eq.symm
      _ ↔ B.connectedComponentMk v = C := by
        have representative : B.connectedComponentMk C.out = C := C.out_eq
        rw [representative]
  have injective : Function.Injective component := by
    intro C D equal
    apply SimpleGraph.ConnectedComponent.supp_injective
    rw [← support C, ← support D, equal]
  have remaining : ∀ D ∈ cyclic.image component, ¬ D.toSimpleGraph.IsAcyclic := by
    intro D hd
    obtain ⟨C, hc, rfl⟩ := Finset.mem_image.mp hd
    intro forest
    let hom : C.toSimpleGraph →g (component C).toSimpleGraph := {
      toFun := fun v => ⟨v.val, by
        change v.val ∈ (component C).supp
        rw [support]
        exact v.property⟩
      map_rel' := fun {u v} adjacent =>
        SimpleGraph.deleteEdges_adj.mpr ⟨adjacent, kept C hc u.property v.property adjacent⟩ }
    have homInjective : Function.Injective hom := by
      intro u v equal
      apply Subtype.ext
      exact congrArg (fun w : component C => w.val) equal
    exact cycles C hc (forest.comap hom homInjective)
  have lower := card_vertices_add_cyclic_le G (cyclic.image component) remaining
  rw [Finset.card_image_of_injective _ injective] at lower
  have components : Nat.card G.ConnectedComponent = Nat.card B.ConnectedComponent := by
    unfold SimpleGraph.ConnectedComponent
    rw [reachable]
  rw [components, SimpleGraph.edgeFinset_deleteEdges] at lower
  have count := Finset.card_sdiff_add_card_eq_card edges
  lia

end Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal
