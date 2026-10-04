/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.CycleRemoval.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.Restoration.Internal

/-!
# Connectivity outside the isolated regions

After deleting one boundary edge of a region with at most two boundary
edges, its remaining boundary has size at most one. A simple path between
vertices outside that region cannot enter it and leave again: that would
repeat its sole boundary edge. Deleting the remaining boundary therefore
preserves reachability between outside vertices. This works for a whole
family simultaneously and supplies the core-connectivity invariant in
Monien and Preis's cycle-removal step.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

theorem mem_of_reachable_of_cut_empty {P : Finset V} (closed : B.cutFinset P = ∅)
    {u v : V} (reachable : B.Reachable u v) (member : u ∈ P) : v ∈ P := by
  obtain ⟨p⟩ := reachable
  induction p with
  | nil => exact member
  | @cons a b c adjacent p ih =>
    apply ih
    by_contra outside
    have crossing := B.mem_cutFinset_mk.mpr ⟨adjacent, Or.inl ⟨member, outside⟩⟩
    rw [closed] at crossing
    exact Finset.notMem_empty _ crossing

theorem trail_avoids_cut_of_card_le_one {P : Finset V} (one : (B.cutFinset P).card ≤ 1)
    {u v : V} {p : B.Walk u v} (trail : p.IsTrail) (hu : u ∉ P) (hv : v ∉ P)
    {e : Sym2 V} (boundary : e ∈ B.cutFinset P) : e ∉ p.edges := by
  obtain ⟨_, a, b, rfl, ha, _⟩ := B.mem_cutFinset.mp boundary
  have only : B.cutFinset P ⊆ {s(a, b)} := fun f hf =>
    Finset.mem_singleton.mpr (Finset.card_le_one.mp one f hf _ boundary)
  have closed : (B.deleteEdges {s(a, b)}).cutFinset P = ∅ := by
    have same := RedBlack.Internal.cut_deleteEdges B {s(a, b)} P
    simpa using same.trans (Finset.sdiff_eq_empty_iff_subset.mpr only)
  have separated {w : V} (hw : w ∉ P) : ¬ (B.deleteEdges {s(a, b)}).Reachable w a := by
    intro reaches
    exact hw (mem_of_reachable_of_cut_empty _ closed reaches.symm ha)
  have avoided := trail.notMem_edges_of_not_reachable
    (x := b) (y := a) (by simpa only [Sym2.eq_swap] using separated hu)
    (by simpa only [Sym2.eq_swap] using separated hv)
  simpa only [Sym2.eq_swap] using avoided

theorem cut_card_le_one_after_chosen_deletion {ι : Type} (P : ι → Finset V)
    (chosen : ι → Sym2 V) (indices : Finset ι)
    (two : ∀ i ∈ indices, (B.cutFinset (P i)).card ≤ 2)
    (boundary : ∀ i ∈ indices, chosen i ∈ B.cutFinset (P i)) {i : ι} (hi : i ∈ indices) :
    ((B.deleteEdges (indices.image chosen : Set (Sym2 V))).cutFinset (P i)).card ≤ 1 := by
  rw [RedBlack.Internal.cut_deleteEdges]
  have subset : B.cutFinset (P i) \ indices.image chosen ⊆
      (B.cutFinset (P i)).erase (chosen i) := by
    intro e he
    obtain ⟨member, fresh⟩ := Finset.mem_sdiff.mp he
    apply Finset.mem_erase.mpr
    refine ⟨?_, member⟩
    rintro rfl
    exact fresh (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have count := Finset.card_erase_add_one (boundary i hi)
  have bound := Finset.card_le_card subset
  have := two i hi
  lia

theorem reachable_after_isolating {ι : Type} (P : ι → Finset V)
    (chosen : ι → Sym2 V) (indices : Finset ι)
    (two : ∀ i ∈ indices, (B.cutFinset (P i)).card ≤ 2)
    (boundary : ∀ i ∈ indices, chosen i ∈ B.cutFinset (P i))
    (preserved : (B.deleteEdges (indices.image chosen : Set (Sym2 V))).Reachable = B.Reachable)
    {u v : V} (hu : ∀ i ∈ indices, u ∉ P i) (hv : ∀ i ∈ indices, v ∉ P i) :
    (B.deleteEdges (indices.biUnion (fun i => B.cutFinset (P i)) : Set (Sym2 V))).Reachable u v ↔
      B.Reachable u v := by
  constructor
  · exact fun h => h.mono (SimpleGraph.deleteEdges_le _)
  intro reachable
  have kept : (B.deleteEdges (indices.image chosen : Set (Sym2 V))).Reachable u v := by
    rw [preserved]
    exact reachable
  obtain ⟨p, path⟩ := kept.exists_isPath
  let q := p.mapLe (SimpleGraph.deleteEdges_le _)
  refine ⟨q.toDeleteEdges _ (fun e member removed => ?_)⟩
  obtain ⟨i, hi, crossing⟩ := Finset.mem_biUnion.mp removed
  have edgeP : e ∈ p.edges := by simpa [q] using member
  have cutP : e ∈ (B.deleteEdges (indices.image chosen : Set (Sym2 V))).cutFinset (P i) := by
    apply (SimpleGraph.mem_cutFinset _).mpr
    exact ⟨p.edges_subset_edgeSet edgeP, (B.mem_cutFinset.mp crossing).2⟩
  exact trail_avoids_cut_of_card_le_one _
    (cut_card_le_one_after_chosen_deletion B P chosen indices two boundary hi)
    path.isTrail (hu i hi) (hv i hi) cutP edgeP

end Algebraic.Cutwidth.Bisection.RedBlack.CycleRemoval.Internal
