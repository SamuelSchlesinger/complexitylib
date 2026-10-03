/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.RedBlack.PathSystem.Internal
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Root deletion and connected remainder unions

Every component left after deleting a root from a connected set contains
a neighbor of that root. Distinct components give distinct neighbors, so
their number is bounded by the root's degree. Small connected sets rooted
at those neighbors join to a connected set after the root is restored.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition.Internal

open scoped Classical
open PathSystem PathSystem.Internal

variable {V : Type} [Fintype V] (B : SimpleGraph V)

omit [Fintype V] in
theorem exists_root_neighbor {S : Finset V} {root : V} (member : root ∈ S)
    (connected : (B.induce {v | v ∈ S}).Connected)
    (C : (B.induce {v | v ∈ S.erase root}).ConnectedComponent) :
    ∃ v ∈ region B (S.erase root) C, B.Adj root v := by
  by_contra! none
  have closed {v w : V} (hv : v ∈ region B (S.erase root) C) (hw : w ∈ S)
      (adjacent : B.Adj v w) : w ∈ region B (S.erase root) C := by
    have different : w ≠ root := by
      intro equal
      subst w
      exact none v hv adjacent.symm
    obtain ⟨hvU, hvC⟩ := (mem_region B (S.erase root) C).mp hv
    have hwU : w ∈ S.erase root := Finset.mem_erase.mpr ⟨different, hw⟩
    exact (mem_region B (S.erase root) C).mpr ⟨hwU,
      C.mem_supp_of_adj_mem_supp hvC adjacent⟩
  let start := C.out
  have initial : start.val ∈ region B (S.erase root) C :=
    (mem_region B (S.erase root) C).mpr
      ⟨start.property, (C.mem_supp_iff _).mpr C.out_eq⟩
  have propagation (v w : {v // v ∈ S})
      (reach : (B.induce {v | v ∈ S}).Reachable v w)
      (initial : v.val ∈ region B (S.erase root) C) :
      w.val ∈ region B (S.erase root) C := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at reach
    induction reach with
    | refl => exact initial
    | @tail b c _ adjacent ih => exact closed ih c.property adjacent
  have reach := connected.preconnected
    ⟨start.val, Finset.mem_of_mem_erase start.property⟩ ⟨root, member⟩
  have rootRegion := propagation _ _ reach initial
  exact (Finset.mem_erase.mp (region_subset B (S.erase root) C rootRegion)).1 rfl

theorem card_components_erase_le_degree {S : Finset V} {root : V} (member : root ∈ S)
    (connected : (B.induce {v | v ∈ S}).Connected) :
    Nat.card (B.induce {v | v ∈ S.erase root}).ConnectedComponent ≤ B.degree root := by
  let : Fintype (B.induce {v | v ∈ S.erase root}).ConnectedComponent := Fintype.ofFinite _
  choose neighbor inside adjacent using exists_root_neighbor B member connected
  let f (C : (B.induce {v | v ∈ S.erase root}).ConnectedComponent) : B.neighborSet root :=
    ⟨neighbor C, adjacent C⟩
  have injective : Function.Injective f := by
    intro C D equal
    by_contra different
    have same : neighbor C = neighbor D := congrArg Subtype.val equal
    exact Finset.disjoint_left.mp (region_disjoint B (S.erase root) different)
      (inside C) (by rw [same]; exact inside D)
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f injective

omit [Fintype V] in
theorem connected_insert_biUnion {ι : Type} (root : V) (A : ι → Finset V)
    (neighbor : ι → V) (adjacent : ∀ i, B.Adj root (neighbor i))
    (rooted : ∀ i, A i = ∅ ∨ neighbor i ∈ A i ∧ (B.induce {v | v ∈ A i}).Connected)
    (indices : Finset ι) : (B.induce {v | v ∈ insert root (indices.biUnion A)}).Connected := by
  induction indices using Finset.induction_on with
  | empty =>
    have same : {v | v ∈ insert root ((∅ : Finset ι).biUnion A)} = {root} := by
      ext v
      simp
    rw [same]
    exact (SimpleGraph.IsTree.of_subsingleton (G := B.induce ({root} : Set V))).connected
  | @insert i indices fresh ih =>
    rcases rooted i with empty | ⟨member, connected⟩
    · have same : insert root ((insert i indices).biUnion A) =
          insert root (indices.biUnion A) := by
        ext v
        simp only [Finset.mem_insert, Finset.mem_biUnion]
        aesop
      rw [same]
      exact ih
    · have joined := SimpleGraph.connected_induce_union ih.preconnected connected.preconnected
        (show root ∈ {v | v ∈ insert root (indices.biUnion A)} from Finset.mem_insert_self _ _)
        member (adjacent i)
      have same : {v | v ∈ insert root ((insert i indices).biUnion A)} =
          {v | v ∈ insert root (indices.biUnion A)} ∪ {v | v ∈ A i} := by
        ext v
        simp only [Finset.mem_insert, Finset.mem_biUnion, Set.mem_union, Set.mem_ofPred_eq]
        aesop
      rw [same]
      exact joined

end Algebraic.Cutwidth.Bisection.RedBlack.ConnectedPartition.Internal
