/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Spanning paths in connected graphs of degree at most two

A longest simple path cannot have an external neighbor at an endpoint.
At an internal vertex its two path neighbors exhaust the ambient degree.
Connectivity therefore forces the path to span the graph, including when
the graph is a cycle. This supplies an ordering for the degree-two regions
in Monien and Preis's thin-path argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal

open scoped Classical

variable {V : Type} [Fintype V] (B : SimpleGraph V)

theorem exists_spanning_path (connected : B.Connected) (degree : ∀ v, B.degree v ≤ 2) :
    ∃ (u v : V) (p : B.Walk u v), p.IsPath ∧ ∀ w, w ∈ p.support := by
  let : Nonempty V := connected.nonempty
  obtain ⟨u, v, p, path, longest⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length B
  have start {w} (adjacent : B.Adj u w) : w ∈ p.support := by
    by_contra fresh
    have := longest w v (.cons adjacent.symm p) (path.cons fresh)
    simp only [SimpleGraph.Walk.length_cons] at this
    lia
  have finish {w} (adjacent : B.Adj v w) : w ∈ p.support := by
    by_contra fresh
    have reverseFresh : w ∉ p.reverse.support := by simpa using fresh
    have := longest w u (.cons adjacent.symm p.reverse) (path.reverse.cons reverseFresh)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse] at this
    lia
  have closed {a b} (member : a ∈ p.support) (adjacent : B.Adj a b) : b ∈ p.support := by
    by_cases ha : a = u
    · exact start (ha ▸ adjacent)
    by_cases hb : a = v
    · exact finish (hb ▸ adjacent)
    obtain ⟨i, rfl, bound⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp member
    have nonzero : i ≠ 0 := by rintro rfl; exact ha p.getVert_zero
    have strict : i < p.length := by
      have : i ≠ p.length := by rintro rfl; exact hb p.getVert_length
      lia
    have same : p.toSubgraph.neighborSet (p.getVert i) = B.neighborSet (p.getVert i) :=
      Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset _) (by
        rw [B.ncard_neighborSet, path.ncard_neighborSet_toSubgraph_internal_eq_two nonzero strict]
        exact degree _)
    have : p.toSubgraph.Adj (p.getVert i) b := by
      change b ∈ p.toSubgraph.neighborSet (p.getVert i)
      rw [same]
      exact adjacent
    exact SimpleGraph.Walk.mem_support_of_adj_toSubgraph this.symm
  refine ⟨u, v, p, path, fun w => ?_⟩
  obtain ⟨q⟩ := connected.preconnected u w
  have propagate {a b} (q : B.Walk a b) : a ∈ p.support → b ∈ p.support := by
    induction q with
    | nil => exact id
    | cons adjacent _ ih => exact fun member => ih (closed member adjacent)
  exact propagate q p.start_mem_support

theorem exists_spanning_path_in_region {P : Finset V}
    (connected : (B.induce {v | v ∈ P}).Connected)
    (degree : ∀ v ∈ P, B.degree v ≤ 2) :
    ∃ (u v : V) (p : B.Walk u v), p.IsPath ∧ p.support.toFinset = P := by
  have inducedDegree (v : {v // v ∈ P}) : (B.induce {v | v ∈ P}).degree v ≤ 2 := by
    apply le_trans _ (degree v v.property)
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← B.card_neighborSet_eq_degree]
    exact Fintype.card_le_of_injective
      (fun w => (⟨w.val.val, w.property⟩ : B.neighborSet v.val))
      (fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun w : B.neighborSet v.val => w.val) h)))
  obtain ⟨u, v, p, path, spans⟩ := exists_spanning_path _ connected inducedDegree
  let hom : (B.induce {v | v ∈ P}) →g B := ⟨Subtype.val, fun h => h⟩
  refine ⟨u, v, p.map hom, path.map Subtype.val_injective, ?_⟩
  ext w
  simp only [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨a, _, rfl⟩
    exact a.property
  · intro hw
    exact ⟨⟨w, hw⟩, spans _, rfl⟩

end Algebraic.Cutwidth.Bisection.RedBlack.PathSystem.Internal
