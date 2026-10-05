/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Multigraph

/-!
# Boundaries of hypergraphs

A signal may have many consumers, but a separator pays for its value only once. Its native
incidence object is therefore a hyperedge. Hypergraph cut cardinality is symmetric and
submodular, so it is a connectivity function even when the hyperedges have unbounded size.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {V E Λ : Type*}

/-- A hypergraph, with named hyperedges and no restriction on their size. -/
abbrev Hypergraph (V Λ : Type*) := Λ → Set V

namespace Hypergraph

/-- Hyperedges meeting both sides of a vertex separator. -/
def cut (H : Hypergraph V Λ) (X : Set V) : Set Λ :=
  {e | (H e ∩ X).Nonempty ∧ (H e \ X).Nonempty}

@[simp] theorem cut_compl (H : Hypergraph V Λ) (X : Set V) : H.cut Xᶜ = H.cut X := by
  ext e
  simp only [cut, mem_ofPred_eq, sdiff_eq, compl_compl]
  exact and_comm

@[simp] theorem cut_empty (H : Hypergraph V Λ) : H.cut ∅ = ∅ := by
  ext e
  simp [cut]

@[simp] theorem cut_univ (H : Hypergraph V Λ) : H.cut univ = ∅ := by
  rw [← compl_empty, cut_compl, cut_empty]

theorem cut_union_inter_subset (H : Hypergraph V Λ) (X Y : Set V) :
    H.cut (X ∩ Y) ∪ H.cut (X ∪ Y) ⊆ H.cut X ∪ H.cut Y := by
  rintro e (⟨⟨u, hu, huX, huY⟩, v, hv, hvXY⟩ | ⟨⟨u, hu, huXY⟩, v, hv, hvXY⟩)
  · by_cases hvX : v ∈ X
    · exact Or.inr ⟨⟨u, hu, huY⟩, v, hv, fun hvY => hvXY ⟨hvX, hvY⟩⟩
    · exact Or.inl ⟨⟨u, hu, huX⟩, v, hv, hvX⟩
  · rcases huXY with huX | huY
    · exact Or.inl ⟨⟨u, hu, huX⟩, v, hv, fun hvX => hvXY (Or.inl hvX)⟩
    · exact Or.inr ⟨⟨u, hu, huY⟩, v, hv, fun hvY => hvXY (Or.inr hvY)⟩

theorem cut_inter_union_subset (H : Hypergraph V Λ) (X Y : Set V) :
    H.cut (X ∩ Y) ∩ H.cut (X ∪ Y) ⊆ H.cut X ∩ H.cut Y := by
  rintro e ⟨⟨⟨u, hu, huX, huY⟩, _⟩, ⟨_, v, hv, hvXY⟩⟩
  exact ⟨⟨⟨u, hu, huX⟩, v, hv, fun hvX => hvXY (Or.inl hvX)⟩,
    ⟨⟨u, hu, huY⟩, v, hv, fun hvY => hvXY (Or.inr hvY)⟩⟩

/-- Hypergraph boundary size is submodular. -/
theorem ncard_cut_submodular [Finite Λ] (H : Hypergraph V Λ) (X Y : Set V) :
    (H.cut (X ∩ Y)).ncard + (H.cut (X ∪ Y)).ncard ≤
      (H.cut X).ncard + (H.cut Y).ncard := by
  rw [← ncard_union_add_ncard_inter (H.cut (X ∩ Y)) (H.cut (X ∪ Y)),
    ← ncard_union_add_ncard_inter (H.cut X) (H.cut Y)]
  exact Nat.add_le_add (ncard_le_ncard (H.cut_union_inter_subset X Y))
    (ncard_le_ncard (H.cut_inter_union_subset X Y))

end Hypergraph

namespace Multigraph

/-- Contract the endpoints carrying the same signal into a native hyperedge. -/
def signalHypergraph (G : Multigraph V E) (label : E → Λ) : Hypergraph V Λ :=
  fun s => {v | ∃ e, label e = s ∧ G.Incident v e}

/-- Every crossing labelled edge gives a crossing signal hyperedge. The converse requires
the occurrences of a label to be connected; it is false for arbitrary labellings. -/
theorem image_cut_subset_hypergraph_cut (G : Multigraph V E) (label : E → Λ) (X : Set V) :
    label '' G.cut X ⊆ (G.signalHypergraph label).cut X := by
  rintro _ ⟨e, he, rfl⟩
  change ¬(G.src e ∈ X ↔ G.tgt e ∈ X) at he
  by_cases hs : G.src e ∈ X
  · exact ⟨⟨_, ⟨e, rfl, Or.inl rfl⟩, hs⟩,
      _, ⟨e, rfl, Or.inr rfl⟩, fun ht => he ⟨fun _ => ht, fun _ => hs⟩⟩
  · have ht : G.tgt e ∈ X := by tauto
    exact ⟨⟨_, ⟨e, rfl, Or.inr rfl⟩, ht⟩, _, ⟨e, rfl, Or.inl rfl⟩, hs⟩

/-- The graph consisting of the edges with one chosen label. -/
def labelGraph (G : Multigraph V E) (label : E → Λ) (s : Λ) :
    Multigraph V {e // label e = s} where
  src e := G.src e.1
  tgt e := G.tgt e.1

/-- A connected occurrence graph makes the native hypergraph boundary exact. -/
theorem image_cut_eq_hypergraph_cut (G : Multigraph V E) (label : E → Λ)
    (hconn : ∀ s, ∀ u ∈ G.signalHypergraph label s, ∀ v ∈ G.signalHypergraph label s,
      Relation.ReflTransGen (G.labelGraph label s).Adj u v) (X : Set V) :
    label '' G.cut X = (G.signalHypergraph label).cut X := by
  apply subset_antisymm (G.image_cut_subset_hypergraph_cut label X)
  rintro s ⟨⟨u, hu, huX⟩, v, hv, hvX⟩
  by_contra! hs
  have hsame : ∀ e, label e = s → (G.src e ∈ X ↔ G.tgt e ∈ X) := by
    intro e he
    by_contra h
    exact hs ⟨e, h, he⟩
  have hwalk : ∀ {a b}, Relation.ReflTransGen (G.labelGraph label s).Adj a b →
      (a ∈ X ↔ b ∈ X) := by
    intro a b h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
      obtain ⟨e, he | he⟩ := hbc
      · change G.src e.1 = b ∧ G.tgt e.1 = c at he
        exact ih.trans (by rw [← he.1, ← he.2]; exact hsame e.1 e.2)
      · change G.src e.1 = c ∧ G.tgt e.1 = b at he
        exact ih.trans (by rw [← he.1, ← he.2]; exact (hsame e.1 e.2).symm)
  exact hvX ((hwalk (hconn s u hu v hv)).mp huX)

end Multigraph

end Complexity.Frontier
