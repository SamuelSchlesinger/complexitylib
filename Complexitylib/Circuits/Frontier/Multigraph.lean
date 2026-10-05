/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Multigraphs, layouts, and the layout hypothesis

A `Multigraph V E` gives every edge two endpoints. Parallel edges are distinct elements of `E`;
the orientation of an edge plays no role. A *layout* numbers the vertices `v₀, v₁, ...`, and its
*frontier* at time `t` is the cut between the first `t` vertices and the rest. The *width* of a
layout is the size of its largest frontier; the cutwidth of a graph is the least width of a
layout.

For a connected graph, the *cycle rank* `β₁ = |E| - |V| + 1` counts its independent cycles.
Trees have cycle rank zero and, in bounded degree, logarithmic cutwidth. The circuit lower
bound needs one fact from graph theory: that graphs of maximum degree `d` have layouts whose
width is at most a fixed multiple `A` of their cycle rank, up to lower-order terms.

`LayoutBound d A` states this as a hypothesis, so that any layout theorem can be plugged in. For
subcubic graphs (`d = 3`, the case of circuits of fan-in two) it is proved in `Frontier.Layouts`
with `A = (3/π) arccos((1 + 2√2)/4) ≈ 0.2807`, from Gaussian edge-score layouts, and hence with
`A = 1/3`. The circuit lower bounds take `LayoutBound (r + 1) A` as an assumption and prove the
coefficient `(1 + 1/A) / (r - 1)` for circuits of fan-in `r`.

## Main definitions

* `Frontier.Multigraph`: a multigraph, with `Incident`, `edgesAt`, `MaxDegreeLE`, `Loopless`,
  `Adj`, `Connected`, `cut`, and `cycleRank`.
* `Frontier.Layout V`: a numbering of the vertices, with `Layout.initial`.
* `Frontier.LayoutBound d A`: the layout hypothesis for maximum degree `d` with coefficient `A`.

## Main results

* `Frontier.Multigraph.Connected.card_vertex_le`: a connected graph has at least `|V| - 1`
  edges, so its cycle rank `|E| + 1 - |V|` involves no truncation.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

/-- A multigraph: every edge has two endpoints, its *source* and its *target*. Parallel edges
are distinct elements of `E`. The orientation plays no role in what follows. -/
structure Multigraph (V E : Type*) where
  /-- One endpoint of an edge. -/
  src : E → V
  /-- The other endpoint of an edge. -/
  tgt : E → V

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- An edge is incident to each of its endpoints. -/
def Incident (v : V) (e : E) : Prop :=
  G.src e = v ∨ G.tgt e = v

/-- The edges incident to a vertex. -/
def edgesAt (v : V) : Set E :=
  {e | G.Incident v e}

/-- Every vertex has at most `d` incident edges. -/
def MaxDegreeLE (d : ℕ) : Prop :=
  ∀ v, (G.edgesAt v).ncard ≤ d

/-- No edge joins a vertex to itself. -/
def Loopless : Prop :=
  ∀ e, G.src e ≠ G.tgt e

/-- Two vertices are adjacent when an edge joins them. -/
def Adj (u v : V) : Prop :=
  ∃ e, (G.src e = u ∧ G.tgt e = v) ∨ (G.src e = v ∧ G.tgt e = u)

/-- Every two vertices are joined by a walk. -/
def Connected : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- The *cut* of a set of vertices `L`: the edges with exactly one endpoint in `L`. -/
def cut (L : Set V) : Set E :=
  {e | ¬(G.src e ∈ L ↔ G.tgt e ∈ L)}

/-- The edges with an endpoint in `L`. -/
def touching (L : Set V) : Set E :=
  {e | G.src e ∈ L ∨ G.tgt e ∈ L}

/-- The connected cycle-rank expression `max (|E| - |V| + 1) 0`. For a nonempty connected
graph, this is the number of independent cycles. On disconnected graphs it is not the sum
of the component cycle ranks. -/
noncomputable def cycleRank (_G : Multigraph V E) : ℕ :=
  Nat.card E + 1 - Nat.card V

theorem mem_cut {L : Set V} {e : E} : e ∈ G.cut L ↔ ¬(G.src e ∈ L ↔ G.tgt e ∈ L) :=
  Iff.rfl

@[simp] theorem cut_empty : G.cut ∅ = ∅ := by
  ext e; simp [mem_cut]

@[simp] theorem cut_univ : G.cut univ = ∅ := by
  ext e; simp [mem_cut]

/-- Adding one vertex changes a cut only at the edges incident to it. -/
theorem cut_insert_subset (v : V) (L : Set V) : G.cut (insert v L) ⊆ G.cut L ∪ G.edgesAt v := by
  intro e he
  by_cases hv : G.src e = v ∨ G.tgt e = v
  · exact Or.inr hv
  · rw [not_or] at hv
    left
    simpa [mem_cut, hv.1, hv.2] using he

/-- Adjacency is symmetric. -/
theorem Adj.symm {G : Multigraph V E} {u v : V} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨e, h | h⟩ := h
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Walks can be reversed. -/
theorem reflTransGen_adj_symm {G : Multigraph V E} {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) : Relation.ReflTransGen G.Adj v u := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact .head hab.symm ih

/-- **A connected graph has at least `|V| - 1` edges**: its cycle rank `|E| + 1 - |V|` involves
no truncation. -/
theorem Connected.card_vertex_le {G : Multigraph V E} [Finite E] (h : G.Connected) :
    Nat.card V ≤ Nat.card E + 1 := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  -- The simple graph with the same adjacency is connected and has no more edges.
  let H := SimpleGraph.fromRel G.Adj
  have hconn : H.Connected := by
    refine ⟨fun u v => ?_⟩
    induction h u v with
    | refl => rfl
    | @tail b c _ hbc ih =>
      by_cases hb : b = c
      · exact hb ▸ ih
      · exact ih.trans ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hb, Or.inl hbc⟩).reachable
  have hedges : Nat.card H.edgeSet ≤ Nat.card E := by
    let f : {e : E // G.src e ≠ G.tgt e} → H.edgeSet := fun e =>
      ⟨s(G.src e, G.tgt e), (SimpleGraph.fromRel_adj _ _ _).mpr
        ⟨e.2, Or.inl ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      induction z using Sym2.ind with
      | h u v =>
        obtain ⟨huv, ⟨e, he⟩ | ⟨e, he⟩⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hz <;>
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨⟨e, huv⟩, rfl⟩
        · exact ⟨⟨e, huv.symm⟩, Subtype.ext Sym2.eq_swap⟩
        · exact ⟨⟨e, huv.symm⟩, Subtype.ext Sym2.eq_swap⟩
        · exact ⟨⟨e, huv⟩, rfl⟩
    exact (Nat.card_le_card_of_surjective f hf).trans (Finite.card_subtype_le _)
  have := hconn.card_vert_le_card_edgeSet_add_one
  omega

/-- A graph in which every vertex reaches one fixed vertex is connected. -/
theorem connected_of_forall_reflTransGen {G : Multigraph V E} (root : V)
    (h : ∀ v, Relation.ReflTransGen G.Adj v root) : G.Connected := fun u v =>
  (h u).trans (reflTransGen_adj_symm (h v))

end Multigraph

/-- A *layout* of a finite set of vertices: a numbering `v₀, v₁, ..., v_{N-1}`. -/
abbrev Layout (V : Type*) :=
  V ≃ Fin (Nat.card V)

namespace Layout

variable {V : Type*} (π : Layout V)

/-- The first `t` vertices of a layout. -/
def initial (t : ℕ) : Set V :=
  {v | (π v : ℕ) < t}

theorem mem_initial {t : ℕ} {v : V} : v ∈ π.initial t ↔ (π v : ℕ) < t :=
  Iff.rfl

@[simp] theorem initial_zero : π.initial 0 = ∅ := by
  ext v; simp [mem_initial]

theorem initial_of_card_le {t : ℕ} (ht : Nat.card V ≤ t) : π.initial t = univ := by
  ext v; simpa [mem_initial] using (π v).isLt.trans_le ht

/-- The first `t + 1` vertices are the first `t` and the vertex numbered `t`. -/
theorem initial_succ {t : ℕ} (ht : t < Nat.card V) :
    π.initial (t + 1) = insert (π.symm ⟨t, ht⟩) (π.initial t) := by
  ext v
  simp only [mem_initial, mem_insert_iff, Equiv.eq_symm_apply, Fin.ext_iff]
  omega

end Layout

/-- **The layout hypothesis** for maximum degree `d`, with coefficient `A`. For every `η > 0`
there is a constant `C` such that every connected, loopless multigraph of maximum degree `d`
has a layout all of whose frontiers have at most `(A + η) β₁ + η |V| + C` edges, where `β₁` is
the cycle rank.

Only the coefficient `A` matters for the circuit lower bound: any error term that is
sublinear in the number of vertices may be absorbed into `η |V| + C`. -/
def LayoutBound (d : ℕ) (A : ℝ) : Prop :=
  ∀ η > 0, ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.Connected → G.Loopless → G.MaxDegreeLE d →
      ∃ π : Layout V, ∀ t,
        ((G.cut (π.initial t)).ncard : ℝ) ≤ (A + η) * G.cycleRank + η * Nat.card V + C

end Complexity.Frontier
