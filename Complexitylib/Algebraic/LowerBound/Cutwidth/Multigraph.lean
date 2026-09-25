/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite multigraphs, prefix cuts, and the graph-ordering hypothesis

A `Multigraph V E` records the two endpoints of every edge in `E`. Parallel
edges are distinct elements of `E` and are counted separately. For a vertex
ordering, the *cut after* a vertex is the set of edges with exactly one
endpoint among the vertices up to it; these are exactly the cuts of the lower
sets of the order.

`OrderingBound η C` is the graph-ordering hypothesis: every connected
loopless multigraph of maximum degree three has a vertex ordering whose
prefix cuts have at most `(1/3 + η) (M - N)⁺ + 3 log₂ N + C` edges, where `N`
and `M` are the numbers of vertices and edges. The lower bound takes this
statement as a hypothesis; it is not proved in this development.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

/-- A multigraph: every edge has a first and a second endpoint. Parallel edges
are distinct elements of `E`. -/
structure Multigraph (V E : Type) where
  /-- The first endpoint of an edge. -/
  fst : E → V
  /-- The second endpoint of an edge. -/
  snd : E → V

namespace Multigraph

variable {V E : Type} (G : Multigraph V E)

/-- An edge is incident to each of its endpoints. -/
def Incident (v : V) (e : E) : Prop :=
  G.fst e = v ∨ G.snd e = v

/-- No edge joins a vertex to itself. -/
def Loopless : Prop :=
  ∀ e, G.fst e ≠ G.snd e

/-- Two vertices are adjacent when some edge joins them, in either direction. -/
def Adj (u v : V) : Prop :=
  ∃ e, (G.fst e = u ∧ G.snd e = v) ∨ (G.fst e = v ∧ G.snd e = u)

theorem Adj.symm {G : Multigraph V E} {u v : V} (h : G.Adj u v) : G.Adj v u := by
  obtain ⟨e, h | h⟩ := h
  · exact ⟨e, Or.inr h⟩
  · exact ⟨e, Or.inl h⟩

/-- Every two vertices are joined by a walk. -/
def Connected : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- Reachability along walks is symmetric. -/
theorem reflTransGen_adj_symm {G : Multigraph V E} {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) : Relation.ReflTransGen G.Adj v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact Relation.ReflTransGen.head step.symm ih

/-- A multigraph in which every vertex reaches a common vertex is connected. -/
theorem connected_of_forall_reflTransGen {G : Multigraph V E} (root : V)
    (h : ∀ v, Relation.ReflTransGen G.Adj v root) : G.Connected :=
  fun u v => (h u).trans (reflTransGen_adj_symm (h v))

section Finite

variable [Fintype E]

/-- The edges incident to a vertex. -/
noncomputable def edgesAt (v : V) : Finset E :=
  Finset.univ.filter fun e => G.Incident v e

theorem mem_edgesAt {v : V} {e : E} : e ∈ G.edgesAt v ↔ G.Incident v e := by
  simp [edgesAt]

/-- The number of edges incident to a vertex. -/
noncomputable def degree (v : V) : Nat :=
  (G.edgesAt v).card

/-- Every vertex has at most `d` incident edges. -/
def MaxDegreeLE (d : Nat) : Prop :=
  ∀ v, G.degree v ≤ d

/-- The edges with exactly one endpoint in `L`. -/
noncomputable def cut (L : Finset V) : Finset E :=
  Finset.univ.filter fun e => ¬ (G.fst e ∈ L ↔ G.snd e ∈ L)

theorem mem_cut {L : Finset V} {e : E} :
    e ∈ G.cut L ↔ ¬ (G.fst e ∈ L ↔ G.snd e ∈ L) := by
  simp [cut]

@[simp] theorem cut_empty : G.cut ∅ = ∅ := by
  ext e
  simp [mem_cut]

@[simp] theorem cut_univ [Fintype V] : G.cut Finset.univ = ∅ := by
  ext e
  simp [mem_cut]

/-- An edge in a cut is incident to a vertex in the set and to one outside it. -/
theorem exists_mem_of_mem_cut {L : Finset V} {e : E} (h : e ∈ G.cut L) :
    (G.fst e ∈ L ∧ G.snd e ∉ L) ∨ (G.fst e ∉ L ∧ G.snd e ∈ L) := by
  rw [mem_cut] at h
  by_cases h₁ : G.fst e ∈ L <;> by_cases h₂ : G.snd e ∈ L <;> simp_all

/-- Every cut has at most `w` edges. -/
def CutsAtMost (L : Set (Finset V)) (w : Nat) : Prop :=
  ∀ S ∈ L, (G.cut S).card ≤ w

end Finite

/-- The graph-ordering hypothesis with slack `η` and additive constant `C`:
every connected loopless multigraph of maximum degree three has a linear
vertex ordering all of whose lower-set cuts have at most
`(1/3 + η) (M - N)⁺ + 3 log₂ N + C` edges. -/
def OrderingBound (η C : ℝ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
    G.Loopless → G.MaxDegreeLE 3 → G.Connected →
    ∃ _ : LinearOrder V, ∀ L : Finset V, IsLowerSet (L : Set V) →
      ((G.cut L).card : ℝ) ≤
        (1 / 3 + η) * max ((Fintype.card E : ℝ) - Fintype.card V) 0 +
          3 * Real.logb 2 (Fintype.card V) + C

end Multigraph

end Cutwidth
end Algebraic
