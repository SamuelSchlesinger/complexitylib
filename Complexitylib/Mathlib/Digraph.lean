/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
public import Std.Tactic.BVDecide.Normalize.Prop

/-! # Digraph extensions for Mathlib

General-purpose definitions on top of Mathlib's `Digraph`: directed walks
and simple paths, `depth` (longest simple-path length on a finite graph),
`IsAcyclic`, the `edgeFinset` of a digraph with decidable adjacency on a
finite vertex type, and `deleteEdges`.

The `depth` measure is exported together with its general bounds, public for
downstream reuse and as upstreaming candidates: `pathLength_bddAbove`
(simple-path lengths are bounded by the vertex count), `depth_le_card`
(`depth ≤ Fintype.card V`), `one_le_depth` (a nonempty graph has positive
depth), and `depth_deleteEdges_empty` (deleting the empty edge set preserves
depth). These hold for every finite digraph, with no acyclicity assumption.

This file lives in `Complexitylib/Mathlib/` because it extends a Mathlib
type in its home (root) namespace — the one sanctioned exception to the
`Complexity` root-namespace rule. Its contents are candidates for
upstreaming to Mathlib.

Depth-reduction-specific machinery (canonical labeling, acyclicity
arguments, edge partitions by first-differing bit, etc.) lives in
`Complexitylib.Circuits.Internal.Valiant`.
-/


@[expose] public section

namespace Digraph

variable {V : Type*}

/-- `G.IsDirectedWalk p` says that `p : Fin m → V` is a directed walk
in the digraph `G`: consecutive vertices are joined by an edge. -/
def IsDirectedWalk (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  ∀ i : Fin m, ∀ h : i.val + 1 < m, G.Adj (p i) (p ⟨i.val + 1, h⟩)

/-- `G.IsPath p` says that `p : Fin m → V` is a *simple* directed
path: an injective directed walk. -/
def IsPath (G : Digraph V) {m : Nat} (p : Fin m → V) : Prop :=
  G.IsDirectedWalk p ∧ Function.Injective p

/-- The lengths of simple paths in a finite graph are bounded by its vertex
cardinality. -/
lemma pathLength_bddAbove [Fintype V] (G : Digraph V) :
    BddAbove {m | ∃ p : Fin m → V, G.IsPath p} := by
  refine ⟨Fintype.card V, ?_⟩
  rintro m ⟨p, _, hp⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hp

/-- The **depth** of a finite digraph is the maximum length — number of
vertices — of a simple directed path. Using simple paths makes `depth` a
total, honest finite measure even when the graph contains a cycle. Results
whose proofs require a DAG state `IsAcyclic` explicitly. -/
-- The instance restricts the definition's domain to finite graphs; the
-- supremum expression itself does not inspect the chosen enumeration.
@[nolint unusedArguments]
noncomputable def depth [Fintype V] (G : Digraph V) : Nat :=
  sSup {m | ∃ p : Fin m → V, G.IsPath p}

/-- A finite digraph's simple-path depth is at most its number of vertices. -/
theorem depth_le_card [Fintype V] (G : Digraph V) : G.depth ≤ Fintype.card V := by
  unfold depth
  apply csSup_le
  · exact ⟨0, fun i => i.elim0, ⟨fun i _ => i.elim0, fun i => i.elim0⟩⟩
  · rintro m ⟨p, _, hp⟩
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hp

/-- A finite nonempty digraph has a one-vertex path, hence positive depth. -/
theorem one_le_depth [Fintype V] [Nonempty V] (G : Digraph V) : 1 ≤ G.depth := by
  unfold depth
  apply le_csSup (pathLength_bddAbove G)
  let v : V := Classical.choice inferInstance
  exact ⟨fun _ => v, ⟨fun i h => by omega, fun i j _ => Subsingleton.elim i j⟩⟩

/-- The directed edge set of a digraph with decidable adjacency on a
finite vertex type. -/
def edgeFinset [Fintype V]
    (G : Digraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  Finset.univ.filter (fun p => G.Adj p.1 p.2)

lemma mem_edgeFinset [Fintype V] {G : Digraph V}
    [DecidableRel G.Adj] {e : V × V} : e ∈ G.edgeFinset ↔ G.Adj e.1 e.2 := by
  simp [edgeFinset]

/-- The digraph obtained from `G` by deleting a finite set of directed
edges `F`. -/
def deleteEdges (G : Digraph V) (F : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∧ (u, v) ∉ F

instance [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (F : Finset (V × V)) : DecidableRel (G.deleteEdges F).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ _))

/-- A digraph is **acyclic** when its set of directed-walk lengths is
bounded. For finite vertex types this is equivalent to having no
directed cycles. -/
def IsAcyclic (G : Digraph V) : Prop :=
  BddAbove { m | ∃ p : Fin m → V, G.IsDirectedWalk p }

/-- The simple-path set of `G.deleteEdges ∅` agrees with that of `G`,
so the two graphs have the same depth. -/
lemma depth_deleteEdges_empty [Fintype V] (G : Digraph V) :
    (G.deleteEdges ∅).depth = G.depth := by
  unfold Digraph.depth
  congr 1
  ext m
  refine ⟨fun ⟨p, hp, hinj⟩ => ⟨p, fun i h => (hp i h).1, hinj⟩,
    fun ⟨p, hp, hinj⟩ => ⟨p, ?_, hinj⟩⟩
  intro i h
  exact ⟨hp i h, Finset.notMem_empty _⟩

/-- The **canonical labeling** of `G`: the length — node count — of a
longest simple directed path ending at `v`. Parameterized by edge
count `n`, with the outer `+ 1` converting to node count; the
single-vertex path `![v]` always witnesses `n = 0`, so the label is
automatically at least `1`. -/
noncomputable def canonicalLabel {V : Type*}
    (G : Digraph V) (v : V) : Nat :=
  sSup { n | ∃ p : Fin (n + 1) → V, G.IsPath p ∧ p (Fin.last n) = v } + 1

end Digraph
