/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Path decompositions and the cubic pathwidth bound

A path decomposition of a simple graph is a sequence of bags covering every
vertex and every edge, in which the bags containing a fixed vertex are
consecutive. Its width is one less than the largest bag.

`PathwidthBound p ξ N₀` states a pathwidth bound with coefficient `p` for
cubic graphs: every simple 3-regular graph on more than `N₀` vertices has a
path decomposition of width at most `(p + ξ) h`, where `h` is the number of
vertices. Together with the compression and median-ordering arguments it
yields the graph-ordering hypothesis `Multigraph.OrderingBound (2 p)`.
`PathDecomposition.Bisection` proves the bound with `p = 1/6` from a cubic
bisection bound, and `Bisection.Helpful` supplies the sharp bound for every
positive slack.

The cut of a vertex set in a simple graph, `SimpleGraph.cutFinset`, is the set
of edges with exactly one endpoint in the set. `CutwidthBound c ξ N₀` states a
cutwidth bound with coefficient `c` for cubic graphs: every simple 3-regular
graph on more than `N₀` vertices has a vertex ordering all of whose prefix
cuts have at most `(c + ξ) h` edges. It yields `Multigraph.OrderingBound (2 c)`
directly, without a path decomposition.
-/

@[expose] public section

namespace Algebraic
namespace Cutwidth

open scoped Classical

variable {W : Type} (H : SimpleGraph W)

/-- A path decomposition: bags indexed by `Fin length`, covering every vertex
and every edge, with the bags containing any vertex forming an interval. -/
structure PathDecomposition where
  /-- The number of bags. -/
  length : Nat
  /-- The bags. -/
  bag : Fin length → Finset W
  /-- Every vertex lies in some bag. -/
  vertex_mem : ∀ w, ∃ i, w ∈ bag i
  /-- Both endpoints of every edge lie in a common bag. -/
  edge_mem : ∀ u v, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  /-- The bags containing a vertex are consecutive. -/
  consecutive : ∀ w (i j k : Fin length), i ≤ j → j ≤ k → w ∈ bag i → w ∈ bag k → w ∈ bag j

/-- The one-bag decomposition of a finite graph. -/
def PathDecomposition.trivial [Fintype W] : PathDecomposition H where
  length := 1
  bag := fun _ => Finset.univ
  vertex_mem := fun _ => ⟨0, Finset.mem_univ _⟩
  edge_mem := fun _ _ _ => ⟨0, Finset.mem_univ _, Finset.mem_univ _⟩
  consecutive := fun _ _ _ _ _ _ _ _ => Finset.mem_univ _

/-- The pathwidth bound for cubic graphs with coefficient `p`, slack `ξ`, and
threshold `N₀`: every simple 3-regular graph on `h > N₀` vertices has a path
decomposition all of whose bags have at most `(p + ξ) h + 1` vertices. The
Fomin–Høie bound has `p = 1/6`. -/
def PathwidthBound (p ξ : ℝ) (N₀ : Nat) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
    ∃ D : PathDecomposition H, ∀ i, ((D.bag i).card : ℝ) ≤ (p + ξ) * Fintype.card W + 1

section Cut

variable [Fintype W]

/-- The edges of a simple graph with exactly one endpoint in `S`. -/
noncomputable def _root_.SimpleGraph.cutFinset (S : Finset W) : Finset (Sym2 W) :=
  H.edgeFinset.filter fun e => ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S

theorem _root_.SimpleGraph.mem_cutFinset {S : Finset W} {e : Sym2 W} :
    e ∈ H.cutFinset S ↔ e ∈ H.edgeSet ∧ ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S := by
  simp [SimpleGraph.cutFinset, SimpleGraph.mem_edgeFinset]

/-- An edge crossing a set is adjacent-pair witnessed with the inside endpoint first. -/
theorem _root_.SimpleGraph.mem_cutFinset_mk {S : Finset W} {a b : W} :
    s(a, b) ∈ H.cutFinset S ↔ H.Adj a b ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)) := by
  rw [SimpleGraph.mem_cutFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨adj, x, y, hxy, hx, hy⟩
    refine ⟨adj, ?_⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro ⟨adj, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
    · exact ⟨adj, a, b, rfl, ha, hb⟩
    · exact ⟨adj, b, a, Sym2.eq_swap, hb, ha⟩

/-- A graph with at most one vertex has no crossing edges. -/
theorem _root_.SimpleGraph.cutFinset_eq_empty_of_subsingleton [Subsingleton W] (S : Finset W) :
    H.cutFinset S = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨_, a, b, _, ha, hb⟩ := (H.mem_cutFinset).mp he
  exact hb (Subsingleton.elim a b ▸ ha)

end Cut

/-- The cutwidth bound for cubic graphs with coefficient `c`, slack `ξ`, and
threshold `N₀`: every simple 3-regular graph on `h > N₀` vertices has an
injective vertex key all of whose prefixes `{w | key w < t}` are crossed by at
most `(c + ξ) h` edges. -/
def CutwidthBound (c ξ : ℝ) (N₀ : Nat) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
    ∃ key : W → Nat, Function.Injective key ∧
      ∀ t : Nat, ((H.cutFinset (Finset.univ.filter fun w => key w < t)).card : ℝ) ≤
        (c + ξ) * Fintype.card W

end Cutwidth
end Algebraic
