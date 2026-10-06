/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Defs

/-!
# Concentrators

Every edge of a `Multigraph V E` is directed from its first endpoint `fst` to its second
endpoint `snd`, and a directed walk (`Multigraph.IsDirWalk`) is a list of vertices in which each
vertex is joined to the next by an edge directed towards it.

An `(n, m)`-concentrator (Pinsker, 1973) has `n` inputs and `m` outputs, `n + m` distinct
vertices in all, such that every set `X` of at most `m` inputs is joined to some `|X|` outputs
by vertex-disjoint directed walks, one from each input of `X`. The outputs are not prescribed.
The walks are not required to be paths, and they may pass through other inputs and outputs.
Every path is a walk, so a graph that is a concentrator in the usual sense, with paths, is one
in this sense, and lower bounds for this notion apply to it.

A multigraph is *acyclic* (`Multigraph.Acyclic`) when its vertices can be numbered so that every
edge leads from a lower to a higher number: a topological order. For finite multigraphs this
holds exactly when there is no directed cycle.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph

variable {V E : Type} (G : Multigraph V E)

/-- `G` is an `(n, m)`-concentrator with inputs `input` and outputs `output`. The `n` inputs and
the `m` outputs are `n + m` distinct vertices. For every set `X` of at most `m` inputs there are
pairwise vertex-disjoint directed walks, one from each input `i` in `X` to some output
`output (target i)`. Disjointness forces distinct walks to end at distinct outputs, so the walks
join `X` to `|X|` outputs. -/
structure Concentrator {n m : ℕ} (input : Fin n → V) (output : Fin m → V) : Prop where
  /-- The inputs are distinct. -/
  input_injective : Function.Injective input
  /-- The outputs are distinct. -/
  output_injective : Function.Injective output
  /-- No input is an output. -/
  input_ne_output : ∀ i j, input i ≠ output j
  /-- Every set of at most `m` inputs is joined to some outputs by vertex-disjoint directed
  walks. -/
  exists_walks : ∀ X : Finset (Fin n), X.card ≤ m →
    ∃ (target : Fin n → Fin m) (walk : Fin n → List V),
      (∀ i ∈ X, G.IsDirWalk (walk i) (input i) (output (target i))) ∧
        ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j)

/-- `G` is acyclic: some numbering of the vertices increases strictly along every edge, from its
first endpoint to its second. -/
def Acyclic : Prop :=
  ∃ rank : V → ℕ, ∀ e, rank (G.fst e) < rank (G.snd e)

end Algebraic.Cutwidth.Multigraph
