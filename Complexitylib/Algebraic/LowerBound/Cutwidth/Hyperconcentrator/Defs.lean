/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Superconcentrator.Defs

/-!
# Hyperconcentrators

Every edge of a `Multigraph V E` is directed from its first endpoint `fst` to its second
endpoint `snd`, and a directed walk (`Multigraph.IsDirWalk`) is a list of vertices in which each
vertex is joined to the next by an edge directed towards it.

An `N`-hyperconcentrator has `N` inputs and `N` outputs `y₀, …, y_{N-1}`, `2 N` distinct
vertices in all, such that for every `k`, every set of `k` inputs is joined to the first `k`
outputs `y₀, …, y_{k-1}` by vertex-disjoint directed walks. The walks are not required to be
paths, and they may pass through other inputs and outputs. Every path is a walk, so a graph that
is a hyperconcentrator in the usual sense, with paths, is one in this sense, and lower bounds
for this notion apply to it. Every superconcentrator is a hyperconcentrator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Multigraph

variable {V E : Type} (G : Multigraph V E)

/-- `G` is an `N`-hyperconcentrator with inputs `input` and outputs `output`. The `N` inputs
and the `N` outputs are `2 N` distinct vertices. For every set `X` of inputs there are pairwise
vertex-disjoint directed walks, one from each input `i` in `X` to an output `output (target i)`
among the first `|X|` outputs. Disjointness forces distinct walks to end at distinct outputs,
so the walks join `X` to all of the first `|X|` outputs. -/
structure Hyperconcentrator {N : ℕ} (input output : Fin N → V) : Prop where
  /-- The inputs are distinct. -/
  input_injective : Function.Injective input
  /-- The outputs are distinct. -/
  output_injective : Function.Injective output
  /-- No input is an output. -/
  input_ne_output : ∀ i j, input i ≠ output j
  /-- Every set of inputs is joined to the first equally many outputs by vertex-disjoint
  directed walks. -/
  exists_walks : ∀ X : Finset (Fin N),
    ∃ (target : Fin N → Fin N) (walk : Fin N → List V),
      (∀ i ∈ X, (target i : ℕ) < X.card ∧
        G.IsDirWalk (walk i) (input i) (output (target i))) ∧
        ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j)

end Algebraic.Cutwidth.Multigraph
