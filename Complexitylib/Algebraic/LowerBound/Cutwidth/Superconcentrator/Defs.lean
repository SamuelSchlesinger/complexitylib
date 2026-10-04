/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph

/-!
# Superconcentrators

Every edge of a `Multigraph V E` is directed from its first endpoint `fst` to its second
endpoint `snd`. A *directed walk* is a list of vertices in which each vertex is joined to the
next by an edge directed towards it.

An `N`-superconcentrator has `N` inputs and `N` outputs, `2 N` distinct vertices in all, such
that for every `k`, every `k` inputs can be joined to every `k` outputs by vertex-disjoint
directed walks. The walks are not required to be paths. Every path is a walk, so a graph that
is a superconcentrator in the usual sense, with paths, is one in this sense, and lower bounds
for this notion apply to it.
-/

@[expose] public section

open scoped Classical

namespace Algebraic.Cutwidth.Multigraph

variable {V E : Type} (G : Multigraph V E)

/-- Some edge is directed from `u` to `v`. -/
def DirAdj (u v : V) : Prop :=
  ∃ e, G.fst e = u ∧ G.snd e = v

/-- A directed walk from `u` to `v`, given by its list of vertices: the list starts at `u`,
ends at `v`, and each vertex is joined to the next one by an edge directed towards it. -/
def IsDirWalk (p : List V) (u v : V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.DirAdj

/-- The number of edges directed into `v`. -/
noncomputable def inDegree [Fintype E] (v : V) : ℕ :=
  (Finset.univ.filter fun e => G.snd e = v).card

/-- `G` is an `N`-superconcentrator with inputs `input` and outputs `output`. The `N` inputs
and the `N` outputs are `2 N` distinct vertices. For all sets `X` of inputs and `Y` of outputs
with the same number of elements, there are pairwise vertex-disjoint directed walks, one from
each input in `X` to some output in `Y`. Disjointness forces distinct walks to end at distinct
outputs, so the walks join `X` to all of `Y`. -/
structure Superconcentrator {N : ℕ} (input output : Fin N → V) : Prop where
  /-- The inputs are distinct. -/
  input_injective : Function.Injective input
  /-- The outputs are distinct. -/
  output_injective : Function.Injective output
  /-- No input is an output. -/
  input_ne_output : ∀ i j, input i ≠ output j
  /-- Equally large sets of inputs and outputs are joined by vertex-disjoint directed walks. -/
  exists_walks : ∀ X Y : Finset (Fin N), X.card = Y.card →
    ∃ (target : Fin N → Fin N) (walk : Fin N → List V),
      (∀ i ∈ X, target i ∈ Y ∧ G.IsDirWalk (walk i) (input i) (output (target i))) ∧
        ∀ i ∈ X, ∀ j ∈ X, i ≠ j → (walk i).Disjoint (walk j)

end Algebraic.Cutwidth.Multigraph
