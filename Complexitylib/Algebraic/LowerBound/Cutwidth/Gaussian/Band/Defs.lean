/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Vector
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Band clusters of Gaussian edge scores

The Gaussian edge-score field gives the edge `uv` of a graph the score
`Internal.edgeScore H q R ω s(u, v) = ⟨(x_u + x_v)/‖x_u + x_v‖, ω⟩`, where `x` are the unit
truncated distance-kernel rows (`unitKernel`) with decay rate `q` and radius `R`, and `ω` is a
standard Gaussian vector indexed by the vertices.

The band graph `bandGraph H score c` keeps the edges of `H` whose score lies in the median band
`[-c, c)`. `bigBandEvent H q R c K v` is the event that the band cluster of `v`, the set of
vertices reachable from `v` in the band graph of the Gaussian edge scores, has more than `K`
vertices.

`BandSubcritical q R c` is a percolation hypothesis: the band clusters are subcritical uniformly
over simple cubic graphs. For every `ε > 0` some cluster size `K` makes the expected number of
vertices in band clusters of more than `K` vertices at most `ε h` on every simple cubic graph
with `h` vertices. It is an open hypothesis, not a theorem of this library. Numerically it holds
on the infinite cubic tree for `c < 0.1826`, which appears to be the worst case; the band-jump
path decompositions (`Gaussian.Band`) and the circuit bounds derived from them take it as an
explicit premise.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

open MeasureTheory

variable {W : Type} (H : SimpleGraph W)

/-- The band graph of an edge score: the edges of `H` whose score lies in `[-c, c)`. -/
def bandGraph (score : Sym2 W → ℝ) (c : ℝ) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ -c ≤ score s(u, v) ∧ score s(u, v) < c
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun u h => H.ne_of_adj h.1 rfl⟩

variable [Fintype W]

open scoped Classical in
/-- The event that the band cluster of `v` has more than `K` vertices: more than `K` vertices
are reachable from `v` along edges whose Gaussian edge score lies in `[-c, c)`. -/
def bigBandEvent (q : ℝ) (R : ℕ) (c : ℝ) (K : ℕ) (v : W) : Set (W → ℝ) :=
  {ω | K < (Finset.univ.filter fun u =>
    (bandGraph H (Internal.edgeScore H q R ω) c).Reachable v u).card}

/-- **Subcritical band clusters** (an open percolation hypothesis). For every `ε > 0` there is
a cluster size `K` such that on every simple cubic graph with `h` vertices, the expected number
of vertices whose band cluster has more than `K` vertices is at most `ε h`. The band cluster of
`v` is its connected component in the graph of the edges whose Gaussian edge score, for the
kernel with decay rate `q` and radius `R`, lies in `[-c, c)`.

This is not proved in this library. It says that band percolation of the Gaussian edge-score
field is subcritical uniformly over cubic graphs. Numerically it holds on the infinite cubic
tree for `c < 0.1826`, which appears to be the worst case. -/
def BandSubcritical (q : ℝ) (R : ℕ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj], H.IsRegularOfDegree 3 →
      ∑ v, (gaussPi W).real (bigBandEvent H q R c K v) ≤ ε * Fintype.card W

end Algebraic.Cutwidth.Gaussian
