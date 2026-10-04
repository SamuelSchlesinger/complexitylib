/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Internal

/-!
# Path decompositions of cubic graphs from edge scores

A real score on the edges of a cubic graph lists the edges in nondecreasing order. Bag `k`
of the resulting path decomposition holds the vertices with an incident edge at a position
at most `k` and another at a position at least `k`.

* `indicator_edgeStraddles_le`: a vertex straddling a threshold has at least four ordered
  pairs of distinct incident edges separated by the threshold, so the indicator of
  straddling is at most a quarter of the number of separated pairs.
* `exists_pathDecomposition_subset_edgeScore`: bag `k` lies inside the vertices with an edge
  scoring at most `t` and an edge scoring at least `t`, where `t` is the score of the `k`-th
  edge.
* `exists_pathDecomposition_of_edgeScore`: fix thresholds `a + i δ` for `i ≤ M`. If twice
  the number of edges in each tail is at most `B`, and for each `i < M` the straddling
  vertices of `a + i δ` plus twice the number of edges scoring in `[a + i δ, a + (i + 1) δ)`
  number at most `B`, then every bag has at most `B` vertices.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

open scoped Classical in
/-- In a cubic graph, a straddling vertex has at least four ordered pairs of incident edges
separated by the threshold. -/
theorem indicator_edgeStraddles_le (regular : H.IsRegularOfDegree 3) (score : Sym2 W → ℝ)
    (t : ℝ) (v : W) :
    (if EdgeStraddles H score t v then (1 : ℝ) else 0) ≤
      1 / 4 * ∑ e ∈ H.incidenceFinset v, ∑ e' ∈ (H.incidenceFinset v).erase e,
        if Between t (score e) (score e') then (1 : ℝ) else 0 :=
  Internal.indicator_edgeStraddles_le H regular score t v

open scoped Classical in
/-- **Score-order path decomposition.** List the edges of a cubic graph in nondecreasing score
order and let bag `k` hold the vertices with an incident edge at a position at most `k` and
another at a position at least `k`. Each bag lies inside the vertices with an edge scoring at
most `t` and an edge scoring at least `t`, where `t` is the score of the `k`-th edge. -/
theorem exists_pathDecomposition_subset_edgeScore (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) :
    ∃ D : PathDecomposition H, ∀ k, ∃ t : ℝ, D.bag k ⊆ Finset.univ.filter fun v =>
      (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧ ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e :=
  Internal.exists_pathDecomposition_subset_edgeScore H regular score

open scoped Classical in
/-- **Edge-score path decomposition.** List the edges of a cubic graph by score. With
thresholds `a + i δ`, `i ≤ M`, if both tails contain few edges and every threshold has few
straddling vertices and few edges in the following window, every bag has at most `B`
vertices. -/
theorem exists_pathDecomposition_of_edgeScore (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ) {B : ℝ}
    (low : 2 * ((H.edgeFinset.filter fun e => score e < a).card : ℝ) ≤ B)
    (high : 2 * ((H.edgeFinset.filter fun e => a + M * δ ≤ score e).card : ℝ) ≤ B)
    (mid : ∀ i < M,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a + i * δ) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ).card : ℝ) ≤ B) :
    ∃ D : PathDecomposition H, ∀ k, ((D.bag k).card : ℝ) ≤ B :=
  Internal.exists_pathDecomposition_of_edgeScore H regular score hδ M low high mid

end Algebraic.Cutwidth.Gaussian
