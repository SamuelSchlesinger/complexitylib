/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Order.Internal

/-!
# Jumping the median band of edge scores

Fix `c > 0` and a real score on the edges of a cubic graph. An edge is low when its score is
below `-c`, in the band when its score lies in `[-c, c)`, and high when its score is at least
`c`. Label the band edges by blocks so that band edges sharing a vertex share a label, for
example by the connected components of the band.

The band-jump order lists the low edges by score, then the band blocks one whole block at a
time, then the high edges by score. The blocks are taken in increasing order of the
imbalance `B_j - A_j`, where `A_j` (resp. `B_j`) counts the vertices touching block `j` with a
low (resp. high) edge. Between blocks, a bag holds the vertices with no band edge but both a
low and a high edge, the high endpoints of the finished blocks, and the low endpoints of the
blocks still to come. The vertices straddling `-c` are those of the first kind together with
all `A_j` vertices, and those straddling `c` are those of the first kind together with all
`B_j` vertices. Taking the blocks by increasing imbalance keeps every prefix sum of the
imbalances at most `max 0 (∑ (B_j - A_j))`, so every bag of the band phase has at most the
larger of the two straddling counts plus the vertices of the block in progress.

* `exists_pathDecomposition_of_bandJump`: if every threshold `t < -c` or `t ≥ c` has at most
  `B` vertices with an edge scoring at most `t` and one scoring at least `t`, and for every
  block `j` both straddling counts of `±c` plus the endpoints of block `j` are at most `B`,
  then every bag has at most `B` vertices.
* `card_filter_edgeScore_le_window`: a threshold `t ∈ [u, u')` has at most the straddling
  vertices of `u` plus twice the edges scoring in `[u, u')`.
* `card_filter_edgeScore_le_of_grid`: grid thresholds `a + i δ` with few straddling vertices
  and few edges in each window bound every `t ∈ [a, a + M δ)`.
* `card_filter_edgeScore_le_of_grids`: a low grid reaching `-c`, a high grid starting at or
  below `c`, and the two tails bound every threshold outside the band, as required by
  `exists_pathDecomposition_of_bandJump`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

open scoped Classical in
/-- A threshold `t ∈ [u, u')`: every vertex with an edge scoring at most `t` and an edge
scoring at least `t` straddles `u` or is an endpoint of an edge scoring in `[u, u')`. -/
theorem card_filter_edgeScore_le_window (score : Sym2 W → ℝ) {u t u' : ℝ} (hu : u ≤ t)
    (hu' : t < u') :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤
      ((Finset.univ.filter fun v => EdgeStraddles H score u v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e => u ≤ score e ∧ score e < u').card : ℝ) :=
  Internal.card_filter_edgeScore_le_window H score hu hu'

open scoped Classical in
/-- **Threshold grid.** If every threshold `a + i δ`, `i < M`, has its straddling vertices plus
twice the edges scoring in `[a + i δ, a + (i + 1) δ)` at most `B`, then every `t ∈ [a, a + M δ)`
has at most `B` vertices with an edge scoring at most `t` and an edge scoring at least `t`. -/
theorem card_filter_edgeScore_le_of_grid (score : Sym2 W → ℝ) {a δ : ℝ} (hδ : 0 < δ) (M : ℕ)
    {B : ℝ}
    (mid : ∀ i < M,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a + i * δ) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ).card : ℝ) ≤ B)
    {t : ℝ} (ha : a ≤ t) (ht : t < a + M * δ) :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤ B :=
  Internal.card_filter_edgeScore_le_of_grid H score hδ M mid ha ht

open scoped Classical in
/-- **Thresholds outside the band.** Take a low grid `a₁ + i δ₁`, `i ≤ M₁`, reaching `-c`
and a high grid `a₂ + i δ₂`, `i ≤ M₂`, starting at or below `c`. If twice the edges scoring
below `a₁`, twice the edges scoring at least `a₂ + M₂ δ₂`, and the grid counts of both grids
are at most `B`, then every threshold `t < -c` or `t ≥ c` has at most `B` vertices with an
edge scoring at most `t` and an edge scoring at least `t`. -/
theorem card_filter_edgeScore_le_of_grids (score : Sym2 W → ℝ) {c a₁ δ₁ a₂ δ₂ B : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (M₁ M₂ : ℕ) (hlow : -c ≤ a₁ + M₁ * δ₁) (hhigh : a₂ ≤ c)
    (low : 2 * ((H.edgeFinset.filter fun e => score e < a₁).card : ℝ) ≤ B)
    (high : 2 * ((H.edgeFinset.filter fun e => a₂ + M₂ * δ₂ ≤ score e).card : ℝ) ≤ B)
    (mid₁ : ∀ i < M₁,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a₁ + i * δ₁) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a₁ + i * δ₁ ≤ score e ∧ score e < a₁ + (i + 1) * δ₁).card : ℝ) ≤ B)
    (mid₂ : ∀ i < M₂,
      ((Finset.univ.filter fun v => EdgeStraddles H score (a₂ + i * δ₂) v).card : ℝ) +
        2 * ((H.edgeFinset.filter fun e =>
          a₂ + i * δ₂ ≤ score e ∧ score e < a₂ + (i + 1) * δ₂).card : ℝ) ≤ B)
    (t : ℝ) (ht : t < -c ∨ c ≤ t) :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤ B :=
  Internal.card_filter_edgeScore_le_of_grids H score hδ₁ hδ₂ M₁ M₂ hlow hhigh low high mid₁
    mid₂ t ht

open scoped Classical in
/-- **Band-jump path decomposition.** Let `c > 0` and label the band edges
`-c ≤ score e < c` so that band edges sharing a vertex share a label. Suppose every threshold
`t < -c` or `t ≥ c` has at most `B` vertices with an edge scoring at most `t` and an edge
scoring at least `t`, and for every label `j` the vertices straddling `-c`, as well as those
straddling `c`, together with the endpoints of the band edges labelled `j`, number at most
`B`. Then some path decomposition has every bag of at most `B` vertices. -/
theorem exists_pathDecomposition_of_bandJump (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) {c : ℝ} (hc : 0 < c) (block : Sym2 W → ℕ)
    (hblock : ∀ v, ∀ e ∈ H.incidenceFinset v, ∀ e' ∈ H.incidenceFinset v,
      -c ≤ score e → score e < c → -c ≤ score e' → score e' < c → block e = block e')
    {B : ℝ}
    (outside : ∀ t, (t < -c ∨ c ≤ t) →
      ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
        ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤ B)
    (inside : ∀ j : ℕ,
      ((Finset.univ.filter fun v => EdgeStraddles H score (-c) v).card : ℝ) +
          ((Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧
            score e < c ∧ block e = j).card : ℝ) ≤ B ∧
        ((Finset.univ.filter fun v => EdgeStraddles H score c v).card : ℝ) +
          ((Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset, v ∈ e ∧ -c ≤ score e ∧
            score e < c ∧ block e = j).card : ℝ) ≤ B) :
    ∃ D : PathDecomposition H, ∀ k, ((D.bag k).card : ℝ) ≤ B :=
  Internal.exists_pathDecomposition_of_bandJump H regular score hc block hblock outside inside

end Algebraic.Cutwidth.Gaussian
