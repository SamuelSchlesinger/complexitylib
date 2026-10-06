/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Layouts.Compression
public import Complexitylib.Circuits.Frontier.Layouts.Gaussian
public import Complexitylib.Circuits.Frontier.Layouts.General
public import Complexitylib.Circuits.Frontier.Layouts.Quartic
public import Complexitylib.Circuits.Frontier.Layouts.BoundedDegree

/-!
# Layout bounds

The graph-theoretic input of the lower bound, proved:

* `layoutBound_gaussian`: `LayoutBound 3 (2p)` with `p = (3/(2π)) arccos ((1 + 2√2)/4)`, so
  `2p ≈ 0.2807`. Gaussian edge scores lay out every large cubic graph on `h` vertices with
  prefix cuts at most `(p + o(1)) h` (`Frontier.Gaussian.cubicLayoutBound_gaussian`), and
  compressing a subcubic multigraph to its cubic core turns this into a layout bound with
  coefficient `2p` (`Frontier.LayoutBound.of_cubic`).
* `layoutBound_one_third`: `LayoutBound 3 (1/3)`, since `2p ≤ 9/32 < 1/3`.
* `layoutBound_one d`: coefficient one in every fixed degree, from a spanning tree of width
  at most `d log₂ |V|` and one additional edge per independent cycle.
* `layoutBound_two_fifths`: coefficient `2/5` in degree four, from Gaussian vertex scores
  and a terminal core whose edge count is at most `12/5` times the original cycle rank.
* `layoutBound_degree`: coefficient `A_d = 3d/(2d-3) * arccos(2√(d-1)/d)/π` in every
  fixed degree `d ≥ 3`. It is below `3/4`, equals `2/5` at degree four, and keeps parallel
  edges throughout the compression and Gaussian concentration argument.

## Structure of the proof

```
Frontier.Layouts.Kernel         distance kernels on graphs of bounded maximum degree
Frontier.Layouts.Probability    Gaussian forms; Sheppard's crossing bound; windows and tails
Frontier.Layouts.SecondMoment   concentration of counts of local events
Frontier.Layouts.Star           angles between vectors close to a common vector
Frontier.Layouts.Median         ordering a cubic graph by median edge scores
Frontier.Layouts.Gaussian       the random layout: CubicLayoutBound p
Frontier.Layouts.Compression    from cubic graphs to subcubic multigraphs
Frontier.Layouts.Vertex*        Gaussian vertex layouts in every fixed degree
Frontier.Layouts.Quartic*       degree-four compression and the coefficient 2/5
Frontier.Layouts.Multi*         compression and Gaussian ordering with parallel edges
Frontier.Layouts.BoundedDegree  the cycle-rank coefficient A_d in every degree d ≥ 3
```
-/

@[expose] public section

namespace Complexity.Frontier

/-- A larger coefficient gives a weaker layout bound. -/
theorem LayoutBound.mono {d : ℕ} {A A' : ℝ} (h : LayoutBound d A) (hAA' : A ≤ A') :
    LayoutBound d A' := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hconn hloop hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  refine ⟨π, fun t => (hπ t).trans ?_⟩
  have : (A + η) * G.cycleRank ≤ (A' + η) * G.cycleRank := by gcongr
  linarith

/-- **Gaussian layouts.** Connected, loopless multigraphs of maximum degree three have layouts
of width `(2p + o(1)) β₁ + o(|V|)`, where `p = (3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem layoutBound_gaussian : LayoutBound 3 (2 * Gaussian.gaussianCoefficient) :=
  LayoutBound.of_cubic Gaussian.gaussianCoefficient_pos.le Gaussian.cubicLayoutBound_gaussian

/-- **The coefficient one third.** -/
theorem layoutBound_one_third : LayoutBound 3 (1 / 3) :=
  layoutBound_gaussian.mono (by linarith [Gaussian.two_mul_gaussianCoefficient_le])

end Complexity.Frontier
