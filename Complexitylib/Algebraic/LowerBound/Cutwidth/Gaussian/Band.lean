/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Internal.Limit

/-!
# Band-jump decompositions of cubic graphs (conditional)

Assume the band clusters of the Gaussian edge-score field are subcritical
(`BandSubcritical`, an open percolation hypothesis). Then for every `c > 0` and every slack
`ξ > 0`, every large simple cubic graph on `h` vertices has a path decomposition whose bags
have at most `(exp (-c²/2) p + ξ) h + 1` vertices, where
`p = (3/(2π)) arccos ((1 + 2√2)/4)` is the frontier coefficient of `Gaussian.Frontier`.

The decomposition is the band-jump order of `Gaussian.Band.Order` for the edge scores of one
Gaussian sample, with the band clusters as blocks. Outside the band `[-c, c)` a vertex
straddles a threshold `t` with probability at most `exp (-t²/2) p` by the threshold-decay
crossing bound (`Gaussian.Edge.Decay`), and `|t| ≥ c` there; a grid on each side and the
second-moment bound control every threshold of one sample. Inside the band a bag also holds
the vertices of one block. Such a block lies in one band cluster, which either has at most
`K` vertices or consists of vertices in clusters of more than `K` vertices; by the hypothesis
and Markov's inequality the latter number at most `2 η h` for some sample. Taking `K`
negligible against `h` gives the coefficient.

At `c = 4/25` the doubled coefficient is at most `5/18`, the graph-ordering coefficient of
the circuit bound `23/5`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- **Band-jump cubic pathwidth** (conditional on `BandSubcritical`). If the band clusters
are subcritical for every decay rate `q < 1/√2` and radius `R`, then for every positive slack
`ξ`, every sufficiently large simple cubic graph on `h` vertices has a path decomposition with
bags of at most `(exp (-c²/2) · (3/(2π)) arccos ((1 + 2√2)/4) + ξ) h + 1` vertices. -/
theorem exists_band_pathwidthBound {c : ℝ} (hc : 0 < c)
    (hband : ∀ (q : ℝ) (R : ℕ), 0 ≤ q → 2 * q ^ 2 < 1 → BandSubcritical q R c) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, PathwidthBound (Real.exp (-(c ^ 2) / 2) * frontierCoefficient) ξ N₀ :=
  Internal.exists_pathwidthBound_band hc hband hξ

/-- At `c = 4/25` the doubled band-jump coefficient `2 exp (-c²/2) p` is at most `5/18`. -/
theorem two_mul_exp_mul_frontierCoefficient_le :
    2 * (Real.exp (-((4 / 25 : ℝ) ^ 2) / 2) * frontierCoefficient) ≤ 5 / 18 :=
  Internal.two_mul_exp_mul_frontierCoefficient_le

end Algebraic.Cutwidth.Gaussian
