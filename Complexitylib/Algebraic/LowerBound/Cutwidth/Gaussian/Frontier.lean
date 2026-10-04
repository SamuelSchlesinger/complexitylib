/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Internal.Limit

/-!
# Gaussian edge-score decompositions of cubic graphs

Every large simple cubic graph has a path decomposition whose bags have at most
`((3/(2π)) arccos ((1 + 2√2)/4) + ξ) h` vertices, for every slack `ξ > 0`. The coefficient
`(3/(2π)) arccos ((1 + 2√2)/4) ≈ 0.14035` is well below the `1/6` of the Fomin–Høie bound.

Each edge `uv` receives the Gaussian score `⟨(x_u + x_v)/‖x_u + x_v‖, ω⟩`, where `x` are the
normalized truncated distance-kernel rows of `Gaussian.Layout`; the edges are listed by score,
and a vertex stays in the bags between its first and last edge (`Gaussian.Frontier.Order`).
A vertex therefore occupies the bag at threshold `t` exactly when `t` separates two of its
three edge scores, which happens with probability at most half the summed crossing
probabilities of its edge pairs; by Sheppard's bound (`Gaussian.Edge.Exact`) a pair with
correlation `ρ'` crosses any threshold with probability at most `arccos ρ' / π`. The three edge vectors at a vertex lie within correlation
`√((1 + ρ)/2)` of the vertex row, where `ρ` bounds the kernel correlation of adjacent rows;
since `‖Σ y_e‖ ≥ ⟨Σ y_e, x_v⟩`, their average pairwise correlation is at least `(1 + 3ρ)/4`,
and concavity of `arccos` (`Gaussian.Frontier.Arccos`) bounds the summed angles. With
`ρ → 2√2/3` the per-vertex probability is at most `(3/(2π)) arccos ((1 + 2√2)/4)`, the
coefficient above. A threshold grid and the second-moment bound control every bag of one
sample, as for the cutwidth layout.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- **Gaussian cubic pathwidth.** For every positive slack `ξ`, every sufficiently large
simple cubic graph on `h` vertices has a path decomposition with bags of at most
`((3/(2π)) arccos ((1 + 2√2)/4) + ξ) h + 1` vertices. -/
theorem exists_frontier_pathwidthBound {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, PathwidthBound frontierCoefficient ξ N₀ :=
  Internal.exists_pathwidthBound_frontier hξ

/-- The frontier coefficient is positive. -/
theorem frontierCoefficient_pos : 0 < frontierCoefficient :=
  Internal.frontierCoefficient_pos

/-- The doubled frontier coefficient, the graph-ordering coefficient of this decomposition,
is at most `9/32`. -/
theorem two_mul_frontierCoefficient_le : 2 * frontierCoefficient ≤ 9 / 32 :=
  Internal.two_mul_frontierCoefficient_le

/-- The circuit coefficient `1 + 1/(2p)` of the frontier coefficient `p` equals
`1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem one_add_inv_two_mul_frontierCoefficient :
    1 + 1 / (2 * frontierCoefficient) =
      1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) :=
  Internal.one_add_inv_two_mul_frontierCoefficient

end Algebraic.Cutwidth.Gaussian
