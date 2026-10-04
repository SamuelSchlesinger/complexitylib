/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Layout.Internal.Limit

/-!
# Gaussian layouts of cubic graphs

Every large simple cubic graph has a vertex ordering whose prefix cuts have at most
`((3/π)(3 - 2√2) + ξ) h` edges, for any slack `ξ > 0`. The coefficient
`(3/π)(3 - 2√2) ≈ 0.16384` is below the `1/6` of the Monien–Preis bisection and
Fomin–Høie pathwidth bounds.

The ordering sorts Gaussian scores `X_v = ⟨â_v, ω⟩`, where `â_v` is the normalized
truncated distance kernel `z ↦ q ^ dist(v, z)` (radius `R`) and `ω` has independent
standard Gaussian coordinates. Adjacent kernel rows have correlation at least
`2q/(1+q²) - 3(2q²)^R` in every graph of maximum degree three
(`Gaussian.sum_unitKernel_mul_ge`), so each threshold separates an edge with probability at
most `(2/π)√((1-ρ)/(1+ρ))` (`Gaussian.gaussPi_between_le`). A threshold grid, the locality
of the kernel, and a second-moment bound (`Gaussian.pi_deviation_le`) control all
prefixes of one sample simultaneously.
The limiting correlation `2√2/3` is that of the Gaussian wave functions on the 3-regular
tree studied by Csóka, Gerencsér, Harangi, and Virág (*Invariant Gaussian processes and
independent sets on regular graphs of large girth*, 2015) and used by Lyons (*Factors of
IID on trees*, 2017) for bisections of random cubic graphs. The truncated kernel and its
correlation bound for every graph of maximum degree three are developed here.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- **Gaussian cubic cutwidth.** For every positive slack `ξ`, every sufficiently large
simple cubic graph on `h` vertices has an injective vertex key whose prefix cuts have at
most `((3/π)(3 - 2√2) + ξ) h` edges. -/
theorem exists_cutwidthBound {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, CutwidthBound cutwidthCoefficient ξ N₀ :=
  Internal.exists_key_bound hξ

/-- The Gaussian cutwidth coefficient is positive. -/
theorem cutwidthCoefficient_pos : 0 < cutwidthCoefficient :=
  Internal.cutwidthCoefficient_pos

/-- The doubled coefficient `(6/π)(3 - 2√2)` is the graph-ordering coefficient; it is at
most `20/61`, hence below `1/3`. -/
theorem two_mul_cutwidthCoefficient_le : 2 * cutwidthCoefficient ≤ 20 / 61 :=
  Internal.two_mul_cutwidthCoefficient_le

/-- The circuit coefficient `1 + 1/A` of the Gaussian ordering coefficient
`A = 2 (3/π)(3 - 2√2)` equals `1 + π(3 + 2√2)/6 ≈ 4.0517`. -/
theorem one_add_inv_two_mul_cutwidthCoefficient :
    1 + 1 / (2 * cutwidthCoefficient) = 1 + Real.pi * (3 + 2 * Real.sqrt 2) / 6 :=
  Internal.one_add_inv_two_mul_cutwidthCoefficient

end Algebraic.Cutwidth.Gaussian
