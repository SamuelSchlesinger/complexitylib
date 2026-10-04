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
of the kernel, and a second-moment bound (`Gaussian.pi_real_deviation_le`) control all
prefixes of one sample simultaneously.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian

/-- **Gaussian cubic cutwidth.** For every positive slack `ξ`, every sufficiently large
simple cubic graph on `h` vertices has an injective vertex key whose prefix cuts have at
most `((3/π)(3 - 2√2) + ξ) h` edges. -/
theorem exists_key_cutFinset_le {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.IsRegularOfDegree 3 → N₀ < Fintype.card W →
      ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
        ((H.cutFinset (Finset.univ.filter fun w => key w < t)).card : ℝ) ≤
          (gaussianCutwidthCoefficient + ξ) * Fintype.card W :=
  Internal.exists_key_bound hξ

end Algebraic.Cutwidth.Gaussian
