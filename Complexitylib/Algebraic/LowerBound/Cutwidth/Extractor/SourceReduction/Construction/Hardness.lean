/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Algebraic.Basis.Binary
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Multigraph
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Band.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Defs
public import Mathlib.Order.Filter.AtTopBot.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Hardness.Internal

/-!
# Explicit deterministic circuit lower bounds above four

The fixed family `sourceReductionHardFamily` requires more than
`(1 + π/(3 arccos((1 + 2√2)/4)) - ε) * n ≈ (4.5625 - ε) * n` binary gates at every
sufficiently large input length, for every positive `ε`. No extractor,
entropy, or graph premise remains. `Construction.Uniform` supplies the single
polynomial-time evaluator and its exact agreement with this same family.

The same family needs more than `(1 + 1/A - ε) * n` gates whenever the
graph-ordering hypothesis `Multigraph.OrderingBound A η C` holds for some
`A > 0` at every positive slack. The cubic pathwidth bound gives `A = 1/3`
and the coefficient four; the Gaussian edge-score decomposition (`Cutwidth.Gaussian`)
gives `A = (3/π) arccos ((1 + 2√2)/4) ≈ 0.28070`, and its rational weakening `A = 9/32`
gives the coefficient `41/9`.

Two further bounds are conditional on the open percolation hypothesis
`Gaussian.BandSubcritical` (subcritical band clusters of the Gaussian edge-score field), which
is a premise of the theorems and not an axiom. Under it the band-jump decomposition
(`Gaussian.Band`) gives `A = 2 exp (-c²/2) p` with `p` the frontier coefficient, and at
`c = 4/25` its rational weakening `A = 5/18` gives the coefficient `23/5`.
-/

public section

namespace Algebraic.Cutwidth

/-- For every graph-ordering coefficient `A > 0` for which the ordering
hypothesis holds at every positive slack, the fixed uniformly computable hard
family needs more than `(1 + 1/A - ε) n` gates at its full input length. -/
theorem sourceReductionHardFamily_eventually_lt_size_of_orderingBound {A : ℝ} (hA : 0 < A)
    (order : ∀ η : ℝ, 0 < η → ∃ C : ℝ, Multigraph.OrderingBound A η C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (1 + 1 / A - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_of_orderingBound hA order hε

/-- The fixed uniformly computable hard family has an unconditional coefficient-four
deterministic circuit lower bound, measured at its full input length. -/
theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (4 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size hε

/-- **The Gaussian bound for the explicit family.** Every full-binary-basis circuit for the
fixed uniformly computable hard family has more than
`(1 + π/(3 arccos((1 + 2√2)/4)) - ε) n ≈ (4.5625 - ε) n` gates at every sufficiently large full
input length, for every positive `ε`. -/
theorem sourceReductionHardFamily_eventually_lt_size_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_gaussian hε

/-- **The rational coefficient `41/9`.** The rational ordering coefficient `9/32` gives the
explicit family a `(41/9 - ε) n` lower bound at its full input length. -/
theorem sourceReductionHardFamily_eventually_lt_size_fortyOne_div_nine {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (41 / 9 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_fortyOne_div_nine hε

/-- **The band-jump bound for the explicit family** (conditional). If the band clusters of the
Gaussian edge-score field are subcritical (`Gaussian.BandSubcritical q R c` for every decay rate
`q < 1/√2` and radius `R`), every full-binary-basis circuit for the fixed uniformly computable
hard family has more than `(1 + 1/(2 exp (-c²/2) p) - ε) n` gates at every sufficiently large
full input length, where `p = (3/(2π)) arccos ((1 + 2√2)/4)`. -/
theorem sourceReductionHardFamily_eventually_lt_size_of_bandSubcritical {c : ℝ} (hc : 0 < c)
    (hband : ∀ (q : ℝ) (R : ℕ), 0 ≤ q → 2 * q ^ 2 < 1 → Gaussian.BandSubcritical q R c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (1 + 1 / (2 * (Real.exp (-(c ^ 2) / 2) * Gaussian.frontierCoefficient)) - ε) * n <
          circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_of_bandSubcritical hc hband hε

/-- **The coefficient `23/5` for the explicit family** (conditional). If the band clusters of the
Gaussian edge-score field in the band `[-4/25, 4/25)` are subcritical
(`Gaussian.BandSubcritical q R (4/25)` for every decay rate `q < 1/√2` and radius `R`), every
full-binary-basis circuit for the fixed uniformly computable hard family has more than
`(23/5 - ε) n` gates at every sufficiently large full input length. -/
theorem sourceReductionHardFamily_eventually_lt_size_twentyThree_div_five_of_bandSubcritical
    (hband : ∀ (q : ℝ) (R : ℕ), 0 ≤ q → 2 * q ^ 2 < 1 →
      Gaussian.BandSubcritical q R (4 / 25))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (23 / 5 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_twentyThree_div_five_of_band
    hband hε

end Algebraic.Cutwidth
