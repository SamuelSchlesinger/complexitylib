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
public import Mathlib.Order.Filter.AtTopBot.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Hardness.Internal

/-!
# Explicit deterministic circuit lower bounds above four

The fixed family `sourceReductionHardFamily` requires more than
`(1 + π(3 + 2√2)/6 - ε) * n ≈ (4.0517 - ε) * n` binary gates at every
sufficiently large input length, for every positive `ε`. No extractor,
entropy, or graph premise remains. `Construction.Uniform` supplies the single
polynomial-time evaluator and its exact agreement with this same family.

The same family needs more than `(1 + 1/A - ε) * n` gates whenever the
graph-ordering hypothesis `Multigraph.OrderingBound A η C` holds for some
`A > 0` at every positive slack. The cubic pathwidth bound gives `A = 1/3`
and the coefficient four; the Gaussian layout (`Cutwidth.Gaussian`) gives
`A = (6/π)(3 - 2√2) ≈ 0.32768`, and its rational weakening `A = 20/61` gives
the coefficient `81/20`.
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

/-- **The Gaussian-layout bound for the explicit family.** Every full-binary-basis circuit
for the fixed uniformly computable hard family has more than
`(1 + π(3 + 2√2)/6 - ε) n ≈ (4.0517 - ε) n` gates at every sufficiently large full input
length, for every positive `ε`. -/
theorem sourceReductionHardFamily_eventually_lt_size_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (1 + Real.pi * (3 + 2 * Real.sqrt 2) / 6 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size_gaussian hε

/-- **A rational coefficient above four.** The rational ordering coefficient `20/61 < 1/3`
gives the explicit family a `(81/20 - ε) n` lower bound at its full input length. -/
theorem sourceReductionHardFamily_eventually_lt_eightyOne_div_twenty_size {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (81 / 20 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_eightyOne_div_twenty_size hε

end Algebraic.Cutwidth
