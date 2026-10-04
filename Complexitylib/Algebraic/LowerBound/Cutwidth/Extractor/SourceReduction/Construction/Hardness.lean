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
# An explicit coefficient-four deterministic circuit lower bound

The fixed family `sourceReductionHardFamily` requires more than
`(4 - ε) * n` binary gates at every sufficiently large input length, for
every positive `ε`. No extractor, entropy, or graph premise remains.
`Construction.Uniform` supplies the single polynomial-time evaluator and
its exact agreement with this same family.

The same family needs more than `(1 + 1/A - ε) * n` gates whenever the
graph-ordering hypothesis `Multigraph.OrderingBound A η C` holds for some
`A > 0` at every positive slack. The proved bound has `A = 1/3`; a smaller
ordering coefficient improves the circuit coefficient without changing the
family.
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

end Algebraic.Cutwidth
