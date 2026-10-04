/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
public import Complexitylib.Algebraic.Basis.Binary
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
-/

public section

namespace Algebraic.Cutwidth

/-- The fixed uniformly computable hard family has an unconditional coefficient-four
deterministic circuit lower bound, measured at its full input length. -/
theorem sourceReductionHardFamily_eventually_lt_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∀ circuit : Circuit Binary.signature n 1,
      circuit.Computes Binary.interpretation
        (fun x _ => Extractor.sourceReductionHardFamily n x) →
        (4 - ε) * n < circuit.size :=
  Extractor.Internal.sourceReductionHardFamily_eventually_lt_size hε

end Algebraic.Cutwidth
