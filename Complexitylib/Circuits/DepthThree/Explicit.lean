/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.DepthThree
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Uniform.Defs
import Complexitylib.Circuits.DepthThree.Internal.Explicit

/-!
# Depth-three lower bounds for an explicit family in `P`

The explicit family `Algebraic.Cutwidth.Extractor.sourceReductionHardFamily` is computed by a
uniform polynomial-time evaluator (`sourceReductionHardEval_mem_FP`). Its accepted sets are
eventually `K`-rectangle-free with `log K = o(n)` and accept exactly half of the cube
(`Frontier.sourceReductionHardFamily_frontierHypotheses`), so they contain no subcube of dimension
`2 ⌈log₂ K⌉ = o(n)`. On inputs of positive length the family is balanced padding,
`f(x) = g(x_1, …, x_{n-1}) ⊕ x_0`, so flipping the first input bit exchanges its accepted and
rejected inputs, and the rejected sets have the same properties.

Hence, for every fixed `k`, both `Σ₃^k` and `Π₃^k` of the family are `2 ^ ((1/k - o(1)) n)`.

## Main results

* `sourceReductionHardFamily_two_rpow_le_sigmaThreeSize`: for every `k ≥ 1` and `ε > 0`,
  eventually `Σ₃^k ≥ 2 ^ ((1/k - ε) n)`: every OR of `k`-CNFs computing the family has at least
  that many CNFs.
* `sourceReductionHardFamily_two_rpow_le_piThreeSize`: the same for `Π₃^k`, ANDs of `k`-DNFs.
-/

@[expose] public section

namespace Complexity

open Filter

/-- **`Σ₃^k` lower bound for the explicit family.** For every `k ≥ 1` and `ε > 0`, for all large
`n`, every OR of CNFs of width at most `k` computing `sourceReductionHardFamily n` has at least
`2 ^ ((1/k - ε) n)` CNFs. -/
theorem sourceReductionHardFamily_two_rpow_le_sigmaThreeSize {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤
      sigmaThreeSize k (Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n) :=
  DepthThree.sourceReductionHardFamily_sigmaThree hk hε

/-- **`Π₃^k` lower bound for the explicit family.** For every `k ≥ 1` and `ε > 0`, for all large
`n`, every AND of DNFs of width at most `k` computing `sourceReductionHardFamily n` has at least
`2 ^ ((1/k - ε) n)` DNFs. -/
theorem sourceReductionHardFamily_two_rpow_le_piThreeSize {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((1 / (k : ℝ) - ε) * n) ≤
      piThreeSize k (Algebraic.Cutwidth.Extractor.sourceReductionHardFamily n) :=
  DepthThree.sourceReductionHardFamily_piThree hk hε

end Complexity
