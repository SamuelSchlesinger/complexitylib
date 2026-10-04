/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Mathlib.Analysis.Asymptotics.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Asymptotics.Internal

/-!
# An actual sumset-extractor family with sublinear source entropy

Choose `L = clog 2 (n+1)` in the fixed finite source reduction. Both concrete
sampler guards eventually hold, and the actual selected entropy exponent
is little-o of `n`. The candidate count remains the full exponential of the
cubic Gamma seed budget; it too is sublinear in `n`, so an eventual linear
cap can be used in a separate total evaluator.

These are numerical deductions for the checked Chattopadhyay--Liao
Lemma 5.4 construction, <https://arxiv.org/abs/2110.12652>. Cslib's natural
exponential-versus-polynomial theorem supplies the limit comparison. The
statistical conclusion concerns the actual fixed map, with error `35/72`.
This module does not assert polynomial-time evaluation of its full outer
and candidate enumeration.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Filter

/-- The full, unbounded candidate count is sublinear in the original input length. -/
theorem sourceReductionCandidateCount_isLittleO :
    (fun n : Nat =>
      (sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) :=
  Internal.sourceReductionCandidateCount_isLittleO

/-- Clamping the candidate count at `n+1` is eventually inactive. -/
theorem eventually_sourceReductionCandidateCount_le :
    ∀ᶠ n : Nat in atTop,
      sourceReductionCandidateCount (matchedBlockSeedBits (Nat.clog 2 (n + 1))) ≤ n + 1 :=
  Internal.eventually_sourceReductionCandidateCount_le

/-- The complete source reserve, including every leakage word and the sampler, is sublinear. -/
theorem sourceReductionEntropy_isLittleO :
    (fun n : Nat => (sourceReductionEntropy n (Nat.clog 2 (n + 1)) : ℝ))
      =o[atTop] (fun n => (n : ℝ)) :=
  Internal.sourceReductionEntropy_isLittleO

/-- The selected source support threshold is eventually feasible within `n` bits. -/
theorem eventually_sourceReductionEntropy_le :
    ∀ᶠ n : Nat in atTop, sourceReductionEntropy n (Nat.clog 2 (n + 1)) ≤ n :=
  Internal.eventually_sourceReductionEntropy_le

/-- The actual growing matched and Gamma samplers meet all their finite numerical guards. -/
theorem eventually_sourceReduction_guards :
    ∀ᶠ n : Nat in atTop,
      let L := Nat.clog 2 (n + 1)
      0 < L ∧ GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4 ∧
        GammaBlockSizeGuard (matchedBlockSeedBits L) :=
  Internal.eventually_sourceReduction_guards

/-- One fixed actual Boolean family eventually extracts from both flat sources. -/
theorem eventually_sourceReductionExtractor_flat :
    ∀ᶠ n : Nat in atTop,
      FlatSumsetExtractor (sourceReductionExtractor n (Nat.clog 2 (n + 1)))
        (2 ^ sourceReductionEntropy n (Nat.clog 2 (n + 1))) (35 / 72) :=
  Internal.eventually_sourceReductionExtractor_flat

end Algebraic.Cutwidth.Extractor
