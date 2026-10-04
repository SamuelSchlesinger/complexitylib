/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Internal.Sampler

/-!
# The actual finite sumset extractor

The concrete source-linear sampler and one fixed affine correlation breaker
supply every parity test of order at most four. Their exact error budgets
give enough good coordinates to apply the moment and majority theorems.
The final Boolean map is a flat-source sumset extractor with error `35/72`.
Its only premises are the positive scale and the two numerical sampler
guards; no sampler, security, or parity estimate is assumed.

This formalizes the finite composition in Chattopadhyay--Liao, *Extractors
for Sum of Two Sources*, Lemma 5.4 and the proof of Theorem 2:
<https://arxiv.org/abs/2110.12652>. The source threshold is the maximum of
the actual affine leakage and growing matched-sampler reserves. The eventual
sublinear entropy bound and uniform evaluation of the complete family are
proved separately, in `Construction.Asymptotics` and `Construction.Uniform`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Concrete binary enumeration preserves source XOR-linearity at every size. -/
theorem sourceReductionSampler_xor (n L : Nat) (x y : Fin n → Bool)
    (i : Fin (sourceReductionOuterCount (matchedBlockSeedBits L)))
    (z : Fin (sourceReductionCandidateCount (matchedBlockSeedBits L))) :
    sourceReductionSampler n L (xorInput x y) i z =
      xorInput (sourceReductionSampler n L x i z) (sourceReductionSampler n L y i z) :=
  Internal.sourceReductionSampler_xor n L x y i z

/-- The actual enumerated sampler meets its source, test-density, and failure budgets. -/
theorem sourceReductionSampler_somewhereSampler (n L : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    SomewhereSampler (sourceReductionSampler n L)
      ((2 : ℝ) ^ amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L))
      (sourceReductionSamplerError (matchedBlockSeedBits L)) (1 / 2) :=
  Internal.sourceReductionSampler_somewhereSampler n L positive base gamma

/-- Majority of the actual XOR reduction extracts from both flat sources at the stated reserve. -/
theorem sourceReductionExtractor_flat (n L : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    FlatSumsetExtractor (sourceReductionExtractor n L) (2 ^ sourceReductionEntropy n L)
      (35 / 72) :=
  Internal.sourceReductionExtractor_flat n L positive base gamma

end Algebraic.Cutwidth.Extractor
