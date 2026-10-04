/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Reindex
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler

/-!
# The enumerated sampler used by the actual reduction

The concrete binary encodings transport the sampling theorem to the exact
finite ranges traversed by the reduction. The same index maps preserve
unconditional source XOR-linearity.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem sourceReductionSampler_xor (n L : Nat) (x y : Fin n → Bool)
    (i : Fin (sourceReductionOuterCount (matchedBlockSeedBits L)))
    (z : Fin (sourceReductionCandidateCount (matchedBlockSeedBits L))) :
    sourceReductionSampler n L (fun j => Bool.xor (x j) (y j)) i z =
      fun j => Bool.xor (sourceReductionSampler n L x i z j)
        (sourceReductionSampler n L y i z j) :=
  amplifiedMatchedSampler_xor n L (sourceReductionSeedBits n L) x y _ _

theorem sourceReductionSampler_somewhereSampler (n L : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    SomewhereSampler (sourceReductionSampler n L)
      ((2 : ℝ) ^ amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L))
      (sourceReductionSamplerError (matchedBlockSeedBits L)) (1 / 2) :=
  (amplifiedMatchedSampler_somewhereSampler n L (sourceReductionSeedBits n L)
    positive base gamma).reindex
    (sourceReductionIndexEquiv (sourceReductionOuterBits (matchedBlockSeedBits L)))
    (sourceReductionIndexEquiv (sourceReductionCandidateBits (matchedBlockSeedBits L)))

end Algebraic.Cutwidth.Extractor.Internal
