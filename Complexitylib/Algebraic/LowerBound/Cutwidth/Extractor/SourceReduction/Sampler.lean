/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Sampler.Amplification.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Internal.Basic

/-!
# An actual source-linear somewhere sampler

The actual growing-depth matched extractor, at constant error one sixteenth,
is amplified by the actual padded Gamma extractor. At the explicit finite
guards, the resulting sampler has failure probability one half and target
test density `2^(-5*b)`, where `b = 2^24 * L` is the base seed width. Its
source threshold is the growing extractor's threshold times two.

No extractor or coverage hypothesis is supplied by the caller. The only
guards concern the concrete numerical parameters. XOR-linearity holds at
every size, independently of those statistical guards. The construction
implements the amplification used in Chattopadhyay--Liao, *Extractors for
Sum of Two Sources*, Lemma 5.4 and Appendix A, proof of Lemma 3.17:
<https://arxiv.org/abs/2110.12652>. Selecting an eventual parameter family
and enumerating its outer coordinates remain separate steps.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The selected logarithmic depth supplies every requested output bit at positive scale. -/
theorem amplifiedMatchedSampler_output_capacity (L d : Nat) (positive : 0 < L) :
    d ≤ matchedBlockOutputBits (growingMatchedBlockDepth d) L :=
  Internal.amplifiedMatchedSampler_output_capacity L d positive

/-- At positive scale, false completion is inactive in the requested prefix. -/
theorem amplifiedMatchedSampler_eq_prefix (n L d : Nat) (positive : 0 < L)
    (x : Fin n → Bool) (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSampler n L d x outer candidate = fun j =>
      matchedBlockExtractor n (growingMatchedBlockDepth d) L 4 x
        (gammaBlockPaddedExtractor (matchedBlockSeedBits L) outer candidate)
        (Fin.castLE (amplifiedMatchedSampler_output_capacity L d positive) j) :=
  Internal.amplifiedMatchedSampler_eq_prefix n L d positive x outer candidate

/-- Each fixed outer word and candidate gives an XOR-linear map of the original source. -/
theorem amplifiedMatchedSampler_xor (n L d : Nat) (x x' : Fin n → Bool)
    (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) :
    amplifiedMatchedSampler n L d (fun i => Bool.xor (x i) (x' i)) outer candidate =
      fun j => Bool.xor (amplifiedMatchedSampler n L d x outer candidate j)
        (amplifiedMatchedSampler n L d x' outer candidate j) :=
  Internal.amplifiedMatchedSampler_xor n L d x x' outer candidate

/-- The actual composition samples small tests for every normalized source at the stated cap. -/
theorem amplifiedMatchedSampler_somewhereSampler (n L d : Nat) (positive : 0 < L)
    (base : GrowingMatchedBlockRuntimeValid n d L 4)
    (gamma : GammaBlockSizeGuard (matchedBlockSeedBits L)) :
    SomewhereSampler (amplifiedMatchedSampler n L d)
      ((2 : ℝ) ^ amplifiedMatchedSamplerEntropy L d)
      (((2 : ℝ) ^ (5 * matchedBlockSeedBits L))⁻¹) (1 / 2) :=
  Internal.amplifiedMatchedSampler_somewhereSampler n L d positive base gamma

end Algebraic.Cutwidth.Extractor
