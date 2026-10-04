/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Growing.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded.Defs

/-!
# The actual amplified linear sampler

The outer word and candidate choose a seed through the actual padded Gamma
extractor. The actual growing-depth matched extractor then reads the source
with that seed. Its requested output prefix is completed with false bits,
so the definition is total for every width. Gamma need not be linear: for
each fixed outer word and candidate, only the matched extractor reads the
source.

This is the source-linear sampler composition in Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.4 and Appendix A, proof of
Lemma 3.17: <https://arxiv.org/abs/2110.12652>. Finite sampling guarantees
and a uniform evaluator are separate theorems about this actual map.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Source entropy paying the growing extractor threshold and one sampling bit. -/
def amplifiedMatchedSamplerEntropy (L d : Nat) : Nat :=
  2 ^ (2 * growingMatchedBlockDepth d + 14) * L + 1

/-- The Gamma-selected matched output, truncated or false-completed to `d` bits. -/
def amplifiedMatchedSampler (n L d : Nat) (x : Fin n → Bool)
    (outer : Fin (8 * matchedBlockSeedBits L) → Bool)
    (candidate : Fin (gammaBlockSeedBudget (matchedBlockSeedBits L)) → Bool) : Fin d → Bool :=
  fun j => (List.ofFn (matchedBlockExtractor n (growingMatchedBlockDepth d) L 4 x
    (gammaBlockPaddedExtractor (matchedBlockSeedBits L) outer candidate)))[j.val]?.getD false

end Algebraic.Cutwidth.Extractor
