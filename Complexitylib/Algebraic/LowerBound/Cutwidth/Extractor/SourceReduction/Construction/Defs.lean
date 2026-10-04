/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Tests.Defs

/-!
# The actual finite sumset-extractor construction

The amplified matched sampler produces the seed of one fixed affine
correlation breaker. Its advice encodes the outer and candidate indices.
XOR over candidates gives each outer bit, and strict majority gives the
final bit. None of these choices depends on the source sets or on a tested
parity. All maps are total, including outside the finite sampling guards.

This is the construction strategy of Chattopadhyay--Liao, *Extractors for
Sum of Two Sources*, Lemma 5.4 and the proof of Theorem 2:
<https://arxiv.org/abs/2110.12652>. Its parameters use the library's
conservative matched and Gamma extractors. Eventual entropy bounds and
uniform evaluation of the complete family are proved in
`Construction.Asymptotics` and `Construction.Uniform`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The seed width of the single affine breaker used by the entire reduction. -/
def sourceReductionSeedBits (n L : Nat) : Nat :=
  let b := matchedBlockSeedBits L
  affineTestSeedBits n (sourceReductionCandidateCount b) (sourceReductionAdviceLength b)
    (sourceReductionTarget b)

/-- Source entropy sufficient for both affine leakage and the amplified sampler. -/
def sourceReductionEntropy (n L : Nat) : Nat :=
  let b := matchedBlockSeedBits L
  max (affineLeakageSourceEntropy n (sourceReductionTamperingCount b)
    (sourceReductionAdviceLength b) (sourceReductionTarget b))
    (amplifiedMatchedSamplerEntropy L (sourceReductionSeedBits n L))

/-- The actual sampler with explicit binary enumeration of both seed indices. -/
def sourceReductionSampler (n L : Nat) (x : Fin n → Bool)
    (i : Fin (sourceReductionOuterCount (matchedBlockSeedBits L)))
    (z : Fin (sourceReductionCandidateCount (matchedBlockSeedBits L))) :
    Fin (sourceReductionSeedBits n L) → Bool :=
  let b := matchedBlockSeedBits L
  amplifiedMatchedSampler n L (sourceReductionSeedBits n L) x
    (sourceReductionIndexWord (sourceReductionOuterBits b) i)
    (sourceReductionIndexWord (sourceReductionCandidateBits b) z)

/-- XOR the actual candidate calls, using injective fixed-length binary advice. -/
def sourceReductionOutput (n L : Nat) (x : Fin n → Bool) :
    Fin (sourceReductionOuterCount (matchedBlockSeedBits L)) → Bool :=
  let b := matchedBlockSeedBits L
  affineSourceReduction
    (affineTestBit n (sourceReductionCandidateCount b) (sourceReductionAdviceLength b)
      (sourceReductionTarget b)) (sourceReductionSampler n L)
    (fun i z => sourceReductionAdvice (sourceReductionOuterBits b)
      (sourceReductionCandidateBits b) (i, z)) x

/-- The final finite construction: majority of the actual XOR-reduction outputs. -/
def sourceReductionExtractor (n L : Nat) (x : Fin n → Bool) : Bool :=
  Complexity.majority (sourceReductionOutput n L x)

end Algebraic.Cutwidth.Extractor
