/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Padded.Defs
public import Mathlib.Basic.Real.Basic

/-!
# Finite parameters for the sumset source reduction

One global affine breaker handles every parity of at most four outer
coordinates and all their candidate calls. Its error pays for the union of
those tests. The resulting parity bias and discarded-coordinate allowance
are chosen for the checked moment and majority bounds.

These are conservative finite choices for the strategy in Chattopadhyay--
Liao, *Extractors for Sum of Two Sources*, Lemma 5.4 and equation (5):
<https://arxiv.org/pdf/2110.12652>. The choices alone do not assert the
sampler guards, source entropy, asymptotics, or a uniform evaluator.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Bit width of the outer sampler index. -/
def sourceReductionOuterBits (b : Nat) : Nat := 8 * b

/-- Bit width of the candidate index, using the actual padded Gamma seed budget. -/
def sourceReductionCandidateBits (b : Nat) : Nat := gammaBlockSeedBudget b

/-- Number of outer coordinates in the final majority. -/
def sourceReductionOuterCount (b : Nat) : Nat := 2 ^ sourceReductionOuterBits b

/-- Number of affine calls XORed at each outer coordinate. -/
def sourceReductionCandidateCount (b : Nat) : Nat := 2 ^ sourceReductionCandidateBits b

/-- One honest call and enough tampered slots for every parity of order at most four. -/
def sourceReductionTamperingCount (b : Nat) : Nat := 4 * sourceReductionCandidateCount b - 1

/-- An injective advice word records the outer and candidate indices. -/
def sourceReductionAdviceLength (b : Nat) : Nat :=
  sourceReductionOuterBits b + sourceReductionCandidateBits b

/-- Local dyadic error exponent of the single selected affine breaker. -/
def sourceReductionTarget (b : Nat) : Nat := 54 * b + sourceReductionCandidateBits b + 10

/-- Size allowance for the common sampler test. -/
noncomputable def sourceReductionSamplerError (b : Nat) : ℝ := ((2 : ℝ) ^ (5 * b))⁻¹

/-- Discrepancy threshold defining each bad-seed test. -/
noncomputable def sourceReductionBadThreshold (b : Nat) : ℝ := ((2 : ℝ) ^ (17 * b + 10))⁻¹

/-- Low-order sign-parity bias furnished outside the bad-seed tests. -/
noncomputable def sourceReductionParityBias (b : Nat) : ℝ := 2 * sourceReductionBadThreshold b

end Algebraic.Cutwidth.Extractor
