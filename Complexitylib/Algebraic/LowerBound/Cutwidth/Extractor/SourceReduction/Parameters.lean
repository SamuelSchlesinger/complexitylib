/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters.Defs
public import Mathlib.Analysis.Real.Sqrt
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Parameters.Internal

/-!
# Finite budgets for the actual sumset source reduction

The single affine error budget pays exactly for all parity tests of order
at most four and every candidate. The chosen parity bias satisfies the
fourth-moment budget. At outer bit scale `b >= 5`, the selection theorem's
discard allowance leaves a positive number of good coordinates and meets
the majority theorem's square-root margin.

These finite estimates implement conservative parameters for
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Lemma 5.4,
<https://arxiv.org/pdf/2110.12652>. They do not supply the sampler, source
entropy, eventual parameter guards, or a uniform evaluation certificate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The outer index type is nonempty at every size. -/
theorem sourceReductionOuterCount_pos (b : Nat) : 0 < sourceReductionOuterCount b :=
  Internal.sourceReductionOuterCount_pos b

/-- The candidate index type is nonempty at every size. -/
theorem sourceReductionCandidateCount_pos (b : Nat) : 0 < sourceReductionCandidateCount b :=
  Internal.sourceReductionCandidateCount_pos b

/-- The single actual affine construction has a positive tampering count. -/
theorem sourceReductionTamperingCount_pos (b : Nat) : 0 < sourceReductionTamperingCount b :=
  Internal.sourceReductionTamperingCount_pos b

/-- The honest and tampered slots together hold four complete candidate families. -/
theorem sourceReductionTamperingCount_add_one (b : Nat) :
    sourceReductionTamperingCount b + 1 = 4 * sourceReductionCandidateCount b :=
  Internal.sourceReductionTamperingCount_add_one b

/-- A positive outer scale leaves room to flip an advice bit for unused slots. -/
theorem sourceReductionAdviceLength_pos {b : Nat} (positive : 0 < b) :
    0 < sourceReductionAdviceLength b :=
  Internal.sourceReductionAdviceLength_pos positive

/-- The sampler test allowance is positive. -/
theorem sourceReductionSamplerError_pos (b : Nat) : 0 < sourceReductionSamplerError b :=
  Internal.sourceReductionSamplerError_pos b

/-- The strict bad-seed discrepancy threshold is positive. -/
theorem sourceReductionBadThreshold_pos (b : Nat) : 0 < sourceReductionBadThreshold b :=
  Internal.sourceReductionBadThreshold_pos b

/-- The sign-parity bias parameter is nonnegative. -/
theorem sourceReductionParityBias_nonneg (b : Nat) : 0 ≤ sourceReductionParityBias b :=
  Internal.sourceReductionParityBias_nonneg b

/-- The union of all fourth-order parity tests and candidate tests exactly spends the allowance. -/
theorem sourceReduction_union_budget (b : Nat) :
    (sourceReductionOuterCount b : ℝ) ^ 4 * sourceReductionCandidateCount b *
      (((2 : ℝ) ^ sourceReductionTarget b)⁻¹ / sourceReductionBadThreshold b) =
        sourceReductionSamplerError b :=
  Internal.sourceReduction_union_budget b

/-- Every retained coordinate set satisfies the checked fourth-moment budget. -/
theorem sourceReduction_moment_budget {b m : Nat} (size : m ≤ sourceReductionOuterCount b) :
    100 * (m : ℝ) ^ 2 * sourceReductionParityBias b ≤ 1 :=
  Internal.sourceReduction_moment_budget size

/-- The selection theorem's discard allowance has this exact dyadic size. -/
theorem sourceReduction_bad_count_bound (b : Nat) :
    2 * sourceReductionSamplerError b * sourceReductionOuterCount b =
      (2 : ℝ) ^ (3 * b + 1) :=
  Internal.sourceReduction_bad_count_bound b

/-- The actual selection allowance gives a positive good set and the required majority margin. -/
theorem sourceReduction_majority_guards {b m : Nat} (large : 5 ≤ b)
    (size : m ≤ sourceReductionOuterCount b)
    (bad : ((sourceReductionOuterCount b - m : Nat) : ℝ) ≤
      2 * sourceReductionSamplerError b * sourceReductionOuterCount b) :
    0 < m ∧ ((sourceReductionOuterCount b - m : Nat) : ℝ) ≤ Real.sqrt (m : ℝ) / 8 :=
  Internal.sourceReduction_majority_guards large size bad

end Algebraic.Cutwidth.Extractor
