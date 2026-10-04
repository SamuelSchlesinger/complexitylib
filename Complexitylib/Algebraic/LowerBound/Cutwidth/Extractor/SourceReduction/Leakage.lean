/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Average
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.BadSeeds
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parameters

/-!
# Few bad seeds for the actual affine correlation breaker

For the complete selected construction, most honest seeds remain good
after deterministic source-dependent seed leakage, simultaneously for
every shift and every tuple of tampered seeds. The original source pays
for all `t + 1` leakage words. No caller-supplied security or conditional
entropy statement is required.

This proves the finite form of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.3, with the library's actual
conservative affine parameters:
<https://arxiv.org/abs/2110.12652>.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual selected affine construction has at most a `2^-target / γ` fraction of bad seeds. -/
theorem affineLeakageBadSeeds_parameters_card_le (n t a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) →
      Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (advice : Option (Fin t) → List Bool) {γ : ℝ}
    (positive : 0 < t) (error : 0 < γ) (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ affineLeakageSourceEntropy n t a target)⁻¹)
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i)) :
    let σ := affineIterationTarget t target
    let d := affinePhaseOneRightBits n t a σ
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a σ
    let L := affinePhaseOneScale n t a σ
    let e := affinePhaseOneLocalError σ
    let cb := affineCorrelationBreaker n d h L₀ e L (adviceErrorExponent a e) e
      (affineIterationRounds t)
    ((affineLeakageBadSeeds cb p leak advice γ).card : ℝ) ≤
      (((2 : ℝ) ^ target)⁻¹ / γ) * Fintype.card (Fin d → Bool) := by
  dsimp only
  apply affineLeakageBadSeeds_card_le _ p leak advice error
  intro g f
  exact affineLeakageOutputWeight_average_dist_le n t a target p leak advice g f positive
    probability cap honest_length tampered_length different

end Algebraic.Cutwidth.Extractor
