/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Average.Internal

/-!
# The actual affine construction tolerates deterministic seed leakage on average

The source supplies the selected affine construction's entropy reserve plus
all `(t + 1) * d` leakage bits. For arbitrary shifts and tampered base seeds
chosen as functions of the honest base seed, the average conditional output
discrepancy is at most the construction's selected dyadic error. Conditioning
uses exact source masses and normalized completions for impossible leakage
transcripts, with no conditional entropy or security hypothesis from the caller.

This proves the average-error step of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources*, Lemma 5.3, printed pp.19--20:
<https://arxiv.org/abs/2110.12652>. The tampered seed retains `f y i`; the
argument does not replace it by the honest base seed. The subsequent bad-seed
counting argument is a separate finite averaging theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- All source-dependent seed leakage is paid before applying the actual selected affine map. -/
theorem affineLeakageOutputWeight_average_dist_le (n t a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) →
      Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (advice : Option (Fin t) → List Bool)
    (g : (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool) →
      Fin n → Bool)
    (f : (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool) →
      Fin t → Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (positive : 0 < t) (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ (affineIterationSourceEntropy n t a target +
      (t + 1) * affinePhaseOneRightBits n t a (affineIterationTarget t target)))⁻¹)
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
    ∑ y, uniformWeight (Fin d → Bool) y *
      weightDist (affineLeakageOutputWeight cb p leak advice (g y) y (f y))
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice (g y) y (f y))) ≤
      ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affineLeakageOutputWeight_average_dist_le n t a target p leak advice g f
    positive probability cap honest_length tampered_length different

end Algebraic.Cutwidth.Extractor
