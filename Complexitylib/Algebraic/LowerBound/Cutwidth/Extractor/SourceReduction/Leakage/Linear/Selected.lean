/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Linear
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Parity

/-!
# Actual affine calls supply the linear-sampler parity estimate

The complete selected affine construction supplies both the small bad set
and the parity estimate outside that set. The source has only its original
point-mass bound; no extractor, security, or parity-bias witness is assumed.
The caller supplies a linear map for the sampler values at the selected
call positions. Choosing and amplifying the global sampler is a separate
step of Chattopadhyay--Liao, Lemma 5.4.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual construction gives a small seed test and all corresponding linear-sampler parities. -/
theorem affineLeakage_linear_parameters (n t a target : Nat)
    (p : (Fin n → Bool) → ℝ)
    (sampler : (Fin n → Bool) → Option (Fin t) →
      Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool)
    (advice : Option (Fin t) → List Bool)
    (j : Fin (matchedBlockOutputBits (growingMatchedBlockDepth t)
      (affinePhaseOneScale n t a (affineIterationTarget t target)))) {γ : ℝ}
    (positive : 0 < t) (error : 0 < γ) (probability : IsProbabilityWeight p)
    (cap : ∀ x, p x ≤ ((2 : ℝ) ^ affineLeakageSourceEntropy n t a target)⁻¹)
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i))
    (linear : ∀ x y i, sampler (xorInput x y) i = xorInput (sampler x i) (sampler y i)) :
    let σ := affineIterationTarget t target
    let d := affinePhaseOneRightBits n t a σ
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a σ
    let L := affinePhaseOneScale n t a σ
    let e := affinePhaseOneLocalError σ
    let cb := affineCorrelationBreaker n d h L₀ e L (adviceErrorExponent a e) e
      (affineIterationRounds t)
    let bad := affineLeakageBadSeeds cb p sampler advice γ
    ((bad.card : ℝ) ≤ (((2 : ℝ) ^ target)⁻¹ / γ) * Fintype.card (Fin d → Bool)) ∧
      ∀ b, sampler b none ∉ bad →
        |∑ x, p x * ∏ i, if cb (xorInput x b) (sampler (xorInput x b) i) (advice i) j
          then (1 : ℝ) else -1| ≤ 2 * γ := by
  dsimp only
  refine ⟨affineLeakageBadSeeds_parameters_card_le n t a target p sampler advice
    positive error probability cap honest_length tampered_length different, ?_⟩
  intro b good
  exact affineLeakage_linear_parity_le (n := n) (t := t)
    (affineCorrelationBreaker n
      (affinePhaseOneRightBits n t a (affineIterationTarget t target))
      (growingMatchedBlockDepth t)
      (affinePhaseOneInitialScale n t a (affineIterationTarget t target))
      (affinePhaseOneLocalError (affineIterationTarget t target))
      (affinePhaseOneScale n t a (affineIterationTarget t target))
      (adviceErrorExponent a (affinePhaseOneLocalError (affineIterationTarget t target)))
      (affinePhaseOneLocalError (affineIterationTarget t target)) (affineIterationRounds t))
    p sampler advice linear (fun out => out j)
    (mapWeight_uniform_bool_coordinate j) γ b good

end Algebraic.Cutwidth.Extractor
