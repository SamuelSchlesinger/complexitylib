/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript

/-!
# Initial envelopes for the unchanged original affine sources

These packages expose the existing first-phase envelope signs, caps, and
exact alphabet costs in the field coordinates of the actual iteration
initializer. No conditional entropy assumption is introduced.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneIterationState_left_envelope (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let envelope := affinePhaseOneTranscriptLeftEnvelope n d t L₀ e₀ L₁ e₁ μ r mask ys advice
    (∀ z, 0 ≤ envelope z) ∧
      (∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ envelope z) ∧
      (∑ z, envelope z) =
        (Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) : ℝ) *
          ∑ z, μ z := by
  refine ⟨?_, ?_, ?_⟩
  · exact affinePhaseOneTranscriptLeftEnvelope_nonnegative
      n d t L₀ e₀ L₁ e₁ μ r mask ys advice nonnegative hr
  · exact affinePhaseOneTranscript_left_envelope n d t L₀ e₀ L₁ e₁
      w l r x mask ys advice μ hw hl hr cap
  · exact affinePhaseOneTranscriptLeftEnvelope_sum n d t L₀ e₀ L₁ e₁ μ r mask ys advice hr

theorem affinePhaseOneIterationState_right_envelope (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (ν : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ ν z)
    (cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let envelope := affinePhaseOneTranscriptRightEnvelope n t L₀ e₀ L₁ ν l x
    (∀ z, 0 ≤ envelope z) ∧
      (∀ z y₀, s.weight z *
        mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ envelope z) ∧
      (∑ z, envelope z) =
        (Fintype.card (AffinePhaseOneCopies t (matchedBlockSeedBits L₁)) : ℝ) *
          Fintype.card (AffinePhaseOneRightMessage t L₀) * ∑ z, ν z := by
  refine ⟨?_, ?_, ?_⟩
  · exact affinePhaseOneTranscriptRightEnvelope_nonnegative
      n t L₀ e₀ L₁ ν l x nonnegative (fun z => (hl z).1)
  · exact affinePhaseOneTranscript_right_envelope n d t L₀ e₀ L₁ e₁
      w l r x mask ys advice (fun z b => ys z b none) ν hw hl hr cap
  · exact affinePhaseOneTranscriptRightEnvelope_sum n t L₀ e₀ L₁ ν l x (fun z => (hl z).2)

end Algebraic.Cutwidth.Extractor.Internal
