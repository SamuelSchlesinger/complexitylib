/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs

/-!
# Initialize actual affine iteration from the executed first phase

The initializer uses the first phase's exact observed transcript, original
conditional kernels, and actual output contributions. Both original
source maps are lifted to that transcript. No extraction certificate is
stored or assumed by this construction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Package the actual first phase as the initial state for the repeated merging rounds. -/
noncomputable def affinePhaseOneIterationState (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) :
    AffineIterationState n d h t L₁ (AffinePhaseOneTranscript Z t L₀ L₁) A B where
  weight := affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice
  left := affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x
  right := affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice
  source z := x z.1.1.1
  mask z := mask z.1.1.1
  rightWords z := ys z.1.1.1
  leftRows := affinePhaseOneOutputLeft n t h L₀ L₁ er x
  rightRows := affinePhaseOneOutputRight n t h L₀ L₁ er mask

/-- Add the first phase's actual transcript while retaining both original latent states. -/
def affinePhaseOneIterationLift (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) : (AffinePhaseOneTranscript Z t L₀ L₁ × B) × A :=
  ((affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p, p.1.2), p.2)

end Algebraic.Cutwidth.Extractor
