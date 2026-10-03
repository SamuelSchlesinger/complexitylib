/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs

/-!
# The actual advice outputs in the first affine phase

The honest and one selected tampered second seed are evaluated on the
original joint law. The retained coordinates are the complete first right
transcript, the original left latent state, and the actual tampered seed.
This is the pairwise seed law used before the final linear extraction.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual second seed retains all first right messages and the entire original left state. -/
noncomputable def affinePhaseOneSecondSeedWeight (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) (i : Fin t) :
    ((AffinePhaseOneRightTranscript Z t L₀ × A) × (Fin (matchedBlockSeedBits L₁) → Bool)) ×
      (Fin (matchedBlockSeedBits L₁) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let seeds := (affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p).2
    (((affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1, p.2), seeds (some i)),
      seeds none)) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
