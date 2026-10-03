/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs

/-!
# Actual final pair laws of the first affine phase

Both laws retain the complete executed transcript, the original right
latent state, and one actual tampered final value. The first keeps the
original-left extraction contributions; the second keeps the XOR-masked
program outputs. Each is a deterministic image of the original factored
source, with no intermediate distribution substituted.

These are the pairwise base laws in the first phase of Chattopadhyay--Liao,
*Extractors for Sum of Two Sources* (2021), Theorem 6.1, printed p.23:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- The actual left contributions, retaining one tampering, the transcript, and original B. -/
noncomputable def affinePhaseOneLeftPairWeight (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) :
    ((AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool)) ×
        (Fin (matchedBlockOutputBits h L₁) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let z := affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p
    (((z, p.1.2), affinePhaseOneOutputLeft n t h L₀ L₁ er x z p.2 (some i)),
      affinePhaseOneOutputLeft n t h L₀ L₁ er x z p.2 none)) (factoredWeight w l r)

/-- The actual masked outputs, retaining one tampering, the transcript, and original B. -/
noncomputable def affinePhaseOnePairWeight (n d t h L₀ e₀ L₁ e₁ er : Nat)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) :
    ((AffinePhaseOneTranscript Z t L₀ L₁ × B) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool)) ×
        (Fin (matchedBlockOutputBits h L₁) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let input := fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)
    (((affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p, p.1.2),
      affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er input
        (ys p.1.1 p.1.2 (some i)) (advice (some i))),
      affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er input
        (ys p.1.1 p.1.2 none) (advice none))) (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
