/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed.Defs

/-!
# The actual first-phase left-row subset law

This is the generic old-left-row law at the full first-phase transcript,
with its original left kernel and actual left-contribution outputs. It is
therefore the exact initialization used by subsequent affine rounds.
No repaired law, entropy premise, or security invariant is built into the
definition. The pairwise initialization follows the first phase of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources*, Theorem 6.1:
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The generic left-row law at the complete actual first-phase transcript and kernels. -/
noncomputable def affinePhaseOneLeftRowsWeight (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) :
    (AffinePhaseOneTranscript Z t L₀ L₁ × (S → Fin (matchedBlockOutputBits h L₁) → Bool)) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool) → ℝ :=
  affineRoundLeftRowsWeight h t L₁
    (affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice)
    (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x)
    (affinePhaseOneOutputLeft n t h L₀ L₁ er x) S

end Algebraic.Cutwidth.Extractor
