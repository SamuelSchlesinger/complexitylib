/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant.Defs

/-!
# Finite errors and actual output laws of repeated affine rounds

Each round doubles the previous discrepancy and adds eight times its
local dyadic error. The closed expression records exactly that recurrence;
it is not an assumed security guarantee for the evolving state.

The state laws retain the complete original right variable and selected
left or actual masked rows. The complete-program law is a direct image
of the original factored distribution, retaining the original tag and
right variable along with the selected actual tampered outputs.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The exact discrepancy recurrence after `i` subset-doubling rounds. -/
noncomputable def affineIterationError (e : Nat) (ρ : ℝ) (i : Nat) : ℝ :=
  (2 : ℝ) ^ i * ρ + 8 * ((2 : ℝ) ^ i - 1) * ((2 : ℝ) ^ e)⁻¹

namespace AffineIterationState

variable {n d h t L : Nat} {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]

/-- Retain the full right state, selected left rows, and the honest left row. -/
noncomputable def leftSubsetWeight (s : AffineIterationState n d h t L Z A B)
    (S : Finset (Fin t)) :
    ((Z × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) ×
      (Fin (matchedBlockOutputBits h L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((p.1, fun j : S => s.leftRows p.1.1 p.2 (some j.val)), s.leftRows p.1.1 p.2 none))
    (factoredWeight s.weight s.left s.right)

/-- Retain the full right state and selected actual masked rows, with the honest masked row. -/
noncomputable def subsetWeight (s : AffineIterationState n d h t L Z A B)
    (S : Finset (Fin t)) :
    ((Z × B) × (S → Fin (matchedBlockOutputBits h L) → Bool)) ×
      (Fin (matchedBlockOutputBits h L) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    ((p.1, fun j : S => fun k => Bool.xor
      (s.leftRows p.1.1 p.2 (some j.val) k) (s.rightRows p.1.1 p.1.2 (some j.val) k)),
      fun k => Bool.xor (s.leftRows p.1.1 p.2 none k) (s.rightRows p.1.1 p.1.2 none k)))
    (factoredWeight s.weight s.left s.right)

end AffineIterationState

/-- The complete actual algorithm retaining the original tag, full right state, and tampered outputs. -/
noncomputable def affineCorrelationBreakerWeight (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) :
    ((Z × B) × (S → Fin (matchedBlockOutputBits h L₁) → Bool)) ×
      (Fin (matchedBlockOutputBits h L₁) → Bool) → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let input := fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k)
    ((p.1, fun j : S => affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
      (ys p.1.1 p.1.2 (some j.val)) (advice (some j.val))),
      affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
        (ys p.1.1 p.1.2 none) (advice none)))
    (factoredWeight w l r)

end Algebraic.Cutwidth.Extractor
