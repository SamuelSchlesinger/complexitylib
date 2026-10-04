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
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Defs

/-!
# Exact first-phase initialization of affine iteration

The initializer is the existing first-phase factorization and actual row
decomposition, with no statistical or extractor-guard premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneIterationState_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    IsProbabilityWeight s.weight ∧ (∀ z, IsProbabilityWeight (s.left z)) ∧
      ∀ z, IsProbabilityWeight (s.right z) :=
  affinePhaseOneTranscript_probability n d t L₀ e₀ L₁ e₁ w l r x mask ys advice hw hl hr

theorem affinePhaseOneIterationState_factored (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    mapWeight (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice)
      (factoredWeight w l r) = factoredWeight s.weight s.left s.right :=
  affinePhaseOneTranscript_factored n d t L₀ e₀ L₁ e₁ w l r x mask ys advice hl hr

theorem affinePhaseOneIterationState_rows_eq (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let q := affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p
    (fun k => Bool.xor (s.leftRows q.1.1 q.2 j k) (s.rightRows q.1.1 q.1.2 j k)) =
      affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er
        (fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k))
        (ys p.1.1 p.1.2 j) (advice j) :=
  (affinePhaseOneOutput_eq_xor n d t h L₀ e₀ L₁ e₁ er x mask ys advice p j).symm

theorem affinePhaseOneIterationState_leftRowsWeight_eq (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    affineRoundLeftRowsWeight h t L₁ s.weight s.left s.leftRows S =
      affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S := rfl

end Algebraic.Cutwidth.Extractor.Internal
