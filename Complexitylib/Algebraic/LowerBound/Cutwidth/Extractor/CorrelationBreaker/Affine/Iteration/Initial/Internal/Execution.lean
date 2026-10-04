/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# The initialized iteration is the complete actual affine algorithm

The first phase and all following rounds are deterministic observations
and calls on the same original variables. Their composed factorization
and output equations identify the actual retained-subset law directly.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneIterationState_iterate_factored (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    mapWeight (fun p => s.lift er rounds
      (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p))
      (factoredWeight w l r) =
      factoredWeight (s.iterate er rounds).weight
        (s.iterate er rounds).left (s.iterate er rounds).right := by
  dsimp only
  rw [← mapWeight_comp, affinePhaseOneIterationState_factored
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice (fun z => (hl z).1) hr]
  have probability := affinePhaseOneIterationState_probability
    n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice hw hl hr
  exact AffineIterationState.iterate_factored _ er rounds
    probability.1 probability.2.1 probability.2.2

theorem affinePhaseOneIterationState_iterate_rows_eq (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (j : Option (Fin t)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    let q := s.lift er rounds (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p)
    (fun k => Bool.xor
      ((s.iterate er rounds).leftRows q.1.1 q.2 j k)
      ((s.iterate er rounds).rightRows q.1.1 q.1.2 j k)) =
      affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds
        (fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k))
        (ys p.1.1 p.1.2 j) (advice j) := by
  dsimp only
  unfold affineCorrelationBreaker
  rw [← affinePhaseOneIterationState_rows_eq n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice p j]
  exact AffineIterationState.iterate_rows_eq _ er rounds
    (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p) j

theorem affinePhaseOneIterationState_subsetWeight_eq (n d t h L₀ e₀ L₁ e₁ er rounds : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t))
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    let s := affinePhaseOneIterationState n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice
    (s.iterate er rounds).subsetWeight S =
      mapWeight (fun p : (Z × B) × A =>
        let input := fun k => Bool.xor (x p.1.1 p.2 k) (mask p.1.1 p.1.2 k)
        let tag := s.transcript er rounds
          (affinePhaseOneIterationLift n d t L₀ e₀ L₁ e₁ x mask ys advice p)
        (((tag, p.1.2), fun j : S =>
          affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
            (ys p.1.1 p.1.2 (some j.val)) (advice (some j.val))),
          affineCorrelationBreaker n d h L₀ e₀ L₁ e₁ er rounds input
            (ys p.1.1 p.1.2 none) (advice none)))
        (factoredWeight w l r) := by
  dsimp only
  rw [AffineIterationState.subsetWeight,
    ← affinePhaseOneIterationState_iterate_factored
      n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice hw hl hr,
    mapWeight_comp]
  congr 1
  funext p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      exact affinePhaseOneIterationState_iterate_rows_eq
        n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice p (some j.val)
  · exact affinePhaseOneIterationState_iterate_rows_eq
      n d t h L₀ e₀ L₁ e₁ er rounds w l r x mask ys advice p none

end Algebraic.Cutwidth.Extractor.Internal
