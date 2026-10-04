/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Seed
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Projecting actual pair laws to initial left-row subsets

A subset of one selected index is either that singleton or empty. The
same deterministic projection handles both: drop the original right state
and repeat the retained tampered value on the requested subset. Exact
factorization identifies its law with the first-phase left-row marginal.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem affinePhaseOneLeftRowsWeight_eq_map_pair (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (i : Fin t) (selected : S ⊆ {i})
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S =
      mapWeight (fun p => ((p.1.1.1, fun _ : S => p.1.2), p.2))
        (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
          w l r x mask ys advice i) := by
  have finalRight : ∀ z, IsProbabilityWeight
      (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice z) := by
    apply observedTranscriptKernel_probability
    intro z
    exact observedTranscriptKernel_probability r _ hr z.1
  unfold affinePhaseOneLeftRowsWeight affineRoundLeftRowsWeight observedSeedWeight
  rw [← factoredWeight_right_marginal _
    (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice) _ finalRight,
    ← factoredWeight_swap, mapWeight_comp,
    ← affinePhaseOneTranscript_factored n d t L₀ e₀ L₁ e₁ w l r x mask ys advice hl hr,
    mapWeight_comp]
  unfold affinePhaseOneLeftPairWeight
  simp only [mapWeight_comp]
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  let z := affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p
  apply congrArg (fun f : S → Fin (matchedBlockOutputBits h L₁) → Bool =>
    ((z, f), affinePhaseOneOutputLeft n t h L₀ L₁ er x z p.2 none))
  funext j
  exact congrArg (fun k => affinePhaseOneOutputLeft n t h L₀ L₁ er x z p.2 (some k))
    (Finset.mem_singleton.mp (selected j.property))

theorem affinePhaseOneLeftRowsWeight_dist_le_pair (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (i : Fin t) (selected : S ⊆ {i})
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice S)
      (uniformSecondWeight (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er
        w l r x mask ys advice S)) ≤
      weightDist (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
        w l r x mask ys advice i)
        (uniformSecondWeight (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
          w l r x mask ys advice i)) := by
  have projected := weightDist_uniformSecond_map_first_le
    (affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice i)
    (fun p => (p.1.1, fun _ : S => p.2))
  rw [← affinePhaseOneLeftRowsWeight_eq_map_pair n d t h L₀ e₀ L₁ e₁ er
    w l r x mask ys advice S i selected hl hr] at projected
  exact projected

theorem affinePhaseOneLeftRowsWeight_probability (n d t h L₀ e₀ L₁ e₁ er : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (S : Finset (Fin t)) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneLeftRowsWeight n d t h L₀ e₀ L₁ e₁ er w l r x mask ys advice S) := by
  have full := affinePhaseOneTranscript_probability n d t L₀ e₀ L₁ e₁
    w l r x mask ys advice hw hl hr
  exact affineRoundLeftRowsWeight_probability h t L₁ _ _ _ S full.1 full.2.1

end Algebraic.Cutwidth.Extractor.Internal
