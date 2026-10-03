/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Exact execution and normalized first-phase transcript factors

The first extraction's XOR law makes its output left-only after observing
the seed and mask contribution. The actual advice outputs then become
right-only. Compose the three exact deterministic-observation identities;
no extractor security theorem or positive-row assumption enters this proof.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneFirstOutput_xor (n d L₀ e₀ : Nat) (x mask : Fin n → Bool)
    (y : Fin d → Bool) :
    affinePhaseOneFirstOutput n d L₀ e₀ (fun j => Bool.xor (x j) (mask j)) y =
      fun j => Bool.xor (affinePhaseOneFirstOutput n d L₀ e₀ x y j)
        (affinePhaseOneFirstOutput n d L₀ e₀ mask y j) :=
  matchedBlockExtractor_xor n 64 L₀ e₀ x mask (affinePhaseOneFirstSeed d L₀ y)

theorem affinePhaseOneFirstLeft_eq (n d t L₀ e₀ : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (p : (Z × B) × A) :
    affinePhaseOneFirstLeft n t L₀ e₀ x
        (affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1) p.2 =
      fun i => affinePhaseOneFirstOutput n d L₀ e₀
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j)) (ys p.1.1 p.1.2 i) := by
  funext i
  unfold affinePhaseOneFirstLeft
  dsimp only [affinePhaseOneRightTranscript, affinePhaseOneRightMessage]
  rw [affinePhaseOneFirstOutput_xor]
  rfl

theorem affinePhaseOneSecondRight_eq (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) :
    affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice
        (affinePhaseOneLeftTranscript n d t L₀ e₀ x mask ys p) p.1.2 =
      fun i => affinePhaseOneSecondSeed n d L₀ e₀ L₁ e₁
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j))
        (ys p.1.1 p.1.2 i) (advice i) := by
  unfold affinePhaseOneSecondRight
  dsimp only [affinePhaseOneLeftTranscript,
    affinePhaseOneRightTranscript, affinePhaseOneSecondSeed]

theorem affinePhaseOneOutput_eq_xor (n d t h L₀ e₀ L₁ e₁ er : Nat) {Z A B : Type*}
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (p : (Z × B) × A) (i : Option (Fin t)) :
    affinePhaseOneOutput n d h L₀ e₀ L₁ e₁ er
        (fun j => Bool.xor (x p.1.1 p.2 j) (mask p.1.1 p.1.2 j))
        (ys p.1.1 p.1.2 i) (advice i) =
      fun j => Bool.xor
        (affinePhaseOneOutputLeft n t h L₀ L₁ er x
          (affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p) p.2 i j)
        (affinePhaseOneOutputRight n t h L₀ L₁ er mask
          (affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p) p.1.2 i j) := by
  dsimp only [affinePhaseOneOutput, affinePhaseOneOutputLeft, affinePhaseOneOutputRight,
    affinePhaseOneTranscript, affinePhaseOneLeftTranscript, affinePhaseOneRightTranscript]
  exact matchedBlockExtractor_xor n h L₁ er (x p.1.1 p.2) (mask p.1.1 p.1.2) _

theorem affinePhaseOneRight_probability (n d t L₀ e₀ : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (w : Z → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys) ∧
      ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) := by
  exact ⟨observedTranscriptWeight_probability _ _ _ hw hr,
    observedTranscriptKernel_probability _ _ hr⟩

theorem affinePhaseOneLeft_probability (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys) ∧
      (∀ z, IsProbabilityWeight (affinePhaseOneLeftKernel n t L₀ e₀ l x z)) ∧
      ∀ z : AffinePhaseOneLeftTranscript Z t L₀,
        IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) := by
  obtain ⟨hw₀, hr₀⟩ := affinePhaseOneRight_probability n d t L₀ e₀ w r mask ys hw hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₀ (fun z => hl z.1),
    observedTranscriptKernel_probability _ _ (fun z => hl z.1), fun z => hr₀ z.1⟩

theorem affinePhaseOneTranscript_probability (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁
      w l r x mask ys advice) ∧
      (∀ z, IsProbabilityWeight (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x z)) ∧
      ∀ z, IsProbabilityWeight
        (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice z) := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := affinePhaseOneLeft_probability n d t L₀ e₀
    w l r x mask ys hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hw₁ hr₁,
    fun z => hl₁ z.1, observedTranscriptKernel_probability _ _ hr₁⟩

theorem affinePhaseOneRight_factored (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (mask : Z → B → Fin n → Bool) (ys : Z → B → AffinePhaseOneCopies t d)
    (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneRightTranscript n d t L₀ e₀ mask ys p.1, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys)
        (fun z => l z.1) (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys) :=
  factoredWeight_observe_right w l r _ hr

theorem affinePhaseOneLeft_factored (n d t L₀ e₀ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z b, 0 ≤ r z b) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneLeftTranscript n d t L₀ e₀ x mask ys p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
        (affinePhaseOneLeftKernel n t L₀ e₀ l x)
        (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1) := by
  have first := affinePhaseOneRight_factored n d t L₀ e₀ w l r mask ys hr
  have second := factoredWeight_observe_left
    (affinePhaseOneRightWeight n d t L₀ e₀ w r mask ys) (fun z => l z.1)
    (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys)
    (affinePhaseOneFirstLeft n t L₀ e₀ x) (fun z => hl z.1)
  rw [← first, mapWeight_comp] at second
  change mapWeight _ (factoredWeight w l r) = _ at second
  unfold affinePhaseOneLeftWeight affinePhaseOneLeftKernel
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (AffinePhaseOneLeftTranscript Z t L₀ × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affinePhaseOneFirstLeft_eq]
  rfl

theorem affinePhaseOneTranscript_factored (n d t L₀ e₀ L₁ e₁ : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (hl : ∀ z a, 0 ≤ l z a) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((affinePhaseOneTranscript n d t L₀ e₀ L₁ e₁ x mask ys advice p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (affinePhaseOneTranscriptWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice)
        (affinePhaseOneTranscriptLeft n t L₀ e₀ L₁ l x)
        (affinePhaseOneTranscriptRight n d t L₀ e₀ L₁ e₁ r mask ys advice) := by
  have first := affinePhaseOneLeft_factored n d t L₀ e₀ w l r x mask ys hl
    (fun z => (hr z).1)
  have hr₀ : ∀ z, IsProbabilityWeight (affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z) :=
    observedTranscriptKernel_probability _ _ hr
  have second := factoredWeight_observe_right
    (affinePhaseOneLeftWeight n d t L₀ e₀ w l r x mask ys)
    (affinePhaseOneLeftKernel n t L₀ e₀ l x)
    (fun z => affinePhaseOneRightKernel n d t L₀ e₀ r mask ys z.1)
    (affinePhaseOneSecondRight d t L₀ L₁ e₁ ys advice) (fun z => (hr₀ z.1).1)
  rw [← first, mapWeight_comp] at second
  unfold affinePhaseOneTranscriptWeight affinePhaseOneTranscriptLeft affinePhaseOneTranscriptRight
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (AffinePhaseOneTranscript Z t L₀ L₁ × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [affinePhaseOneSecondRight_eq]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
