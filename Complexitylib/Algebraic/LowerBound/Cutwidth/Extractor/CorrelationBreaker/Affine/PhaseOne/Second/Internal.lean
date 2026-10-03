/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Alternating.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Initial
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Alternating
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Security of the actual second seed in the first affine phase

Use the actual masked first extraction as the standard advice breaker's
seed, after conditioning on every first right message. The uniform
original right input pays the finite message alphabet in its source
envelope. The output retains the original left state and one actual
tampered second seed, so the next extraction may observe all first outputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem affinePhaseOneSecondSeedWeight_eq_alternating (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) (i : Fin t) :
    affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i =
      alternatingAdviceWeight d (matchedBlockOutputBits 64 L₀) L₁ e₁ w l r
        (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)
        (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a none)
        (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a (some i))
        (fun z b => ys z b none) (fun z b => ys z b (some i))
        (advice none) (advice (some i)) := by
  unfold affinePhaseOneSecondSeedWeight alternatingAdviceWeight
  apply congrArg (fun f => mapWeight f (factoredWeight w l r))
  funext p
  have honest := congrFun (affinePhaseOneFirstLeft_eq n d t L₀ e₀ x mask ys p) none
  have tampered := congrFun (affinePhaseOneFirstLeft_eq n d t L₀ e₀ x mask ys p) (some i)
  dsimp only [affinePhaseOneTranscript, affinePhaseOneSecondSeed]
  dsimp only [affinePhaseOneRightTranscript] at honest tampered ⊢
  rw [honest, tampered]

theorem affinePhaseOneSecondSeedWeight_probability (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) (i : Fin t)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i) :=
  (factoredWeight_probability w l r hw hl hr).map _

private theorem uniform_message_budget (d k m : Nat) (budget : k + m ≤ d) :
    (2 : ℝ) ^ m * ((2 : ℝ) ^ d)⁻¹ ≤ ((2 : ℝ) ^ k)⁻¹ := by
  have bound : (2 : ℝ) ^ (m + k) ≤ 2 ^ d :=
    pow_le_pow_right₀ (by norm_num) (by lia)
  calc
    _ ≤ (2 : ℝ) ^ m * ((2 : ℝ) ^ (m + k))⁻¹ :=
      mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ (by positivity) (by positivity)).mpr bound) (by positivity)
    _ = _ := by
      rw [pow_add, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (by positivity), mul_one]

theorem affinePhaseOne_second_seed_dist_le (n d t L₀ e₀ L₁ target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool)
    (i : Fin t) (μ : Z → ℝ)
    (length : Nat.clog 2 (n + 1) ≤ L₀) (room : 64 ≤ L₀) (error : e₀ + 64 + 2 ≤ L₀)
    (size : matchedBlockSeedBits L₀ ≤ d)
    (guard : FlipFlopSizeGuard d (matchedBlockOutputBits 64 L₀) L₁
      (adviceErrorExponent (advice none).length target))
    (output_size : matchedBlockOutputBits 64 L₁ ≤ matchedBlockOutputBits 64 L₀)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) = uniformWeight (Fin d → Bool))
    (advice_length : (advice none).length = (advice (some i)).length)
    (different : advice none ≠ advice (some i))
    (source_budget : 2 ^ 150 * ((advice none).length + 1) * L₁ +
      (t + 1) * (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀) ≤ d)
    (seed_width : 2 ^ 150 * ((advice none).length + 1) * L₁ ≤ matchedBlockOutputBits 64 L₀) :
    let e₁ := adviceErrorExponent (advice none).length target
    let actual := affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i
    weightDist actual (uniformSecondWeight actual) ≤
      ((2 : ℝ) ^ e₀)⁻¹ + (2 : ℝ) ^ (2 ^ 142 * L₀) * ∑ z, μ z +
        ((2 : ℝ) ^ target)⁻¹ := by
  have initial := affinePhaseOne_initial_seed_dist_le n d t L₀ e₀ length room error size
    w l r x mask ys μ hw hl hr nonnegative cap uniform
  have right_cap (z : Z) (y₀ : Fin d → Bool) :
      w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ w z * ((2 : ℝ) ^ d)⁻¹ := by
    rw [uniform]
    simp only [uniformWeight, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, le_refl]
  have total : (∑ z, w z * ((2 : ℝ) ^ d)⁻¹) = ((2 : ℝ) ^ d)⁻¹ := by
    rw [← Finset.sum_mul, hw.2, one_mul]
  have budget : (Fintype.card (AffinePhaseOneRightMessage t L₀) : ℝ) *
      (∑ z, w z * ((2 : ℝ) ^ d)⁻¹) ≤
        ((2 : ℝ) ^ (2 ^ 150 * ((advice none).length + 1) * L₁))⁻¹ := by
    rw [total, card_affinePhaseOneRightMessage, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_mul, Nat.mul_comm (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀)]
    exact uniform_message_budget _ _ _ source_budget
  dsimp only
  rw [affinePhaseOneSecondSeedWeight_eq_alternating]
  exact alternatingAdvice_dyadic_dist_le d (matchedBlockOutputBits 64 L₀) L₁ target
    w l r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)
    (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a none)
    (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a (some i))
    (fun z b => ys z b none) (fun z b => ys z b (some i))
    (advice none) (advice (some i)) (fun z => w z * ((2 : ℝ) ^ d)⁻¹)
    guard output_size hw hl hr (fun z => mul_nonneg (hw.1 z) (by positivity))
    right_cap initial advice_length different budget seed_width

end Algebraic.Cutwidth.Extractor.Internal
