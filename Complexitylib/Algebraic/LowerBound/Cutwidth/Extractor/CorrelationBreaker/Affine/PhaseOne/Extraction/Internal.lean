/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Final
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import Mathlib.Tactic.Ring

/-!
# Composing the actual three-call first affine phase

Derive the actual advice seed from original source assumptions, then use
it for the final growing-depth linear extraction. Both the left-side
contribution and the complete masked output retain the actual transcript,
original right state, and one actual tampered output. No intermediate
seed or execution witness remains as a premise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

private theorem final_coefficient (t h L₀ L₁ : Nat) :
    (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁) *
        Fintype.card (Fin (matchedBlockOutputBits h L₁) → Bool) *
        Fintype.card (AffinePhaseOneCopies t (matchedBlockOutputBits 64 L₀)) =
      (2 : ℝ) ^ (2 ^ (2 * h + 14) * L₁ + matchedBlockOutputBits h L₁ +
        (t + 1) * matchedBlockOutputBits 64 L₀) := by
  rw [card_affinePhaseOneCopies]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem affinePhaseOne_left_pair_dist_le (n d t h L₀ e₀ L₁ target er : Nat)
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
    (final_length : Nat.clog 2 (n + 1) ≤ L₁)
    (final_error : er + h + 2 ≤ L₁)
    (final_budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
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
    let actual := affinePhaseOneLeftPairWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice i
    weightDist actual (uniformSecondWeight actual) ≤
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) := by
  have seed := affinePhaseOne_second_seed_dist_le n d t L₀ e₀ L₁ target
    w l r x mask ys advice i μ length room error size guard output_size hw hl hr
    nonnegative cap uniform advice_length different source_budget seed_width
  have final := affinePhaseOneLeftPair_dist_le n d t h L₀ e₀ L₁
    (adviceErrorExponent (advice none).length target) er final_length final_error final_budget
    w l r x mask ys advice i μ hw hl hr nonnegative cap seed
  rw [final_coefficient] at final
  simpa only [affinePhaseOneError] using final

theorem affinePhaseOne_pair_dist_le (n d t h L₀ e₀ L₁ target er : Nat)
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
    (final_length : Nat.clog 2 (n + 1) ≤ L₁)
    (final_error : er + h + 2 ≤ L₁)
    (final_budget : (h + 1) * (er + 2 * h + Nat.clog 2 (L₁ + 1) + 4) ≤ L₁)
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
    let actual := affinePhaseOnePairWeight n d t h L₀ e₀ L₁ e₁ er
      w l r x mask ys advice i
    weightDist actual (uniformSecondWeight actual) ≤
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) := by
  exact (affinePhaseOnePair_dist_le_left n d t h L₀ e₀ L₁
    (adviceErrorExponent (advice none).length target) er w l r x mask ys advice i).trans
      (affinePhaseOne_left_pair_dist_le n d t h L₀ e₀ L₁ target er
        w l r x mask ys advice i μ length room error size guard output_size
        final_length final_error final_budget hw hl hr nonnegative cap uniform
        advice_length different source_budget seed_width)

end Algebraic.Cutwidth.Extractor.Internal
