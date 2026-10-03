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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Second.Internal

/-!
# The actual advice-generated seed in the first affine phase

The first masked extraction supplies an approximately uniform seed to the
actual advice correlation breaker with the original right source as input.
The source envelope pays for every first right observation. The resulting
second seed is close to uniform given the original left state and one
actual tampered second seed, without an intermediate security premise.

This is the advice step of Chattopadhyay--Liao, *Extractors for Sum of Two
Sources* (2021), Theorem 6.1, printed p.23:
<https://arxiv.org/abs/2110.12652>. It supplies a pairwise seed guarantee;
the final extraction and the later subset-doubling argument are separate.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- The actual second-seed law equals the observed advice call on the original source. -/
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
        (advice none) (advice (some i)) :=
  Internal.affinePhaseOneSecondSeedWeight_eq_alternating n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i

/-- The two actual advice outputs and retained original states form a probability law. -/
theorem affinePhaseOneSecondSeedWeight_probability (n d t L₀ e₀ L₁ e₁ : Nat)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (advice : Option (Fin t) → List Bool) (i : Fin t)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (affinePhaseOneSecondSeedWeight n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i) :=
  Internal.affinePhaseOneSecondSeedWeight_probability n d t L₀ e₀ L₁ e₁ w l r x mask ys advice i hw hl hr

/-- Original source hypotheses imply the actual pairwise second-seed bound. -/
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
        ((2 : ℝ) ^ target)⁻¹ :=
  Internal.affinePhaseOne_second_seed_dist_le n d t L₀ e₀ L₁ target
    w l r x mask ys advice i μ length room error size guard output_size hw hl hr
    nonnegative cap uniform advice_length different source_budget seed_width

end Algebraic.Cutwidth.Extractor
