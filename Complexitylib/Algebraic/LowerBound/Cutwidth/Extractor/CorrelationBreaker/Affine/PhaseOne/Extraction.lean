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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Extraction.Internal

/-!
# Pairwise security of the actual first affine phase

The three actual calls give a pairwise guarantee from the original
normalized source factors, a uniform honest right input, unequal advice,
and finite numerical budgets. Both laws retain the complete executed
transcript and original right state. The left-contribution guarantee is
suited to subsequent merging; the masked-output guarantee concerns the
actual program. Neither theorem assumes an intermediate seed certificate.

This proves the pairwise first phase of the standard-to-affine conversion
in Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021),
Theorem 6.1, printed p.23, for the displayed actual components and budgets:
<https://arxiv.org/abs/2110.12652>. The later subset-doubling rounds are
required to obtain joint security against all tamperings.
-/

public section

namespace Algebraic.Cutwidth.Extractor

universe u

/-- Original source assumptions bound the actual left contributions against one tampering. -/
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
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) :=
  Internal.affinePhaseOne_left_pair_dist_le n d t h L₀ e₀ L₁ target er
    w l r x mask ys advice i μ length room error size guard output_size
    final_length final_error final_budget hw hl hr nonnegative cap uniform
    advice_length different source_budget seed_width

/-- The complete actual masked first phase satisfies the pairwise strong guarantee. -/
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
      affinePhaseOneError t h L₀ e₀ L₁ target er (∑ z, μ z) :=
  Internal.affinePhaseOne_pair_dist_le n d t h L₀ e₀ L₁ target er
    w l r x mask ys advice i μ length room error size guard output_size
    final_length final_error final_budget hw hl hr nonnegative cap uniform
    advice_length different source_budget seed_width

end Algebraic.Cutwidth.Extractor
