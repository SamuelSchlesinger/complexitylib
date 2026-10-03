/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Initial.Internal

/-!
# The initial seed of the actual affine phase

A uniform original right input supplies the balanced prefix used by the
first linear extractor. Its actual masked output is close to uniform even
after retaining every tampered prefix and first mask contribution. The
bound uses only the original source's point-mass envelope; it assumes no
intermediate seed certificate or execution witness.

This supplies the first extraction in Chattopadhyay--Liao, *Extractors for
Sum of Two Sources* (2021), Theorem 6.1, printed p.23:
<https://arxiv.org/abs/2110.12652>. The subsequent advice call and extraction,
and the later independence-merging rounds, require further proofs.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A sufficiently long uniform right input has a uniform first seed prefix. -/
theorem affinePhaseOneFirstSeed_uniform (d L₀ : Nat) (size : matchedBlockSeedBits L₀ ≤ d) :
    mapWeight (affinePhaseOneFirstSeed d L₀) (uniformWeight (Fin d → Bool)) =
      uniformWeight (Fin (matchedBlockSeedBits L₀) → Bool) :=
  Internal.affinePhaseOneFirstSeed_uniform d L₀ size

/-- The actual initial extraction retains all first right messages at no additional cost. -/
theorem affinePhaseOne_initial_seed_dist_le (n d t L₀ e₀ : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₀) (room : 64 ≤ L₀) (error : e₀ + 64 + 2 ≤ L₀)
    (size : matchedBlockSeedBits L₀ ≤ d)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) = uniformWeight (Fin d → Bool)) :
    let actual := alternatingSeedWeight w l r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)
      (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a none)
    weightDist actual (uniformSecondWeight actual) ≤
      ((2 : ℝ) ^ e₀)⁻¹ + (2 : ℝ) ^ (2 ^ 142 * L₀) * ∑ z, μ z :=
  Internal.affinePhaseOne_initial_seed_dist_le n d t L₀ e₀ length room error size
    w l r x mask ys μ hw hl hr nonnegative cap uniform

end Algebraic.Cutwidth.Extractor
