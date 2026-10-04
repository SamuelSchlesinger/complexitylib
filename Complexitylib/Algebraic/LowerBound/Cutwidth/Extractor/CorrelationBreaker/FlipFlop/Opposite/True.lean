/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.True.Internal

/-!
# The actual honest-true, tampered-false flip-flop guarantee

The actual output is nearly uniform given the complete two-pass transcript,
its opposite-advice tampered final output, and the entire original left state.
Honest and tampered variables on either side may be arbitrarily correlated.
The two original side kernels factor given the original transcript. The only
security hypotheses concern the original honest source envelopes, the original
right look-ahead input envelope, and its initial prefix discrepancy.

The first honest refresh, retaining the tampered refresh, has error `ρ`.
The tampered right coordinate is observed exactly; a correlated repair makes
the honest coordinate uniform given that transcript while preserving both
original sources. The terminal
refresh then uses a left-only tampered seed. Returning to the actual retained
marginal costs `2 * ρ`. Both refreshes reread the original right source.
The left and right observation losses yield the displayed `M^5` and `N^5`
terms, without any independent refreshed-source assumption.

This is the second advice orientation of Chattopadhyay--Goyal--Li's Algorithm 1
and Lemma 6.8, Section 6.3, <https://arxiv.org/pdf/1505.00107>. The matched-width
programs and conservative finite error accounting are this library's checked
specialization. `Advice.Extraction` proves the complete advice-chain guarantee
(`adviceCorrelationBreaker_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The complete actual true-versus-false execution is close to its own retained marginal
times a uniform final state, with only original source and prefix hypotheses. -/
theorem flipFlopOpposite_true_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ν ξ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (state_nonnegative : ∀ z, 0 ≤ ν z)
    (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (state_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => flipFlopSeedPrefix L (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z b => flipFlopSeedPrefix L (q z b)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let M : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let N : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    let ρ := 4 * ε + δ + (K : ℝ) * (1 + M ^ 2) * (∑ z, μ z) +
      (K : ℝ) * M ^ 2 * (∑ z, ν z) + (J : ℝ) * N ^ 3 * ∑ z, ξ z
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' true)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' true)) ≤
        2 * ρ + 2 * ε + (K : ℝ) * M ^ 5 * (∑ z, μ z) +
          (J : ℝ) * N ^ 5 * ∑ z, ξ z :=
  Internal.flipFlopOpposite_true_dist_le n m L e guard w l r x x' y y' q q' μ ν ξ
    hw hl hr left_nonnegative state_nonnegative right_nonnegative
    left_cap state_cap right_cap seed

end Algebraic.Cutwidth.Extractor
