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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.False.Internal

/-!
# The actual honest-false, tampered-true flip-flop guarantee

The output of `flipFlopStep` on honest advice `false` is nearly uniform
given the complete two-pass transcript, the opposite-advice tampered final
output, and the entire original left state. Inputs on either side may be
arbitrarily correlated; the original left and right kernels factor given
the old transcript. Only original honest source envelopes and the original
prefix discrepancy are assumed. Every extractor is the actual scheduled
matched-width Boolean program.

The first refresh has error `ρ`. A correlated repair preserves both original
source envelopes and makes that coordinate exactly uniform given the first
transcript. The second look-ahead and final refresh then apply to that law.
Returning to the actual retained transcript costs `2 * ρ`. The first
transcript multiplies the total left envelope by `M^4` and the right envelope
by `N^2`; the last refresh yields the displayed `N^5` term. Cardinalities stay
symbolic, with no enumeration of their large Boolean alphabets.

This proves one advice orientation in Chattopadhyay--Goyal--Li's Algorithm 1
and Lemma 6.8, Section 6.3, <https://arxiv.org/pdf/1505.00107>. The common-scale
implementation and this conservative finite accounting are the checked
specialization here. The other orientation is proved in `Opposite.True`.
`Advice.Extraction` proves the complete advice-chain guarantee
(`adviceCorrelationBreaker_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The direct original-law output is normalized for either honest advice bit. -/
theorem flipFlopOppositeWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b) :=
  Internal.flipFlopOppositeWeight_probability n m L e w l r x x' y y' q q' b hw hl hr

/-- The complete actual false-versus-true execution is close to its own retained marginal
times a uniform final state, from original source envelopes and the original prefix error. -/
theorem flipFlopOpposite_false_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ν : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => flipFlopSeedPrefix L (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z b => flipFlopSeedPrefix L (q z b)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let M : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let N : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    let ρ := 2 * ε + δ + (K : ℝ) * (∑ z, μ z) + (J : ℝ) * N ^ 2 * ∑ z, ν z
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' false)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' false)) ≤
        2 * ρ + 4 * ε + (K : ℝ) * (1 + M ^ 2) * M ^ 4 * (∑ z, μ z) +
          (K : ℝ) * M ^ 2 / N + (J : ℝ) * N ^ 5 * ∑ z, ν z :=
  Internal.flipFlopOpposite_false_dist_le n m L e guard w l r x x' y y' q q' μ ν
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

end Algebraic.Cutwidth.Extractor
