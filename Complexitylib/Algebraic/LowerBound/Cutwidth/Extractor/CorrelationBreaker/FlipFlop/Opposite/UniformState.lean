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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.UniformState.Internal

/-!
# Opposite-advice extraction from a nearly uniform whole state

For either honest advice bit, the actual output is nearly uniform given
both complete look-ahead histories, the opposite-advice tampered final
output, and the full original left state. The original left and right
kernels factor given the old transcript; honest and tampered maps on each
side may be arbitrarily correlated.

Only the original honest X/Y joint source envelopes and the whole honest
right-state discrepancy are assumed. The false branch uses contraction
under the checked uniform prefix map. The true branch repairs the right
coordinate inside its full correlated state, preserving every original
source envelope. Its exact uniform cap supplies the middle-source bound.
Returning to the actual retained marginal costs `2 * ρ`; no repaired law
or original right-state cap is an input to the public theorem.

The degree-six factor `(1 + D^2) * (2 + D^4)` covers both branch losses.
Every extraction call is the actual scheduled matched-width Boolean
program. This finite statement combines the two advice orientations of
Chattopadhyay--Goyal--Li, Algorithm 1 and Lemma 6.8, Section 6.3:
<https://arxiv.org/pdf/1505.00107>. Advice-chain induction is a separate
composition obligation.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Either opposite-advice execution needs only original X/Y envelopes and joint whole-state
approximate uniformity, while retaining the actual full transcript and original left state. -/
theorem flipFlopOpposite_uniformState_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (μ ξ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    weightDist (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b)
      (uniformSecondWeight (flipFlopOppositeWeight n m L e w l r x x' y y' q q' b)) ≤
        2 * ρ + 10 * ε + (K : ℝ) * (1 + D ^ 2) * (2 + D ^ 4) * (∑ z, μ z) +
          2 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 3 + C ^ 5) * ∑ z, ξ z :=
  Internal.flipFlopOpposite_uniformState_dist_le n m L e guard w l r x x' y y' q q' b μ ξ
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap state

end Algebraic.Cutwidth.Extractor
