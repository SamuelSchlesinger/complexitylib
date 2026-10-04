/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Internal

/-!
# Preserving uniformity through a selected flip-flop half-step

The old transcript fixes the tampered right look-ahead input. For arbitrary
honest and tampered selection bits, the selected honest refresh is nearly
uniform given both complete look-ahead pairs, both right inputs, the actual
selected tampered refresh, and the full original left state. Every call uses
the scheduled matched-width Boolean extractor, and both refreshes reread the
original right source.

Only normalized original factors, the original honest X/Y joint envelopes,
and whole honest-right-input discrepancy are assumed. A correlated repair
makes that coordinate uniform given the old transcript while preserving the
original right source. It need not be independent of the retained right
state. Returning to the actual retained marginal costs `2 * ρ`. The
`K * D^2 / C` term comes from the repaired coordinate's exact uniform cap.
All four pairs of selection bits share the displayed conservative bound.

This finite half-step is a component of preservation after advice strings
have differed in Chattopadhyay--Goyal--Li, Algorithm 1 and Lemma 6.8,
Section 6.3: <https://arxiv.org/pdf/1505.00107>. `Preservation.Step` composes the
two halves, and `Advice.Extraction` proves the complete advice-chain guarantee
(`adviceCorrelationBreaker_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual selected half-step is normalized for all parameters and selection bits. -/
theorem flipFlopHalfWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b') :=
  Internal.flipFlopHalfWeight_probability n m L e w l r x x' y y' q q' b b' hw hl hr

/-- With the tampered input fixed by the old transcript, either selected refresh preserves
uniformity against the full actual transcript and original left state. -/
theorem flipFlopHalf_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (μ ξ : Z → ℝ) {ρ : ℝ}
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
    weightDist (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')
      (uniformSecondWeight (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')) ≤
        4 * ε + 2 * ρ + (K : ℝ) * D * (1 + D ^ 2) * (∑ z, μ z) +
          (K : ℝ) * D ^ 2 / C + (J : ℝ) * C ^ 2 * ∑ z, ξ z :=
  Internal.flipFlopHalf_dist_le n m L e guard w l r x x' y y' q q' b b' μ ξ
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap state

end Algebraic.Cutwidth.Extractor
