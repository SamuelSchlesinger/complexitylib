/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead.Internal

/-!
# Two-round extraction by the actual flip-flop look-ahead

The concrete three-call program has a nearly uniform second output while
retaining the transcript, full right state, and both first outputs. The
sources factor given the transcript; honest and tampered inputs on either
side may be arbitrarily correlated. The hypotheses are average joint
source envelopes and the original seed-prefix discrepancy. No supplied
extractor or intermediate-seed guarantee is assumed.

The proof instantiates the finite two-round argument of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their
Many Tampered Extensions*, Lemma 6.5 and Claim 6.6, printed pp.25--28,
<https://arxiv.org/pdf/1505.00107>, with the actual matched-width scheduled
programs. It does not yet prove the two-refresh flip-flop invariant or the
longer advice-bit iteration. The conservative matched parameters are
credited separately in `Scheduled.Matched`.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual program law is precisely the three-call law with the proved matched extractors. -/
theorem flipFlopLookAheadWeight_eq (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) :
    flipFlopLookAheadWeight n L e w l r x x' q q' =
      lookAheadExtractionWeight w l r x x' q q' (flipFlopSeedPrefix L)
        (matchedBlockExtractor n 24 L e)
        (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) :=
  Internal.flipFlopLookAheadWeight_eq n L e w l r x x' q q'

/-- Every normalized conditionally factored source has a normalized actual output law. -/
theorem flipFlopLookAheadWeight_probability (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopLookAheadWeight n L e w l r x x' q q') :=
  Internal.flipFlopLookAheadWeight_probability n L e w l r x x' q q' hw hl hr

/-- Actual look-ahead extraction retains the right state and both first outputs. -/
theorem flipFlopLookAhead_dist_le (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (length : Nat.clog 2 (n + 1) ≤ L)
    (right_length : Nat.clog 2 (matchedBlockOutputBits 64 L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ν : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => flipFlopSeedPrefix L (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z b => flipFlopSeedPrefix L (q z b)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let M := Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))
    weightDist (flipFlopLookAheadWeight n L e w l r x x' q q')
      (uniformSecondWeight (flipFlopLookAheadWeight n L e w l r x x' q q')) ≤
        3 * ((2 : ℝ) ^ e)⁻¹ + δ + (K : ℝ) * (1 + M) * (∑ z, μ z) +
          (K : ℝ) * M * ∑ z, ν z :=
  Internal.flipFlopLookAhead_dist_le n L e length right_length room error
    w l r x x' q q' μ ν hw hl hr left_nonnegative right_nonnegative left_cap right_cap seed

end Algebraic.Cutwidth.Extractor
