/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState.Internal

/-!
# Concrete look-ahead extraction after a nearly uniform refresh

The prefix of a uniform right state is uniform. Together with finite
distribution repair, this lets the actual matched-width look-ahead use
a nearly uniform right state without a pointwise entropy premise for it.
The original right state and both first look-ahead outputs are retained;
comparison with their actual marginal charges the refresh error twice.

This is the repair step between passes of the flip-flop argument of
Chattopadhyay--Goyal--Li, *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Lemma 6.8: <https://arxiv.org/pdf/1505.00107>.
The theorem instantiates both extractor calls with the actual scheduled
programs and gives an explicit finite bound. The complete opposite-advice
and iterated correlation-breaking guarantees are proved in `Opposite.UniformState`
and `Advice.Extraction` (`adviceCorrelationBreaker_dist_le`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual seed-width prefix of a uniform refresh-width state is uniform. -/
theorem flipFlopSeedPrefix_uniform (L : Nat) :
    mapWeight (flipFlopSeedPrefix L)
      (uniformWeight (Fin (matchedBlockOutputBits 64 L) → Bool)) =
        uniformWeight (Fin (matchedBlockSeedBits L) → Bool) :=
  Internal.flipFlopSeedPrefix_uniform L

/-- The actual look-ahead needs only joint approximate uniformity of its right state. -/
theorem flipFlopLookAhead_uniformState_dist_le (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (length : Nat.clog 2 (n + 1) ≤ L)
    (right_length : Nat.clog 2 (matchedBlockOutputBits 64 L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let M := Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))
    weightDist (flipFlopLookAheadWeight n L e w l r x x' q q')
      (uniformSecondWeight (flipFlopLookAheadWeight n L e w l r x x' q q')) ≤
        3 * ((2 : ℝ) ^ e)⁻¹ + 2 * ρ + (K : ℝ) * (1 + M) * (∑ z, μ z) +
          (K : ℝ) * M / Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) :=
  Internal.flipFlopLookAhead_uniformState_dist_le n L e length right_length room error
    w l r x x' q q' μ hw hl hr nonnegative cap state

end Algebraic.Cutwidth.Extractor
