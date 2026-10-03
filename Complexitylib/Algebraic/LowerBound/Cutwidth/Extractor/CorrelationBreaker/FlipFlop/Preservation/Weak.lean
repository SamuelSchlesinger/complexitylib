/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Weak.Internal

/-!
# One complete advice-bit step before advice differs

For arbitrary honest and tampered bits, the actual eight-call program
preserves approximate uniformity given both complete look-ahead histories
and the full original left state. The current tampered right state may
remain arbitrarily correlated with the honest state. Only the honest
state's joint discrepancy and original X/Y source envelopes are assumed.
The final tampered output is not observed in this law.

Both look-ahead passes and both refreshes use the actual matched-width
programs. The first refresh derives the second state's discrepancy; it is
not a supplied intermediate invariant. Exact first-history factors account
for the displayed average entropy and error losses.

This is the weak continuation needed before the first unequal advice bit
in Chattopadhyay--Goyal--Li, Algorithm 2 and Claim 6.11, printed pp.31--32:
<https://arxiv.org/pdf/1505.00107>. The conservative finite error estimate
is the deduction formalized here. The full advice-chain induction and its
final strong-extraction step remain separate obligations.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A complete actual step preserves weak uniformity for any pair of advice bits. -/
theorem flipFlopOutput_weak_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
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
    weightDist (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b')
      (uniformSecondWeight (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b')) ≤
        4 * ρ + 12 * ε + (K : ℝ) * (1 + D ^ 2) * (2 + D ^ 4) * (∑ z, μ z) +
          3 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 3 + C ^ 5) * ∑ z, ξ z :=
  Internal.flipFlopOutput_weak_dist_le n m L e guard w l r x x' y y' q q' b b' μ ξ
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap state

end Algebraic.Cutwidth.Extractor
