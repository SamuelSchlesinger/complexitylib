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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Step.Internal

/-!
# Preservation through a complete actual advice-bit step

When the old transcript fixes the incoming tampered state, an entire actual
flip-flop execution preserves near-uniformity for arbitrary honest and
tampered advice bits. The result retains the complete two-pass transcript,
the actual tampered final output, and the original full left state. Every
refresh rereads the original right source.

The two checked half-steps use complementary selection bits. Observing the
first tampered refresh leaves exact normalized factors, multiplies the left
envelope total by `D^4`, and multiplies the right total by `C^3`. The second
half therefore applies to a derived refreshed-state guarantee, with no new
source or security assumption. The fourfold incoming-error coefficient
accounts for both correlated repairs and their actual retained marginals.

This is the finite preservation step after advice strings first differ in
Chattopadhyay--Goyal--Li Algorithm 2 and Lemma 6.9, Section 6.3:
<https://arxiv.org/pdf/1505.00107>. It uses this library's matched-width
programs and conservative finite error accounting. The complete induction
through arbitrary advice words is a separate theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A full step preserves uniformity against the actual observed transcript when the old
transcript fixes the tampered incoming state, for arbitrary current selection bits. -/
theorem flipFlopStep_preservation_dist_le (n m L e : Nat) {Z A B : Type*}
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
    weightDist
      (flipFlopObservedOutputWeight n m L e w l r x x' y y' q (fun z _ => q' z) b b')
      (uniformSecondWeight
        (flipFlopObservedOutputWeight n m L e w l r x x' y y' q (fun z _ => q' z) b b')) ≤
      4 * ρ + 12 * ε + (K : ℝ) * D * (1 + D ^ 2) * (2 + D ^ 4) * (∑ z, μ z) +
        3 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 2 + C ^ 5) * ∑ z, ξ z :=
  Internal.flipFlopStep_preservation_dist_le n m L e guard w l r x x' y y' q q' b b' μ ξ
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap state

end Algebraic.Cutwidth.Extractor
