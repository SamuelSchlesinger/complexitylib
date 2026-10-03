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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Weak.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Weak.Internal.Identity
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Two actual refreshes before the first differing advice bit

The first selected refresh supplies the second state's average discrepancy.
The exact first-history factors preserve original source envelopes with
their stated observation costs. The second selected refresh uses the
opposite honest selection bit and the actual tampered refreshed state.
Its original-law image is the complete unobserved advice-bit output law.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

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
          3 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 3 + C ^ 5) * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let T := LookAheadBaseTranscript Z Q Mid
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let R : (Fin m → Bool) → Mid → Q := matchedBlockExtractor m 64 L e
  let w₁ := lookAheadBaseWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt
  let l₁ := lookAheadBaseLeft l x x' (flipFlopSeedPrefix L) W QExt
  let r₁ : T → B → ℝ := lookAheadBaseRight r q q'
  let qbar := flipFlopHonestRefresh m L e y b
  let qbar' := flipFlopTamperedRefresh m L e y' b'
  let μ₁ : T → ℝ := lookAheadBaseLeftEnvelope μ r q q'
  let ξ₁ : T → ℝ := lookAheadBaseRightEnvelope ξ l x x' (flipFlopSeedPrefix L) W QExt
  obtain ⟨hw₁, hl₁, hr₁⟩ := lookAheadBase_probability
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt hw hl hr
  have first_bound := flipFlopSelectedRefresh_dist_le n m L e guard w l r x x' y q q'
    μ ξ b hw hl hr left_nonnegative right_nonnegative left_cap right_cap state
  have projected := weightDist_uniformSecond_map_first_le
    (lookAheadSelectedRefreshWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt y R b)
    Prod.fst
  rw [lookAheadSelectedRefreshWeight_retainedSeed
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt y R b hl (fun z => (hr z).1)] at projected
  have refreshed := projected.trans first_bound
  have bound := flipFlopSelectedRefresh_dist_le n m L e guard w₁ l₁ r₁
    (fun t => x t.1.1) (fun t => x' t.1.1) (fun t => y t.1.1) qbar qbar' μ₁ ξ₁ (!b)
    hw₁ hl₁ hr₁
    (lookAheadBaseLeftEnvelope_nonnegative μ r q q' left_nonnegative (fun z => (hr z).1))
    (lookAheadBaseRightEnvelope_nonnegative ξ l x x' (flipFlopSeedPrefix L) W QExt
      right_nonnegative (fun z => (hl z).1))
    (lookAheadBase_left_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt μ
      hw.1 (fun z => (hl z).1) (fun z => (hr z).1) left_cap)
    (lookAheadBase_right_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt y ξ
      hw.1 (fun z => (hl z).1) (fun z => (hr z).1) right_cap) refreshed
  have actual : lookAheadSelectedRefreshWeight w₁ l₁ r₁ (fun t => x t.1.1)
      (fun t => x' t.1.1) qbar qbar' (flipFlopSeedPrefix L) W QExt
      (fun t => y t.1.1) R (!b) =
      flipFlopOutputWeight n m L e w l r x x' y y' q q' b b' :=
    flipFlopSelectedRefresh_second_eq_output n m L e w l r x x' y y' q q' b b' hl hr
  change weightDist
      (lookAheadSelectedRefreshWeight w₁ l₁ r₁ (fun t => x t.1.1) (fun t => x' t.1.1)
        qbar qbar' (flipFlopSeedPrefix L) W QExt (fun t => y t.1.1) R (!b)) _ ≤ _ at bound
  rw [actual] at bound
  have sumμ := lookAheadBaseLeftEnvelope_sum (Mid := Mid) μ r q q' (fun z => (hr z).2)
  have sumξ := lookAheadBaseRightEnvelope_sum ξ l x x' (flipFlopSeedPrefix L) W QExt
    (fun z => (hl z).2)
  change (∑ t, μ₁ t) = _ at sumμ
  change (∑ t, ξ₁ t) = _ at sumξ
  rw [sumμ, sumξ] at bound
  dsimp only
  convert bound using 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

end Algebraic.Cutwidth.Extractor.Internal
