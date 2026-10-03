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
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Step.Internal.First
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Composing both selected refresh halves

After the first half, the actual tampered refreshed input is fixed by the
new transcript. The second half reads the same original sources and uses
the complementary selection bits. A deterministic projection removes the
duplicated tampered intermediate coordinate from the final retained history.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

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
        3 * (K : ℝ) * D ^ 2 / C + (J : ℝ) * (2 * C ^ 2 + C ^ 5) * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let T := FlipFlopFirstTranscript Z L
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let w₀ := flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z)
  let l₀ := flipFlopFirstLeft n L e l x x'
  let r₀ := flipFlopFirstRight L r q (fun z _ => q' z)
  let qbar' := flipFlopTamperedRefresh m L e y' b'
  let w₁ := observedTranscriptWeight w₀ r₀ qbar'
  let l₁ : T × Q → A → ℝ := fun tu => l₀ tu.1
  let r₁ := observedTranscriptKernel r₀ qbar'
  let qbar : T × Q → B → Q := fun tu => flipFlopHonestRefresh m L e y b tu.1
  let μ₀ : T → ℝ := lookAheadBaseLeftEnvelope μ r q (fun z _ => q' z)
  let ξ₀ : T → ℝ := lookAheadBaseRightEnvelope ξ l x x' (flipFlopSeedPrefix L) W QExt
  let μ₁ := observedTranscriptWeight μ₀ r₀ qbar'
  let ξ₁ : T × Q → ℝ := fun tu => ξ₀ tu.1
  obtain ⟨hw₀, hl₀, hr₀⟩ := flipFlopFirst_probability
    n L e w l r x x' q (fun z _ => q' z) hw hl hr
  have hw₁ := observedTranscriptWeight_probability w₀ r₀ qbar' hw₀ hr₀
  have hl₁ : ∀ tu, IsProbabilityWeight (l₁ tu) := fun tu => hl₀ tu.1
  have hr₁ := observedTranscriptKernel_probability r₀ qbar' hr₀
  have first_bound := flipFlopHalf_dist_le n m L e guard w l r x x' y y' q q' b b' μ ξ
    hw hl hr left_nonnegative right_nonnegative left_cap right_cap state
  have projected := weightDist_uniformSecond_map_first_le
    (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b') Prod.fst
  rw [flipFlopHalf_retainedSeed n m L e w l r x x' y y' q q' b b' hl hr] at projected
  have refreshed := projected.trans first_bound
  have hμ₀ := lookAheadBaseLeftEnvelope_nonnegative (Mid := Mid) μ r q
    (fun z _ => q' z) left_nonnegative (fun z => (hr z).1)
  have hξ₀ := lookAheadBaseRightEnvelope_nonnegative ξ l x x' (flipFlopSeedPrefix L) W QExt
    right_nonnegative (fun z => (hl z).1)
  have capμ₀ := lookAheadBase_left_envelope w l r x x' q (fun z _ => q' z)
    (flipFlopSeedPrefix L) W QExt μ hw.1 (fun z => (hl z).1) (fun z => (hr z).1) left_cap
  have capξ₀ := lookAheadBase_right_envelope w l r x x' q (fun z _ => q' z)
    (flipFlopSeedPrefix L) W QExt y ξ hw.1 (fun z => (hl z).1) (fun z => (hr z).1) right_cap
  have bound := flipFlopHalf_dist_le n m L e guard w₁ l₁ r₁
    (fun tu => x tu.1.1.1) (fun tu => x' tu.1.1.1)
    (fun tu => y tu.1.1.1) (fun tu => y' tu.1.1.1)
    qbar Prod.snd (!b) (!b') μ₁ ξ₁ hw₁ hl₁ hr₁
    (observedTranscriptWeight_nonnegative μ₀ r₀ qbar' hμ₀ (fun t => (hr₀ t).1))
    (fun tu => hξ₀ tu.1)
    (observedTranscript_right_envelope w₀ l₀ r₀ (fun t => x t.1.1) qbar' μ₀
      (fun t => (hr₀ t).1) capμ₀)
    (observedTranscript_left_envelope w₀ r₀ (fun t => y t.1.1) qbar' ξ₀
      hw₀.1 (fun t => (hr₀ t).1) capξ₀) refreshed
  let project : (LookAheadBaseTranscript (T × Q) Q Mid × Q) × A →
      FlipFlopObservedTranscript Z L × A := fun p =>
    ((((p.1.1.1.1.1, p.1.1.1.2), p.1.1.2), p.1.2), p.2)
  have final_projection := weightDist_uniformSecond_map_first_le
    (flipFlopHalfWeight n m L e w₁ l₁ r₁
      (fun tu => x tu.1.1.1) (fun tu => x' tu.1.1.1)
      (fun tu => y tu.1.1.1) (fun tu => y' tu.1.1.1)
      qbar Prod.snd (!b) (!b')) project
  have factor := flipFlopHalf_factored n m L e w l r x x' y' q q' b' hl hr
  change mapWeight _ (factoredWeight w l r) = factoredWeight w₁ l₁ r₁ at factor
  have actual : mapWeight (fun p => (project p.1, p.2))
      (flipFlopHalfWeight n m L e w₁ l₁ r₁
        (fun tu => x tu.1.1.1) (fun tu => x' tu.1.1.1)
        (fun tu => y tu.1.1.1) (fun tu => y' tu.1.1.1)
        qbar Prod.snd (!b) (!b')) =
      flipFlopObservedOutputWeight n m L e w l r x x' y y' q (fun z _ => q' z) b b' := by
    unfold flipFlopHalfWeight
    rw [mapWeight_comp, ← factor, mapWeight_comp]
    unfold flipFlopObservedOutputWeight
    apply congrArg (fun f : (Z × B) × A → (FlipFlopObservedTranscript Z L × A) × Q =>
      mapWeight f (factoredWeight w l r))
    funext p
    cases b <;> cases b' <;>
      simp only [project, qbar, flipFlopObservedTranscript, flipFlopTranscript,
        flipFlopStep, flipFlopHonestRefresh, flipFlopTamperedRefresh,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
  rw [actual] at final_projection
  have result := final_projection.trans bound
  have sumμ₀ := lookAheadBaseLeftEnvelope_sum (Mid := Mid) μ r (q) (fun z _ => q' z)
    (fun z => (hr z).2)
  have sumξ₀ := lookAheadBaseRightEnvelope_sum ξ l x x' (flipFlopSeedPrefix L) W QExt
    (fun z => (hl z).2)
  have sumμ₁ := observedTranscript_right_envelope_sum μ₀ r₀ qbar' (fun t => (hr₀ t).2)
  have sumξ₁ := observedTranscript_left_envelope_sum (U := Q) ξ₀
  change (∑ t, μ₀ t) = _ at sumμ₀
  change (∑ t, ξ₀ t) = _ at sumξ₀
  change (∑ tu, μ₁ tu) = _ at sumμ₁
  change (∑ tu, ξ₁ tu) = _ at sumξ₁
  rw [sumμ₁, sumξ₁, sumμ₀, sumξ₀] at result
  dsimp only
  convert result using 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

end Algebraic.Cutwidth.Extractor.Internal
