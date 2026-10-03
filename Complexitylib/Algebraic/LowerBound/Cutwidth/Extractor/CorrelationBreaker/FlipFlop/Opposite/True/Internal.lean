/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.True.Internal.Repair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The honest-true, tampered-false flip-flop proof

The first tampered refresh fixes the tampered intermediate right coordinate.
The honest coordinate is repaired while retaining the original right state.
Its second left output is then an arbitrary left-only tampered seed for the
terminal refresh theorem. Every retained variable is computed from the
actual original states, and both returns from the repair are charged.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

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
          (J : ℝ) * N ^ 5 * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let T := LookAheadBaseTranscript Z Q Mid
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let R : (Fin m → Bool) → Mid → Q := matchedBlockExtractor m 64 L e
  let w₀ := lookAheadBaseWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt
  let l₀ := lookAheadBaseLeft l x x' (flipFlopSeedPrefix L) W QExt
  let r₀ : T → B → ℝ := lookAheadBaseRight r q q'
  let qbar' : T → B → Q := fun t b => R (y' t.1.1 b) t.2.2.1
  let w₁ := observedTranscriptWeight w₀ r₀ qbar'
  let l₁ : T × Q → A → ℝ := fun tu => l₀ tu.1
  let r₁ := observedTranscriptKernel r₀ qbar'
  let qbar : T × Q → B → Q := fun tu b => R (y tu.1.1.1 b) tu.1.2.1.2
  let leak : T × Q → A → Mid := fun tu a =>
    (flipFlopLookAhead n L e (x' tu.1.1.1 a) tu.2).2
  let μ₀ : T → ℝ := lookAheadBaseLeftEnvelope μ r q q'
  let ξ₀ : T → ℝ := lookAheadBaseRightEnvelope ξ l x x' (flipFlopSeedPrefix L) W QExt
  let μ₁ := observedTranscriptWeight μ₀ r₀ qbar'
  let ξ₁ : T × Q → ℝ := fun tu => ξ₀ tu.1
  have room : 64 ≤ L := by have := guard.1; lia
  have error : e + 24 + 2 ≤ L := by have := guard.1; lia
  have first : WeightedStrongSeededExtractor W (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 n L e guard.2.1 room error
  have second : WeightedStrongSeededExtractor QExt (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 _ L e guard.2.2.2 room error
  have refresh : WeightedStrongSeededExtractor R (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth64 m L e guard.2.2.1 room (by have := guard.1; lia)
  obtain ⟨hw₀, hl₀, hr₀⟩ := lookAheadBase_probability
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt hw hl hr
  have hw₁ := observedTranscriptWeight_probability w₀ r₀ qbar' hw₀ hr₀
  have hl₁ : ∀ tu, IsProbabilityWeight (l₁ tu) := fun tu => hl₀ tu.1
  have hr₁ := observedTranscriptKernel_probability r₀ qbar' hr₀
  have first_bound := first.lookAhead_tampered_refresh_dist_le (by positivity)
    second (by positivity) refresh (by positivity) w l r x x' q q'
    (flipFlopSeedPrefix L) y y' μ ν ξ hw hl hr left_nonnegative state_nonnegative
    right_nonnegative left_cap state_cap right_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (lookAheadTamperedRefreshWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt y y' R)
    Prod.fst
  have marginal : mapWeight (fun p => (p.1.1, p.2))
      (lookAheadTamperedRefreshWeight w l r x x' q q'
        (flipFlopSeedPrefix L) W QExt y y' R) = retainedSeedWeight w₁ r₁ qbar := by
    rw [lookAheadTamperedRefreshWeight_eq_factored
      w l r x x' q q' (flipFlopSeedPrefix L) W QExt y y' R (fun z => (hl z).1) hr,
      mapWeight_comp, retainedSeedWeight_eq_factored w₁ l₁ r₁ qbar hl₁]
  rw [marginal] at projected
  have refreshed := projected.trans first_bound
  have hμ₀ := lookAheadBaseLeftEnvelope_nonnegative (Mid := Mid) μ r q q' left_nonnegative
    (fun z => (hr z).1)
  have hξ₀ := lookAheadBaseRightEnvelope_nonnegative ξ l x x' (flipFlopSeedPrefix L) W QExt
    right_nonnegative (fun z => (hl z).1)
  have capμ₀ := lookAheadBase_left_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt μ
    hw.1 (fun z => (hl z).1) (fun z => (hr z).1) left_cap
  have capξ₀ := lookAheadBase_right_envelope w l r x x' q q' (flipFlopSeedPrefix L) W QExt y ξ
    hw.1 (fun z => (hl z).1) (fun z => (hr z).1) right_cap
  have bound := fixedTampering_after_repair first (by positivity) refresh (by positivity)
    w₁ l₁ r₁ (fun tu => x tu.1.1.1) qbar (fun tu => y tu.1.1.1)
    (fun tu => y' tu.1.1.1) leak (flipFlopSeedPrefix L) μ₁ ξ₁ hw₁ hl₁ hr₁
    (observedTranscriptWeight_nonnegative μ₀ r₀ qbar' hμ₀ (fun t => (hr₀ t).1))
    (fun tu => hξ₀ tu.1)
    (observedTranscript_right_envelope w₀ l₀ r₀ (fun t => x t.1.1) qbar' μ₀
      (fun t => (hr₀ t).1) capμ₀)
    (observedTranscript_left_envelope w₀ r₀ (fun t => y t.1.1) qbar' ξ₀
      hw₀.1 (fun t => (hr₀ t).1) capξ₀)
    (flipFlopSeedPrefix_uniform L) refreshed
  let project : FixedTamperingTranscript (T × Q) Q Mid Q × A →
      FlipFlopOppositeTranscript Z L × A := fun p =>
    let tu := p.1.1.1.1
    let honest := flipFlopLookAhead n L e (x tu.1.1.1 p.2) p.1.1.2.1
    let tampered := flipFlopLookAhead n L e (x' tu.1.1.1 p.2) tu.2
    (((((tu.1, (p.1.1.2.1, tu.2)), (honest, tampered)), p.1.1.2.2), p.2))
  have final_projection := weightDist_uniformSecond_map_first_le
    (fixedTamperingRefreshWeight w₁ l₁ r₁ (fun tu => x tu.1.1.1) qbar
      (fun tu => y tu.1.1.1) (fun tu => y' tu.1.1.1) leak (flipFlopSeedPrefix L) W R)
    project
  have factor := lookAheadTamperedRefresh_factored
    w l r x x' q q' (flipFlopSeedPrefix L) W QExt y' R (fun z => (hl z).1) hr
  have actual : mapWeight (fun p => (project p.1, p.2))
      (fixedTamperingRefreshWeight w₁ l₁ r₁ (fun tu => x tu.1.1.1) qbar
        (fun tu => y tu.1.1.1) (fun tu => y' tu.1.1.1) leak (flipFlopSeedPrefix L) W R) =
      flipFlopOppositeWeight n m L e w l r x x' y y' q q' true := by
    unfold fixedTamperingRefreshWeight
    rw [mapWeight_comp]
    change mapWeight _ (factoredWeight
      (observedTranscriptWeight
        (lookAheadBaseWeight w l r x x' q q' (flipFlopSeedPrefix L) W QExt)
        (lookAheadBaseRight r q q') (fun t b => R (y' t.1.1 b) t.2.2.1))
      (fun tu => lookAheadBaseLeft l x x' (flipFlopSeedPrefix L) W QExt tu.1)
      (observedTranscriptKernel (lookAheadBaseRight r q q')
        (fun t b => R (y' t.1.1 b) t.2.2.1))) = _
    rw [← factor, mapWeight_comp]
    unfold flipFlopOppositeWeight
    apply congrArg (fun f : (Z × B) × A → (FlipFlopOppositeTranscript Z L × A) × Q =>
      mapWeight f (factoredWeight w l r))
    funext p
    simp only [project, fixedTamperingTranscriptValue, fixedTamperingRightMessage,
      fixedTamperingHonestMessage, flipFlopOppositeTranscript, flipFlopStep, flipFlopLookAhead,
      lookAheadBaseMessage, qbar, leak, W, QExt, R, Bool.not_true]
    dsimp only [matchedBlockOutputBits, matchedBlockSeedBits]
    rfl
  rw [actual] at final_projection
  have result := final_projection.trans bound
  have sumμ₀ := lookAheadBaseLeftEnvelope_sum (Mid := Mid) μ r q q' (fun z => (hr z).2)
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
