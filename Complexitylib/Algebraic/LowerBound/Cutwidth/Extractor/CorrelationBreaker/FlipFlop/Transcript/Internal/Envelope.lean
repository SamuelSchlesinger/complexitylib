/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Mathlib.Tactic.Ring

/-!
# Original-source envelopes through the full pair of executions

Two right-pair messages and two four-output left messages give total
envelope factors `C^4` and `D^8` respectively. Opposite-side message
probabilities are retained in the row envelopes and sum to one. These are
identities for the actual normalized conditional kernels, not per-row
entropy assumptions.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopTranscriptLeftEnvelope_nonnegative (m L e : Nat) {Z B : Type*}
    [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (nonnegative : ∀ z, 0 ≤ μ z) (hr : ∀ z, IsProbabilityWeight (r z))
    (t : FlipFlopTranscript Z L) :
    0 ≤ flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t := by
  unfold flipFlopTranscriptLeftEnvelope
  exact lookAheadBaseLeftEnvelope_nonnegative _ _ _ _
    (lookAheadBaseLeftEnvelope_nonnegative μ r q q' nonnegative (fun z => (hr z).1))
    (fun t => (flipFlopFirstRight_probability L r q q' hr t).1) t

theorem flipFlopTranscriptRightEnvelope_nonnegative (n L e : Nat) {Z A : Type*}
    [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (nonnegative : ∀ z, 0 ≤ ν z) (hl : ∀ z, IsProbabilityWeight (l z))
    (t : FlipFlopTranscript Z L) :
    0 ≤ flipFlopTranscriptRightEnvelope n L e ν l x x' t := by
  unfold flipFlopTranscriptRightEnvelope
  exact lookAheadBaseRightEnvelope_nonnegative _ _ _ _ _ _ _
    (lookAheadBaseRightEnvelope_nonnegative ν l x x' (flipFlopSeedPrefix L)
      (matchedBlockExtractor n 24 L e)
      (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
      nonnegative (fun z => (hl z).1))
    (fun t => (flipFlopFirstLeft_probability n L e l x x' hl t).1) t

theorem flipFlopTranscript_left_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (t : FlipFlopTranscript Z L) (x₀ : Fin n → Bool) :
    flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (x t.1.1.1.1) (flipFlopTranscriptLeft n L e l x x' t) x₀ ≤
      flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := flipFlopFirst_probability n L e w l r x x' q q' hw hl hr
  have first := lookAheadBase_left_envelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q q' (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) μ hw.1
    (fun z => (hl z).1) (fun z => (hr z).1) cap
  unfold flipFlopTranscriptWeight flipFlopTranscriptLeft flipFlopTranscriptLeftEnvelope
  exact lookAheadBase_left_envelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (flipFlopFirstWeight n L e w l r x x' q q')
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
    (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) _ hw₁.1
    (fun t => (hl₁ t).1) (fun t => (hr₁ t).1) first t x₀

theorem flipFlopTranscript_right_envelope (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (ν : Z → ℝ) (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ν z)
    (t : FlipFlopTranscript Z L) (y₀ : Fin m → Bool) :
    flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b' t *
        mapWeight (y t.1.1.1.1) (flipFlopTranscriptRight m L e r y y' q q' b b' t) y₀ ≤
      flipFlopTranscriptRightEnvelope n L e ν l x x' t := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := flipFlopFirst_probability n L e w l r x x' q q' hw hl hr
  have first := lookAheadBase_right_envelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q q' (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) y ν hw.1
    (fun z => (hl z).1) (fun z => (hr z).1) cap
  unfold flipFlopTranscriptWeight flipFlopTranscriptRight flipFlopTranscriptRightEnvelope
  exact lookAheadBase_right_envelope (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (flipFlopFirstWeight n L e w l r x x' q q')
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
    (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) (fun t => y t.1.1)
    _ hw₁.1 (fun t => (hl₁ t).1) (fun t => (hr₁ t).1) first t y₀

theorem flipFlopTranscriptLeftEnvelope_sum (m L e : Nat) {Z B : Type*}
    [Fintype Z] [Fintype B] (μ : Z → ℝ) (r : Z → B → ℝ)
    (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    (∑ t, flipFlopTranscriptLeftEnvelope m L e μ r y y' q q' b b' t) =
      (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 8 * ∑ z, μ z := by
  unfold flipFlopTranscriptLeftEnvelope
  rw [lookAheadBaseLeftEnvelope_sum _ _ _ _
    (fun t => (flipFlopFirstRight_probability L r q q' hr t).2)]
  rw [lookAheadBaseLeftEnvelope_sum μ r q q' (fun z => (hr z).2)]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

theorem flipFlopTranscriptRightEnvelope_sum (n L e : Nat) {Z A : Type*}
    [Fintype Z] [Fintype A] (ν : Z → ℝ) (l : Z → A → ℝ)
    (x x' : Z → A → Fin n → Bool) (hl : ∀ z, IsProbabilityWeight (l z)) :
    (∑ t, flipFlopTranscriptRightEnvelope n L e ν l x x' t) =
      (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 4 * ∑ z, ν z := by
  unfold flipFlopTranscriptRightEnvelope
  erw [lookAheadBaseRightEnvelope_sum _ _ _ _ _ _ _
    (fun t => (flipFlopFirstLeft_probability n L e l x x' hl t).2)]
  erw [lookAheadBaseRightEnvelope_sum ν l x x' (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) (fun z => (hl z).2)]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

end Algebraic.Cutwidth.Extractor.Internal
