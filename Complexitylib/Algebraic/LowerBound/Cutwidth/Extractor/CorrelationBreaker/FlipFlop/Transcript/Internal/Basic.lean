/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript

/-!
# Exact factors for both actual look-ahead histories

Compose the two checked common-transcript factorizations. Their conditional
kernels retain the original left and right states at every row, including
null observations. Both final output maps recover the actual advice-bit
program, and opposite bits recover the existing opposite-advice transcript.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopFirstLeft_probability (n L e : Nat) {Z A : Type*} [Fintype A]
    (l : Z → A → ℝ) (x x' : Z → A → Fin n → Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (t : FlipFlopFirstTranscript Z L) :
    IsProbabilityWeight (flipFlopFirstLeft n L e l x x' t) :=
  observedTranscriptKernel_probability
    (fun zq : Z × ((Fin (matchedBlockOutputBits 64 L) → Bool) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool)) => l zq.1)
    (lookAheadBaseMessage (Mid := Fin (matchedBlockSeedBits L) → Bool) x x'
      (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
      (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e))
    (fun zq => hl zq.1) t

theorem flipFlopFirstRight_probability (L : Nat) {Z B : Type*} [Fintype B]
    (r : Z → B → ℝ) (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) (t : FlipFlopFirstTranscript Z L) :
    IsProbabilityWeight (flipFlopFirstRight L r q q' t) :=
  observedTranscriptKernel_probability r (fun z u => (q z u, q' z u)) hr t.1

theorem flipFlopFirst_probability (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopFirstWeight n L e w l r x x' q q') ∧
      (∀ t, IsProbabilityWeight (flipFlopFirstLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopFirstRight L r q q' t)) :=
  lookAheadBase_probability (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q q' (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) hw hl hr

theorem flipFlopTranscript_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b') ∧
      (∀ t, IsProbabilityWeight (flipFlopTranscriptLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopTranscriptRight m L e r y y' q q' b b' t)) := by
  obtain ⟨hw₁, hl₁, hr₁⟩ := flipFlopFirst_probability n L e w l r x x' q q' hw hl hr
  unfold flipFlopTranscriptWeight flipFlopTranscriptLeft flipFlopTranscriptRight
  exact lookAheadBase_probability (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (flipFlopFirstWeight n L e w l r x x' q q')
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
    (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) hw₁ hl₁ hr₁

theorem flipFlopTranscript_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((flipFlopTranscript n m L e x x' y y' q q' b b' p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopTranscriptLeft n L e l x x')
        (flipFlopTranscriptRight m L e r y y' q q' b b') := by
  have first := lookAheadBase_factored (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q q' (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
    (fun z => (hl z).1) (fun z => (hr z).1)
  have hl₁ : ∀ t, IsProbabilityWeight (flipFlopFirstLeft n L e l x x' t) :=
    flipFlopFirstLeft_probability n L e l x x' hl
  have hr₁ : ∀ t, IsProbabilityWeight (flipFlopFirstRight L r q q' t) :=
    flipFlopFirstRight_probability L r q q' hr
  have second := lookAheadBase_factored (Mid := Fin (matchedBlockSeedBits L) → Bool)
    (flipFlopFirstWeight n L e w l r x x' q q')
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
    (fun t => x t.1.1) (fun t => x' t.1.1)
    (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
    (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
    (fun t => (hl₁ t).1) (fun t => (hr₁ t).1)
  change mapWeight _ (factoredWeight w l r) =
    factoredWeight (flipFlopFirstWeight n L e w l r x x' q q')
      (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q') at first
  rw [← first, mapWeight_comp] at second
  unfold flipFlopTranscriptWeight flipFlopTranscriptLeft flipFlopTranscriptRight
  rw [← second]
  apply congrArg (fun f : (Z × B) × A → (FlipFlopTranscript Z L × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [flipFlopTranscript, flipFlopLookAhead, lookAheadBaseMessage]

theorem flipFlopHonestOutput_eq_step (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) :
    flipFlopHonestOutput m L e y b
      (flipFlopTranscript n m L e x x' y y' q q' b b' p) p.1.2 =
      flipFlopStep n m L e (x p.1.1 p.2) (y p.1.1 p.1.2) (q p.1.1 p.1.2) b := by
  dsimp only [flipFlopHonestOutput, flipFlopTranscript, flipFlopStep, flipFlopHonestRefresh]

theorem flipFlopTamperedOutput_eq_step (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b b' : Bool) (p : (Z × B) × A) :
    flipFlopTamperedOutput m L e y' b'
      (flipFlopTranscript n m L e x x' y y' q q' b b' p) p.1.2 =
      flipFlopStep n m L e (x' p.1.1 p.2) (y' p.1.1 p.1.2) (q' p.1.1 p.1.2) b' := by
  dsimp only [flipFlopTamperedOutput, flipFlopTranscript, flipFlopStep, flipFlopTamperedRefresh]

theorem flipFlopTranscript_opposite (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (p : (Z × B) × A) :
    (flipFlopTranscript n m L e x x' y y' q q' b (!b) p,
      flipFlopTamperedOutput m L e y' (!b)
        (flipFlopTranscript n m L e x x' y y' q q' b (!b) p) p.1.2) =
      flipFlopOppositeTranscript n m L e x x' y y' q q' b p := by
  cases b <;>
    simp only [flipFlopTranscript, flipFlopOppositeTranscript, flipFlopTamperedOutput,
      flipFlopStep, flipFlopHonestRefresh, flipFlopTamperedRefresh,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]

end Algebraic.Cutwidth.Extractor.Internal
