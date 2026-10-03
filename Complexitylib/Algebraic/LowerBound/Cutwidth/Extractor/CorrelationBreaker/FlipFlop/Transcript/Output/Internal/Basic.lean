/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Opposite.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal

/-!
# Exact final-output laws and observed original-source kernels

Append one deterministic right observation to the checked common transcript.
The resulting factorization retains both original sources, even when a
message has zero probability. Projecting the left state identifies the
honest output with its retained seed law over either transcript.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopTranscriptRight_probability (m L e : Nat) {Z B : Type*} [Fintype B]
    (r : Z → B → ℝ) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hr : ∀ z, IsProbabilityWeight (r z)) (t : FlipFlopTranscript Z L) :
    IsProbabilityWeight (flipFlopTranscriptRight m L e r y y' q q' b b' t) :=
  observedTranscriptKernel_probability (flipFlopFirstRight L r q q')
    (fun u a => (flipFlopHonestRefresh m L e y b u a,
      flipFlopTamperedRefresh m L e y' b' u a))
    (flipFlopFirstRight_probability L r q q' hr) t.1

theorem flipFlopOutputWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b') :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem flipFlopObservedOutputWeight_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b') :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem flipFlopObserved_probability (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b') ∧
      (∀ t, IsProbabilityWeight (flipFlopObservedLeft n L e l x x' t)) ∧
      (∀ t, IsProbabilityWeight (flipFlopObservedRight m L e r y y' q q' b b' t)) := by
  obtain ⟨hwt, hlt, hrt⟩ := flipFlopTranscript_probability
    n m L e w l r x x' y y' q q' b b' hw hl hr
  exact ⟨observedTranscriptWeight_probability _ _ _ hwt hrt,
    (fun t => hlt t.1), observedTranscriptKernel_probability _ _ hrt⟩

theorem flipFlopObserved_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      ((flipFlopObservedTranscript n m L e x x' y y' q q' b b' p, p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopObservedLeft n L e l x x')
        (flipFlopObservedRight m L e r y y' q q' b b') := by
  have hrt := flipFlopTranscriptRight_probability m L e r y y' q q' b b' hr
  have obs := factoredWeight_observe_right
    (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopTranscriptLeft n L e l x x')
    (flipFlopTranscriptRight m L e r y y' q q' b b')
    (flipFlopTamperedOutput m L e y' b') (fun t => (hrt t).1)
  rw [← flipFlopTranscript_factored n m L e w l r x x' y y' q q' b b' hl hr,
    mapWeight_comp] at obs
  unfold flipFlopObservedWeight flipFlopObservedLeft flipFlopObservedRight
  rw [← obs]
  apply congrArg (fun f : (Z × B) × A → (FlipFlopObservedTranscript Z L × B) × A =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply, flipFlopObservedTranscript]
  rw [flipFlopTamperedOutput_eq_step]

theorem flipFlopOutputWeight_eq_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    flipFlopOutputWeight n m L e w l r x x' y y' q q' b b' =
      mapWeight (fun p : (FlipFlopTranscript Z L × B) × A =>
        ((p.1.1, p.2), flipFlopHonestOutput m L e y b p.1.1 p.1.2))
        (factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
          (flipFlopTranscriptLeft n L e l x x')
          (flipFlopTranscriptRight m L e r y y' q q' b b')) := by
  unfold flipFlopOutputWeight
  rw [← flipFlopTranscript_factored n m L e w l r x x' y y' q q' b b' hl hr,
    mapWeight_comp]
  apply congrArg (fun f : (Z × B) × A →
    (FlipFlopTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) =>
      mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply]
  rw [flipFlopHonestOutput_eq_step]

theorem flipFlopObservedOutputWeight_eq_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b' =
      mapWeight (fun p : (FlipFlopObservedTranscript Z L × B) × A =>
        ((p.1.1, p.2), flipFlopHonestOutput m L e y b p.1.1.1 p.1.2))
        (factoredWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
          (flipFlopObservedLeft n L e l x x')
          (flipFlopObservedRight m L e r y y' q q' b b')) := by
  unfold flipFlopObservedOutputWeight
  rw [← flipFlopObserved_factored n m L e w l r x x' y y' q q' b b' hl hr,
    mapWeight_comp]
  apply congrArg (fun f : (Z × B) × A →
    (FlipFlopObservedTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) =>
      mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [Function.comp_apply, flipFlopObservedTranscript]
  rw [flipFlopHonestOutput_eq_step]

theorem flipFlopOutputWeight_retainedSeed (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (FlipFlopTranscript Z L × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) => (p.1.1, p.2))
      (flipFlopOutputWeight n m L e w l r x x' y y' q q' b b') =
      retainedSeedWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopTranscriptRight m L e r y y' q q' b b')
        (flipFlopHonestOutput m L e y b) := by
  rw [flipFlopOutputWeight_eq_factored n m L e w l r x x' y y' q q' b b' hl hr,
    mapWeight_comp]
  dsimp only [Function.comp_apply]
  exact (retainedSeedWeight_eq_factored
    (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopTranscriptLeft n L e l x x')
    (flipFlopTranscriptRight m L e r y y' q q' b b')
    (flipFlopHonestOutput m L e y b)
    (flipFlopTranscript_probability n m L e w l r x x' y y' q q' b b' hw hl hr).2.1).symm

theorem flipFlopObservedOutputWeight_retainedSeed (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (FlipFlopObservedTranscript Z L × A) ×
      (Fin (matchedBlockOutputBits 64 L) → Bool) => (p.1.1, p.2))
      (flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b b') =
      retainedSeedWeight (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
        (flipFlopObservedRight m L e r y y' q q' b b')
        (fun t => flipFlopHonestOutput m L e y b t.1) := by
  rw [flipFlopObservedOutputWeight_eq_factored n m L e w l r x x' y y' q q' b b' hl hr,
    mapWeight_comp]
  dsimp only [Function.comp_apply]
  exact (retainedSeedWeight_eq_factored
    (flipFlopObservedWeight n m L e w l r x x' y y' q q' b b')
    (flipFlopObservedLeft n L e l x x')
    (flipFlopObservedRight m L e r y y' q q' b b')
    (fun t => flipFlopHonestOutput m L e y b t.1)
    (flipFlopObserved_probability n m L e w l r x x' y y' q q' b b' hw hl hr).2.1).symm

theorem flipFlopObservedTranscript_opposite (n m L e : Nat) {Z A B : Type*}
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (b : Bool) (p : (Z × B) × A) :
    flipFlopObservedTranscript n m L e x x' y y' q q' b (!b) p =
      flipFlopOppositeTranscript n m L e x x' y y' q q' b p := by
  unfold flipFlopObservedTranscript
  rw [← flipFlopTamperedOutput_eq_step n m L e x x' y y' q q' b (!b) p]
  exact flipFlopTranscript_opposite n m L e x x' y y' q q' b p

theorem flipFlopObservedOutputWeight_opposite (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool)
    : flipFlopObservedOutputWeight n m L e w l r x x' y y' q q' b (!b) =
      flipFlopOppositeWeight n m L e w l r x x' y y' q q' b := by
  unfold flipFlopObservedOutputWeight flipFlopOppositeWeight
  apply congrArg (fun f : (Z × B) × A →
    (FlipFlopObservedTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) =>
      mapWeight f (factoredWeight w l r))
  funext p
  rw [flipFlopObservedTranscript_opposite]

end Algebraic.Cutwidth.Extractor.Internal
