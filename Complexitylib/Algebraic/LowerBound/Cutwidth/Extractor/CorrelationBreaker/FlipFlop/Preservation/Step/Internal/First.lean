/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Refresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Exact factors after the first selected tampered refresh

The first common look-ahead transcript is followed by the actual selected
tampered right refresh. Both original states are retained, and the honest
refreshed coordinate is a right-only function of the resulting factors.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopHalf_factored (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A =>
      let honest := flipFlopLookAhead n L e (x p.1.1 p.2) (q p.1.1 p.1.2)
      let tampered := flipFlopLookAhead n L e (x' p.1.1 p.2) (q' p.1.1)
      let t := ((p.1.1, (q p.1.1 p.1.2, q' p.1.1)), (honest, tampered))
      (((t, flipFlopTamperedRefresh m L e y' b' t p.1.2), p.1.2), p.2))
      (factoredWeight w l r) =
      factoredWeight
        (observedTranscriptWeight (flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z))
          (flipFlopFirstRight L r q (fun z _ => q' z))
          (flipFlopTamperedRefresh m L e y' b'))
        (fun tu => flipFlopFirstLeft n L e l x x' tu.1)
        (observedTranscriptKernel (flipFlopFirstRight L r q (fun z _ => q' z))
          (flipFlopTamperedRefresh m L e y' b')) := by
  have first := lookAheadBase_factored (Mid := Fin (matchedBlockSeedBits L) → Bool)
    w l r x x' q (fun z _ => q' z) (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
    (fun z => (hl z).1) (fun z => (hr z).1)
  have hr₀ := flipFlopFirstRight_probability L r q (fun z _ => q' z) hr
  have observed := factoredWeight_observe_right
    (flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z))
    (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q (fun z _ => q' z))
    (flipFlopTamperedRefresh m L e y' b') (fun t => (hr₀ t).1)
  change mapWeight _ (factoredWeight w l r) =
    factoredWeight (flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z))
      (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q (fun z _ => q' z)) at first
  rw [← first, mapWeight_comp] at observed
  rw [← observed]
  apply congrArg (fun f : (Z × B) × A →
    ((FlipFlopFirstTranscript Z L × (Fin (matchedBlockOutputBits 64 L) → Bool)) × B) × A =>
      mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [flipFlopLookAhead, lookAheadBaseMessage]

theorem flipFlopHalf_retainedSeed (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p => (p.1.1, p.2)) (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b') =
      retainedSeedWeight
        (observedTranscriptWeight (flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z))
          (flipFlopFirstRight L r q (fun z _ => q' z))
          (flipFlopTamperedRefresh m L e y' b'))
        (observedTranscriptKernel (flipFlopFirstRight L r q (fun z _ => q' z))
          (flipFlopTamperedRefresh m L e y' b'))
        (fun tu => flipFlopHonestRefresh m L e y b tu.1) := by
  let T := FlipFlopFirstTranscript Z L × (Fin (matchedBlockOutputBits 64 L) → Bool)
  let w₁ := observedTranscriptWeight
    (flipFlopFirstWeight n L e w l r x x' q (fun z _ => q' z))
    (flipFlopFirstRight L r q (fun z _ => q' z)) (flipFlopTamperedRefresh m L e y' b')
  let l₁ : T → A → ℝ := fun tu => flipFlopFirstLeft n L e l x x' tu.1
  let r₁ := observedTranscriptKernel (flipFlopFirstRight L r q (fun z _ => q' z))
    (flipFlopTamperedRefresh m L e y' b')
  let qbar : T → B → Fin (matchedBlockOutputBits 64 L) → Bool :=
    fun tu => flipFlopHonestRefresh m L e y b tu.1
  have hl₁ : ∀ tu, IsProbabilityWeight (l₁ tu) :=
    fun tu => flipFlopFirstLeft_probability n L e l x x' hl tu.1
  change mapWeight _ (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b') =
    retainedSeedWeight w₁ r₁ qbar
  have factor := flipFlopHalf_factored n m L e w l r x x' y' q q' b' hl hr
  change mapWeight _ (factoredWeight w l r) = factoredWeight w₁ l₁ r₁ at factor
  rw [retainedSeedWeight_eq_factored w₁ l₁ r₁ qbar hl₁]
  rw [← factor, mapWeight_comp]
  unfold flipFlopHalfWeight
  rw [mapWeight_comp]
  apply congrArg (fun f : (Z × B) × A → T × (Fin (matchedBlockOutputBits 64 L) → Bool) =>
    mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [qbar, flipFlopHonestRefresh, flipFlopTamperedRefresh]

end Algebraic.Cutwidth.Extractor.Internal
