/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript.Output
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# The second selected refresh is the actual complete output

Expand the first-history factorization and compose its deterministic map
with the second selected refresh. The opposite honest selector is exactly
the final branch of the actual advice-bit program.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopSelectedRefresh_second_eq_output (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    lookAheadSelectedRefreshWeight (Mid := Fin (matchedBlockSeedBits L) → Bool)
        (flipFlopFirstWeight n L e w l r x x' q q')
        (flipFlopFirstLeft n L e l x x') (flipFlopFirstRight L r q q')
        (fun t => x t.1.1) (fun t => x' t.1.1)
        (flipFlopHonestRefresh m L e y b) (flipFlopTamperedRefresh m L e y' b')
        (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
        (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
        (fun t => y t.1.1) (matchedBlockExtractor m 64 L e) (!b) =
      flipFlopOutputWeight n m L e w l r x x' y y' q q' b b' := by
  rw [flipFlopOutputWeight_eq_factored n m L e w l r x x' y y' q q' b b' hl hr]
  erw [lookAheadSelectedRefreshWeight_eq_factored]
  · change mapWeight _
        (factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
          (flipFlopTranscriptLeft n L e l x x')
          (flipFlopTranscriptRight m L e r y y' q q' b b')) = _
    apply congrArg (fun f : (FlipFlopTranscript Z L × B) × A →
      (FlipFlopTranscript Z L × A) × (Fin (matchedBlockOutputBits 64 L) → Bool) =>
        mapWeight f
          (factoredWeight (flipFlopTranscriptWeight n m L e w l r x x' y y' q q' b b')
            (flipFlopTranscriptLeft n L e l x x')
            (flipFlopTranscriptRight m L e r y y' q q' b b')))
    funext p
    cases b <;> rfl
  · exact fun t => (flipFlopFirstLeft_probability n L e l x x' hl t).1
  · exact fun t => (flipFlopFirstRight_probability L r q q' hr t).1

end Algebraic.Cutwidth.Extractor.Internal
