/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead

/-!
# Instantiating two-round extraction with the actual matched-width programs

The actual look-ahead pushforward agrees definitionally with the generic
three-call law. Both required strong extractors are the proved scheduled
programs, with their full padded Boolean seeds. Cardinalities stay symbolic;
no finite alphabet is enumerated to justify the statistical bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopLookAheadWeight_eq (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool) :
    flipFlopLookAheadWeight n L e w l r x x' q q' =
      lookAheadExtractionWeight w l r x x' q q' (flipFlopSeedPrefix L)
        (matchedBlockExtractor n 24 L e)
        (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) := by
  unfold flipFlopLookAheadWeight lookAheadExtractionWeight
  apply congrArg (fun f : (Z × B) × A →
    ((Z × B) × ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))) × (Fin (matchedBlockSeedBits L) → Bool) =>
        mapWeight f (factoredWeight w l r))
  funext p
  dsimp only [flipFlopLookAhead]
  rfl

theorem flipFlopLookAheadWeight_probability (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (flipFlopLookAheadWeight n L e w l r x x' q q') := by
  rw [flipFlopLookAheadWeight_eq]
  exact lookAheadExtractionWeight_probability w l r x x' q q' (flipFlopSeedPrefix L)
    (matchedBlockExtractor n 24 L e)
    (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e) hw hl hr

theorem flipFlopLookAhead_dist_le (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (length : Nat.clog 2 (n + 1) ≤ L)
    (right_length : Nat.clog 2 (matchedBlockOutputBits 64 L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ν : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r (fun z b => flipFlopSeedPrefix L (q z b)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z b => flipFlopSeedPrefix L (q z b)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let M := Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))
    weightDist (flipFlopLookAheadWeight n L e w l r x x' q q')
      (uniformSecondWeight (flipFlopLookAheadWeight n L e w l r x x' q q')) ≤
        3 * ((2 : ℝ) ^ e)⁻¹ + δ + (K : ℝ) * (1 + M) * (∑ z, μ z) +
          (K : ℝ) * M * ∑ z, ν z := by
  dsimp only
  rw [flipFlopLookAheadWeight_eq]
  have first := matchedBlockExtractor_depth24 n L e length room error
  have second := matchedBlockExtractor_depth24 (matchedBlockOutputBits 64 L) L e
    right_length room error
  have bound := first.lookAhead_dist_le (by positivity) second (by positivity)
    w l r x x' q q' (flipFlopSeedPrefix L) μ ν hw hl hr
    left_nonnegative right_nonnegative left_cap right_cap seed
  have cards : Fintype.card ((Fin (matchedBlockOutputBits 24 L) → Bool) ×
      (Fin (matchedBlockOutputBits 24 L) → Bool)) =
      Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
        (Fin (matchedBlockSeedBits L) → Bool)) := rfl
  rw [cards] at bound
  have errors : 2 * ((2 : ℝ) ^ e)⁻¹ + ((2 : ℝ) ^ e)⁻¹ =
      3 * ((2 : ℝ) ^ e)⁻¹ := by ring
  rw [errors] at bound
  exact bound

end Algebraic.Cutwidth.Extractor.Internal
