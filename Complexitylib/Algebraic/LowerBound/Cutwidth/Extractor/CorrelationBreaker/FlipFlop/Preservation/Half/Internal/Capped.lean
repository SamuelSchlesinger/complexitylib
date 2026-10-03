/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Preservation.Half.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Selected half-step refreshes with joint source caps

When the old transcript fixes the tampered right input, either selected
tampered look-ahead output is a left-only seed. The two terminal refresh
theorems therefore apply, and the complete look-ahead pairs are recovered
deterministically from the retained right input and original left state.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopHalf_dist_le_of_caps (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (q : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (q' : Z → Fin (matchedBlockOutputBits 64 L) → Bool) (b b' : Bool)
    (μ ν ξ : Z → ℝ) {δ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (state_nonnegative : ∀ z, 0 ≤ ν z)
    (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (state_cap : ∀ z q₀, w z * mapWeight (q z) (r z) q₀ ≤ ν z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (seed : weightDist (retainedSeedWeight w r (fun z c => flipFlopSeedPrefix L (q z c)))
      (uniformSecondWeight (retainedSeedWeight w r
        (fun z c => flipFlopSeedPrefix L (q z c)))) ≤ δ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    weightDist (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')
      (uniformSecondWeight (flipFlopHalfWeight n m L e w l r x x' y y' q q' b b')) ≤
        4 * ε + δ + (K : ℝ) * D * (1 + D ^ 2) * (∑ z, μ z) +
          (K : ℝ) * D ^ 2 * (∑ z, ν z) + (J : ℝ) * C ^ 2 * ∑ z, ξ z := by
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let R : (Fin m → Bool) → Mid → Q := matchedBlockExtractor m 64 L e
  let leak : Z → A → Mid := fun z a =>
    let tampered := flipFlopLookAhead n L e (x' z a) (q' z)
    if b' then tampered.2 else tampered.1
  have room : 64 ≤ L := by have := guard.1; lia
  have error : e + 24 + 2 ≤ L := by have := guard.1; lia
  have first : WeightedStrongSeededExtractor W (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 n L e guard.2.1 room error
  have second : WeightedStrongSeededExtractor QExt (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 _ L e guard.2.2.2 room error
  have refresh : WeightedStrongSeededExtractor R (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth64 m L e guard.2.2.1 room (by have := guard.1; lia)
  cases b with
  | false =>
    have bound := first.fixedTampering_dist_le (by positivity) refresh (by positivity)
      w l r x q y y' leak (flipFlopSeedPrefix L) μ ξ hw hl hr
      left_nonnegative right_nonnegative left_cap right_cap seed
    let project : FixedTamperingTranscript Z Q Mid Q × A →
        (LookAheadBaseTranscript Z Q Mid × Q) × A := fun p =>
      let z := p.1.1.1.1
      let honest := flipFlopLookAhead n L e (x z p.2) p.1.1.2.1
      let tampered := flipFlopLookAhead n L e (x' z p.2) (q' z)
      ((((z, (p.1.1.2.1, q' z)), (honest, tampered)), p.1.1.2.2), p.2)
    have projected := weightDist_uniformSecond_map_first_le
      (fixedTamperingRefreshWeight w l r x q y y' leak (flipFlopSeedPrefix L) W R) project
    have actual : mapWeight (fun p => (project p.1, p.2))
        (fixedTamperingRefreshWeight w l r x q y y' leak (flipFlopSeedPrefix L) W R) =
        flipFlopHalfWeight n m L e w l r x x' y y' q q' false b' := by
      unfold fixedTamperingRefreshWeight flipFlopHalfWeight
      rw [mapWeight_comp]
      apply congrArg (fun f : (Z × B) × A → ((LookAheadBaseTranscript Z Q Mid × Q) × A) × Q =>
        mapWeight f (factoredWeight w l r))
      funext p
      simp only [project, fixedTamperingTranscriptValue, fixedTamperingRightMessage,
        fixedTamperingHonestMessage, flipFlopLookAhead, leak, W, R, Bool.false_eq_true]
      rfl
    rw [actual] at projected
    have result := projected.trans bound
    dsimp only
    have hμ : 0 ≤ ∑ z, μ z := Finset.sum_nonneg (fun z _ => left_nonnegative z)
    have hν : 0 ≤ ∑ z, ν z := Finset.sum_nonneg (fun z _ => state_nonnegative z)
    have hε : 0 ≤ ((2 : ℝ) ^ e)⁻¹ := by positivity
    have extra₁ : 0 ≤ (2 ^ (2 ^ 62 * L) : Nat) * (Fintype.card Mid : ℝ) ^ 3 *
        ∑ z, μ z := by positivity
    have extra₂ : 0 ≤ (2 ^ (2 ^ 62 * L) : Nat) * (Fintype.card Mid : ℝ) ^ 2 *
        ∑ z, ν z := by positivity
    dsimp only [Q, Mid] at result extra₁ extra₂
    have larger := result.trans (le_add_of_nonneg_right
      (add_nonneg (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε) extra₁) extra₂))
    convert larger using 1
    ring
  | true =>
    have bound := first.fixedTampering_second_dist_le (by positivity)
      second (by positivity) refresh (by positivity) w l r x q y y' leak
      (flipFlopSeedPrefix L) μ ν ξ hw hl hr left_nonnegative state_nonnegative
      right_nonnegative left_cap state_cap right_cap seed
    let project : FixedTamperingSecondTranscript Z Q Mid Q × A →
        (LookAheadBaseTranscript Z Q Mid × Q) × A := fun p =>
      let z := p.1.1.1.1
      let honest := flipFlopLookAhead n L e (x z p.2) p.1.1.2.1
      let tampered := flipFlopLookAhead n L e (x' z p.2) (q' z)
      ((((z, (p.1.1.2.1, q' z)), (honest, tampered)), p.1.1.2.2), p.2)
    have projected := weightDist_uniformSecond_map_first_le
      (fixedTamperingSecondRefreshWeight w l r x q y y' leak
        (flipFlopSeedPrefix L) W QExt R) project
    have actual : mapWeight (fun p => (project p.1, p.2))
        (fixedTamperingSecondRefreshWeight w l r x q y y' leak
          (flipFlopSeedPrefix L) W QExt R) =
        flipFlopHalfWeight n m L e w l r x x' y y' q q' true b' := by
      unfold fixedTamperingSecondRefreshWeight flipFlopHalfWeight
      rw [mapWeight_comp]
      apply congrArg (fun f : (Z × B) × A → ((LookAheadBaseTranscript Z Q Mid × Q) × A) × Q =>
        mapWeight f (factoredWeight w l r))
      funext p
      simp only [project, fixedTamperingSecondTranscriptValue, fixedTamperingRightMessage,
        fixedTamperingSecondHonestMessage, flipFlopLookAhead, leak, W, QExt, R]
      rfl
    rw [actual] at projected
    have result := projected.trans bound
    dsimp only
    convert result using 1
    simp only [Fintype.card_prod, Nat.cast_mul]
    ring

end Algebraic.Cutwidth.Extractor.Internal
