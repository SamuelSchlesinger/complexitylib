/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Parameters.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Extraction.Internal.Initial
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Initial
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Iteration
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Final
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Extraction by the complete actual advice program

The original factored inputs construct the initial invariant. Paired advice
is processed by the actual fold, and unequal advice supplies separation at
its end. Final extraction retains the original right state and the actual
tampered output. Thus only original-source hypotheses occur in the result;
no intermediate extractor certificate or transcript witness is assumed.

This implements the CGL Algorithm 2 advice-chain argument with the extra
final extraction from the original left source. The finite bound uses the
conservative checked recurrence, rather than the sharper published error.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

universe u

theorem adviceCorrelationBreaker_chain_dist_le (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e) (size : matchedBlockOutputBits 64 L ≤ m)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (length : advice.length = advice'.length) (different : advice ≠ advice') :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    weightDist actual (uniformSecondWeight actual) ≤
      adviceChainError L e 0 (∑ z, μ z) (((2 : ℝ) ^ m)⁻¹) advice.length +
        ((2 : ℝ) ^ e)⁻¹ + (2 : ℝ) ^ (2 ^ 62 * L) *
          D ^ (8 * advice.length + 1) * ∑ z, μ z := by
  classical
  let ξ := fun z => w z * ((2 : ℝ) ^ m)⁻¹
  let q := fun z b => adviceInitialState m L (y z b)
  let q' := fun z b => adviceInitialState m L (y' z b)
  have initial : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ 0 := by
    rw [adviceInitialState_retained_dist m L w r y size uniform]
  let I := AdviceInvariant.initial n m L w l r x y q q' μ ξ hw hl hr nonnegative
    (fun z => mul_nonneg (hw.1 z) (by positivity)) cap
    (fun z y₀ => le_of_eq (adviceUniformRight_cap m w r y uniform z y₀)) initial
  obtain ⟨J⟩ := I.iterate e guard x' y' (advice.zip advice')
  have first : (advice.zip advice').map Prod.fst = advice := List.map_fst_zip length.le
  have second : (advice.zip advice').map Prod.snd = advice' := List.map_snd_zip length.ge
  have pairLength : (advice.zip advice').length = advice.length := by
    rw [List.length_zip, length, min_self]
  have separated : False ∨ (advice.zip advice').map Prod.fst ≠
      (advice.zip advice').map Prod.snd := by
    rw [first, second]
    exact Or.inr different
  have extract := matchedBlockExtractor_depth24 n L e guard.2.1
    (by have := guard.1; lia) (by have := guard.1; lia)
  have final := J.final_dist_le separated extract (by positivity) x'
  dsimp only at final
  change weightDist
      (mapWeight (fun a : (Z × B) × A =>
        ((a.1, matchedBlockExtractor n 24 L e (x' a.1.1 a.2)
          (flipFlopSeedPrefix L (adviceFold n m L e (x' a.1.1 a.2) (y' a.1.1 a.1.2)
            (adviceInitialState m L (y' a.1.1 a.1.2)) ((advice.zip advice').map Prod.snd)))),
          matchedBlockExtractor n 24 L e (x a.1.1 a.2)
            (flipFlopSeedPrefix L (adviceFold n m L e (x a.1.1 a.2) (y a.1.1 a.1.2)
              (adviceInitialState m L (y a.1.1 a.1.2)) ((advice.zip advice').map Prod.fst)))))
        (factoredWeight w l r)) _ ≤ _ at final
  rw [first, second] at final
  change weightDist
      (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')
      (uniformSecondWeight
        (adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice')) ≤
      ((2 : ℝ) ^ e)⁻¹ + adviceChainError L e 0 (∑ z, μ z) (∑ z, ξ z)
        (advice.zip advice').length + (↑(2 ^ (2 ^ 62 * L) : Nat) : ℝ) *
          Fintype.card (Fin (matchedBlockSeedBits L) → Bool) *
          ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^
            (8 * (advice.zip advice').length) * ∑ z, μ z) at final
  rw [pairLength, adviceUniformRight_sum m w hw, Nat.cast_pow, Nat.cast_ofNat] at final
  apply final.trans_eq
  rw [pow_succ]
  ring

theorem adviceCorrelationBreaker_dist_le (n m L e : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e) (size : matchedBlockOutputBits 64 L ≤ m)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (length : advice.length = advice'.length) (different : advice ≠ advice') :
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤
      adviceCorrelationBreakerError m L e advice.length (∑ z, μ z) := by
  have actual := adviceCorrelationBreaker_chain_dist_le n m L e guard size
    w l r x x' y y' advice advice' μ hw hl hr nonnegative cap uniform length different
  have bound := adviceChainError_le L e advice.length (α := ∑ z, μ z)
    (Finset.sum_nonneg (fun z _ => nonnegative z)) (by positivity : 0 ≤ ((2 : ℝ) ^ m)⁻¹)
  apply actual.trans
  dsimp only [adviceCorrelationBreakerError]
  dsimp only at bound
  linarith only [bound]

theorem adviceCorrelationBreaker_dyadic_dist_le (n m L target : Nat) {Z A B : Type u}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y y' : Z → B → Fin m → Bool)
    (advice advice' : List Bool) (μ : Z → ℝ)
    (guard : FlipFlopSizeGuard n m L (adviceErrorExponent advice.length target))
    (size : matchedBlockOutputBits 64 L ≤ m)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (y z) (r z) = uniformWeight (Fin m → Bool))
    (length : advice.length = advice'.length) (different : advice ≠ advice')
    (left : (∑ z, μ z) ≤ ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹)
    (right : 2 ^ 150 * (advice.length + 1) * L ≤ m) :
    let e := adviceErrorExponent advice.length target
    let actual := adviceCorrelationBreakerWeight n m L e w l r x x' y y' advice advice'
    weightDist actual (uniformSecondWeight actual) ≤ ((2 : ℝ) ^ target)⁻¹ := by
  have actual := adviceCorrelationBreaker_chain_dist_le n m L
    (adviceErrorExponent advice.length target) guard size
    w l r x x' y y' advice advice' μ hw hl hr nonnegative cap uniform length different
  have rightBound : ((2 : ℝ) ^ m)⁻¹ ≤
      ((2 : ℝ) ^ (2 ^ 150 * (advice.length + 1) * L))⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) right
  exact actual.trans (adviceChainError_fixedReserve_dyadic_le L advice.length target
    (by have := guard.1; change adviceErrorExponent advice.length target ≤ L; lia)
    (Finset.sum_nonneg (fun z _ => nonnegative z)) (by positivity) left rightBound)

end Algebraic.Cutwidth.Extractor.Internal
