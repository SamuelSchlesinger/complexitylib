/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Initial
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Subset
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Parameters
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Internal.Induction

/-!
# The chosen actual iteration from original sources

The doubled original-left reserve pays the complete first phase and all
subsequent message observations. A uniform original-right source supplies
its own explicit envelope. The finite chooser discharges every guard and
per-round mass requirement of the actual security induction.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem real_card_copies (t width : Nat) :
    (Fintype.card (AffinePhaseOneCopies t width) : ℝ) = (2 : ℝ) ^ ((t + 1) * width) := by
  rw [card_affinePhaseOneCopies, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [Nat.mul_comm]

private theorem real_card_initial_right (t L₀ L : Nat) :
    (Fintype.card (AffinePhaseOneCopies t (matchedBlockSeedBits L)) : ℝ) *
      Fintype.card (AffinePhaseOneRightMessage t L₀) =
        (2 : ℝ) ^ ((t + 1) *
          (matchedBlockSeedBits L₀ + matchedBlockOutputBits 64 L₀ + matchedBlockSeedBits L)) := by
  rw [real_card_copies, card_affinePhaseOneRightMessage,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem affinePhaseOneIterationState_parameters_invariant (n t a target : Nat)
    {Z A B : Type u} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t
      (affinePhaseOneRightBits n t a (affineIterationTarget t target)))
    (advice : Option (Fin t) → List Bool) (μ : Z → ℝ) (positive : 0 < t)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) =
      uniformWeight (Fin (affinePhaseOneRightBits n t a (affineIterationTarget t target)) → Bool))
    (honest_length : (advice none).length = a)
    (tampered_length : ∀ i, (advice (some i)).length = a)
    (different : ∀ i, advice none ≠ advice (some i))
    (source : (∑ z, μ z) ≤ ((2 : ℝ) ^ affineIterationSourceEntropy n t a target)⁻¹) :
    let σ := affineIterationTarget t target
    let d := affinePhaseOneRightBits n t a σ
    let h := growingMatchedBlockDepth t
    let L₀ := affinePhaseOneInitialScale n t a σ
    let L := affinePhaseOneScale n t a σ
    let e := affinePhaseOneLocalError σ
    let s := affinePhaseOneIterationState n d t h L₀ e L (adviceErrorExponent a e) e
      w l r x mask ys advice
    let final := s.iterate e (affineIterationRounds t)
    AffineRowInvariant h t L final.weight final.left final.leftRows t
      (((2 : ℝ) ^ target)⁻¹) := by
  let σ := affineIterationTarget t target
  let d := affinePhaseOneRightBits n t a σ
  let h := growingMatchedBlockDepth t
  let L₀ := affinePhaseOneInitialScale n t a σ
  let L := affinePhaseOneScale n t a σ
  let e := affinePhaseOneLocalError σ
  let s := affinePhaseOneIterationState n d t h L₀ e L (adviceErrorExponent a e) e
    w l r x mask ys advice
  let ν : Z → ℝ := fun z => w z * ((2 : ℝ) ^ d)⁻¹
  let leftEnvelope := affinePhaseOneTranscriptLeftEnvelope n d t L₀ e L
    (adviceErrorExponent a e) μ r mask ys advice
  let rightEnvelope := affinePhaseOneTranscriptRightEnvelope n t L₀ e L ν l x
  have right_nonnegative : ∀ z, 0 ≤ ν z := fun z => mul_nonneg (hw.1 z) (by positivity)
  have right_cap : ∀ z y₀, w z * mapWeight (fun b => ys z b none) (r z) y₀ ≤ ν z := by
    intro z y₀
    rw [uniform]
    apply le_of_eq
    simp only [ν, uniformWeight, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  have right_total : (∑ z, ν z) = ((2 : ℝ) ^ d)⁻¹ := by
    simp only [ν, ← Finset.sum_mul, hw.2, one_mul]
  have probability := affinePhaseOneIterationState_probability n d t h L₀ e L
    (adviceErrorExponent a e) e w l r x mask ys advice hw hl hr
  have left_data := affinePhaseOneIterationState_left_envelope n d t h L₀ e L
    (adviceErrorExponent a e) e w l r x mask ys advice μ hw hl hr nonnegative cap
  have right_data := affinePhaseOneIterationState_right_envelope n d t h L₀ e L
    (adviceErrorExponent a e) e w l r x mask ys advice ν hw hl hr right_nonnegative right_cap
  have initial : AffineRowInvariant h t L s.weight s.left s.leftRows 1
      (((2 : ℝ) ^ σ)⁻¹) := by
    intro S small
    exact affinePhaseOne_left_subset_parameters_dist_le n t a σ
      w l r x mask ys advice S μ positive small hw hl hr nonnegative cap uniform
      honest_length tampered_length different
      (source.trans ((inv_le_inv₀ (by positivity) (by positivity)).mpr
        (pow_le_pow_right₀ (by norm_num) (affineIterationParameters_phase_one_reserve n t a target))))
  have message_card : (Fintype.card (AffineRoundShortMessages t L) : ℝ) =
      (2 : ℝ) ^ affineIterationMessageBits n t a target := by
    rw [card_affineRoundShortMessages, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    exact Nat.mul_comm _ _
  have left_mass (i : Nat) (index : i < affineIterationRounds t) :
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (2 * i) *
        (∑ z, leftEnvelope z) ≤ ((2 : ℝ) ^ affineIterationLeftEntropy n t a target i)⁻¹ := by
    rw [left_data.2.2, message_card, real_card_copies t (matchedBlockOutputBits 64 L₀)]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left source (by positivity)) (by positivity)).trans_eq
        (affineIterationParameters_left_mass n t a target index.le)
  have right_mass (i : Nat) (index : i < affineIterationRounds t) :
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (4 * i) *
        (∑ z, rightEnvelope z) ≤ ((2 : ℝ) ^ affineIterationRightEntropy n t a target i)⁻¹ := by
    rw [right_data.2.2, real_card_initial_right t L₀ L, right_total, message_card]
    exact (affineIterationParameters_right_mass n t a target index.le).le
  have right_guard := affineRoundParameters_right_guard n t a σ
  have row_guard := affineRoundParameters_row_guard n t a σ
  have final_guard := affinePhaseOneParameters_growing_guard n t a σ
  have seed_size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L := by
    apply Nat.mul_le_mul_right L
    exact Nat.pow_le_pow_right (by decide) (by dsimp [h, growingMatchedBlockDepth]; lia)
  have invariant := affineIterationState_iterate_invariant s e (affineIterationRounds t) 1
    (affineIterationLeftEntropy n t a target) (affineIterationRightEntropy n t a target)
    leftEnvelope rightEnvelope seed_size right_guard.2.2.2 row_guard.2.2.2
    right_guard.1 right_guard.2.2.1 final_guard.1 final_guard.2.1 final_guard.2.2
    probability.1 probability.2.1 probability.2.2 left_data.1 right_data.1
    left_data.2.1 right_data.2.1
    (fun _ index => affineIterationParameters_first_reserve n t a target index)
    (affineIterationParameters_merge_reserve n t a target)
    (fun _ index => affineIterationParameters_recover_reserve n t a target index)
    (fun _ index => affineIterationParameters_final_reserve n t a target index)
    left_mass right_mass initial (affineIterationRounds t) le_rfl
  exact invariant.mono h t L
    (by simpa only [Nat.mul_one] using (Nat.le_succ t).trans (affineIterationRounds_cover t))
    (affineIterationParameters_error_budget t target)

end Algebraic.Cutwidth.Extractor.Internal
