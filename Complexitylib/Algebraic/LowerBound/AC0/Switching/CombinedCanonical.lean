/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Canonical
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CombinedCanonicalPacking

/-!
# The combined canonical DNF switching injection

This module replaces the elementary per-query advice alphabet in the
canonical switching injection by the counted source-term block encoding. The
explicit decoder proves injectivity on the bad event, and the general weighted
restriction engine yields the exact scaled bound with advice base
`((5t - 1) / 2)^s` for positive width `t`.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Switching

/-- The one-position block advice at position `0` with the given difference bit. -/
def defaultBlock
    [NeZero width]
    (difference : Bool) : BlockAdvice width 1 :=
  { positions := ⟨{Fin.ofNat width 0}, by simp⟩
    differences := fun _ => difference }

theorem defaultBlock_true_hasMismatch
    [NeZero width] :
    (defaultBlock (width := width) true).HasMismatch := by
  intro allZero
  have atZero := congrFun allZero (0 : Fin 1)
  simp [defaultBlock] at atZero

/-- A harmless total combined-advice value used outside the bad event. -/
def defaultCombinedAdvice
    [NeZero width] : (pathLength : Nat) → CombinedAdvice width pathLength
  | 0 => by
      simp only [CombinedAdvice]
      exact PUnit.unit
  | 1 =>
      CombinedAdvice.ofFinalBlock (defaultBlock false)
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne width))
  | pathLength + 2 => by
      have advice := CombinedAdvice.prependBlock (blockRemaining := 0)
        (tailLength := pathLength + 1)
        ⟨defaultBlock true, defaultBlock_true_hasMismatch⟩
        (defaultCombinedAdvice (pathLength + 1))
        (Nat.one_le_iff_ne_zero.mpr (NeZero.ne width)) (by omega)
      simpa only [Nat.zero_add, Nat.succ_eq_add_one] using advice

/-- Total combined restriction/advice encoding for the canonical-depth bad
event. -/
noncomputable def combinedCanonicalEncoding
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n) :
    PartialAssignment n × CombinedAdvice widthBound pathLength :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    let path := chosenPath formula rho pathLength deep
    let trace := chosenTrace formula rho pathLength deep
    (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound)),
      trace.combinedAdviceOfLength bounded path.length_steps)
  else
    (rho, defaultCombinedAdvice pathLength)

/-- On the bad event, combined encoding refines by the same canonical
satisfying extension as the elementary encoder. -/
theorem combinedCanonicalEncoding_fst_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (combinedCanonicalEncoding formula bounded pathLength rho).1 =
      rho.refine
        (canonicalExtension (widthBound := widthBound)
          formula pathLength rho) := by
  simp [combinedCanonicalEncoding, canonicalExtension, deep]

/-- The combined decoder recovers every bad-event restriction. -/
theorem decodeCombined_combinedCanonicalEncoding_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    decodeCombined formula
      (combinedCanonicalEncoding formula bounded pathLength rho) = rho := by
  simp only [combinedCanonicalEncoding, dite_eq_left deep]
  exact (chosenPath formula rho pathLength deep).decodeCombined_satisfyingEncoding
    (chosenTrace formula rho pathLength deep) bounded

/-- The combined encoder is injective on the canonical-depth bad event. -/
theorem combinedCanonicalEncoding_injectiveOn_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        combinedCanonicalEncoding formula bounded pathLength left =
          combinedCanonicalEncoding formula bounded pathLength right →
          left = right := by
  intro left leftDeep right rightDeep equal
  have decodedEqual := congrArg (decodeCombined formula) equal
  rw [decodeCombined_combinedCanonicalEncoding_of_deep
        formula bounded pathLength left leftDeep,
    decodeCombined_combinedCanonicalEncoding_of_deep
      formula bounded pathLength right rightDeep] at decodedEqual
  exact decodedEqual

/-- The combined-advice cardinality bound transferred to extended
nonnegative reals for probability estimates. -/
theorem card_combinedAdvice_cast_le_ennreal
    (width pathLength : Nat)
    (widthPositive : 0 < width) :
    (Fintype.card (CombinedAdvice width pathLength) : ENNReal) ≤
      ((((5 * width - 1 : Nat) : ENNReal) / 2) ^ pathLength) := by
  have realBound := card_combinedAdvice_cast_le width pathLength widthPositive
  have realNumerator :
      ((5 * width - 1 : Nat) : Real) = (5 : Real) * width - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 5 * width)]
    norm_num
  rw [← realNumerator] at realBound
  have nnrealBound :
      (Fintype.card (CombinedAdvice width pathLength) : NNReal) ≤
        ((((5 * width - 1 : Nat) : NNReal) / 2) ^ pathLength) := by
    exact_mod_cast realBound
  simpa using (ENNReal.coe_le_coe.mpr nnrealBound)

end Switching

namespace RandomRestriction

open scoped ENNReal

/-- Exact weighted switching inequality before inserting the combined-advice
cardinality estimate. -/
theorem probability_canonicalDepthAtLeast_combined_card_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      (Fintype.card (Switching.CombinedAdvice widthBound pathLength) :
          ENNReal) *
        (p : ENNReal) ^ pathLength := by
  let _ : DecidableEq (Switching.CombinedAdvice widthBound pathLength) :=
    Classical.decEq _
  exact probability_scaled_le_of_refinement_encoding
    n p atMostOne
    (fun rho => formula.CanonicalDepthAtLeast rho pathLength)
    (Switching.CombinedAdvice widthBound pathLength) pathLength
    (Switching.canonicalExtension (widthBound := widthBound)
      formula pathLength)
    (Switching.combinedCanonicalEncoding formula bounded pathLength)
    (Switching.combinedCanonicalEncoding_injectiveOn_deep
      formula bounded pathLength)
    (Switching.combinedCanonicalEncoding_fst_of_deep
      formula bounded pathLength)
    (Switching.canonicalExtension_fixesOnlyLive_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixedCount_of_deep
      (widthBound := widthBound) formula pathLength)

/-- Exact positive-width scaled switching inequality with Beame's combined
advice base `((5t - 1) / 2)^s`. -/
theorem probability_canonicalDepthAtLeast_combined_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^ pathLength) *
        (p : ENNReal) ^ pathLength := by
  calc
    (fixedWeight p : ENNReal) ^ pathLength *
          probability n p atMostOne
            (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
        (Fintype.card
            (Switching.CombinedAdvice widthBound pathLength) : ENNReal) *
          (p : ENNReal) ^ pathLength :=
      probability_canonicalDepthAtLeast_combined_card_scaled_le
        formula bounded pathLength p atMostOne
    _ ≤ ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^
          pathLength) * (p : ENNReal) ^ pathLength :=
      mul_le_mul_left
        (Switching.card_combinedAdvice_cast_le_ennreal
          widthBound pathLength (NeZero.pos widthBound)) _

private theorem combinedBase_mul_le_fixedWeight_mul_five
    (width : Nat)
    (widthPositive : 0 < width)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (small : (5 : NNReal) * p * width ≤ 1) :
    (((5 * width - 1 : Nat) : NNReal) / 2) * p ≤
      fixedWeight p * ((5 : NNReal) * p * width) := by
  rw [fixedWeight]
  have subCancel : 1 - p + p = (1 : NNReal) :=
    tsub_add_cancel_of_le atMostOne
  have numerator :
      ((5 * width - 1 : Nat) : NNReal) + 1 = 5 * width := by
    norm_cast
    omega
  have twoPositive : (0 : NNReal) < 2 := by norm_num
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right twoPositive).2
  have productSmall :
      p * ((5 : NNReal) * p * width) ≤ p := by
    simpa using mul_le_mul_right small p
  have numeratorProduct :
      ((5 * width - 1 : Nat) : NNReal) * p + p =
        (5 : NNReal) * p * width := by
    calc
      ((5 * width - 1 : Nat) : NNReal) * p + p =
          (((5 * width - 1 : Nat) : NNReal) + 1) * p := by ring
      _ = ((5 : NNReal) * width) * p := by rw [numerator]
      _ = (5 : NNReal) * p * width := by ring
  have splitProduct :
      (1 - p) * ((5 : NNReal) * p * width) +
          p * ((5 : NNReal) * p * width) =
        (5 : NNReal) * p * width := by
    calc
      (1 - p) * ((5 : NNReal) * p * width) +
            p * ((5 : NNReal) * p * width) =
          ((1 - p) + p) * ((5 : NNReal) * p * width) := by ring
      _ = (5 : NNReal) * p * width := by rw [subCancel]; simp
  apply (add_le_add_iff_right
    (p * ((5 : NNReal) * p * width))).mp
  calc
    ((5 * width - 1 : Nat) : NNReal) * p +
          p * ((5 : NNReal) * p * width) ≤
        ((5 * width - 1 : Nat) : NNReal) * p + p :=
      by simpa [add_comm] using
        add_le_add_left productSmall
          (((5 * width - 1 : Nat) : NNReal) * p)
    _ = (5 : NNReal) * p * width := numeratorProduct
    _ = (1 - p) * ((5 : NNReal) * p * width) +
          p * ((5 : NNReal) * p * width) := splitProduct.symm

private theorem le_of_mul_le_mul_left_finite
    {factor left right : ENNReal}
    (factorNonzero : factor ≠ 0)
    (factorFinite : factor ≠ ⊤)
    (scaled : factor * left ≤ factor * right) :
    left ≤ right := by
  by_contra notLe
  have strict := ENNReal.mul_lt_mul_left factorNonzero factorFinite
    (lt_of_not_ge notLe)
  rw [mul_comm right factor, mul_comm left factor] at strict
  exact (not_lt_of_ge scaled) strict

/-- Positive-width canonical switching lemma with the standard `5pt` base. -/
theorem probability_canonicalDepthAtLeast_le_five_of_pos
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength := by
  by_cases small : (5 : NNReal) * p * widthBound ≤ 1
  · let factor : ENNReal := (fixedWeight p : ENNReal) ^ pathLength
    let target : ENNReal :=
      ((5 : ENNReal) * (p : ENNReal) *
        (widthBound : ENNReal)) ^ pathLength
    have oneLeWidth : (1 : NNReal) ≤ widthBound := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne widthBound)
    have fivePLeFivePWidth :
        (5 : NNReal) * p ≤ (5 : NNReal) * p * widthBound := by
      simpa using mul_le_mul_right oneLeWidth ((5 : NNReal) * p)
    have fivePLeOne : (5 : NNReal) * p ≤ 1 :=
      fivePLeFivePWidth.trans small
    have pLeFifth : p ≤ (1 / 5 : NNReal) := by
      apply (le_div_iff₀ (by norm_num : (0 : NNReal) < 5)).2
      simpa [mul_comm] using fivePLeOne
    have pLtOne : p < 1 := pLeFifth.trans_lt (by norm_num)
    have fixedPositive : 0 < fixedWeight p := by
      rw [fixedWeight]
      exact div_pos (tsub_pos_iff_lt.mpr pLtOne) (by norm_num)
    have stepNN := combinedBase_mul_le_fixedWeight_mul_five
      widthBound (NeZero.pos widthBound) p atMostOne small
    have step :
        ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) *
            (p : ENNReal)) ≤
          (fixedWeight p : ENNReal) *
            ((5 : ENNReal) * (p : ENNReal) *
              (widthBound : ENNReal)) := by
      simpa using (ENNReal.coe_le_coe.mpr stepNN)
    have scaled :=
      probability_canonicalDepthAtLeast_combined_scaled_le
        formula bounded pathLength p atMostOne
    have rightBound :
        ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^
              pathLength) * (p : ENNReal) ^ pathLength ≤
          factor * target := by
      calc
        ((((5 * widthBound - 1 : Nat) : ENNReal) / 2) ^
              pathLength) * (p : ENNReal) ^ pathLength =
            (((((5 * widthBound - 1 : Nat) : ENNReal) / 2) *
              (p : ENNReal)) ^ pathLength) :=
          (mul_pow _ _ pathLength).symm
        _ ≤ (((fixedWeight p : ENNReal) *
              ((5 : ENNReal) * (p : ENNReal) *
                (widthBound : ENNReal))) ^ pathLength) :=
          pow_le_pow_left' step pathLength
        _ = factor * target := by
          rw [mul_pow]
    apply le_of_mul_le_mul_left_finite (factor := factor)
    · dsimp [factor]
      apply pow_ne_zero
      exact ENNReal.coe_ne_zero.mpr (ne_of_gt fixedPositive)
    · dsimp [factor]
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    · exact scaled.trans rightBound
  · have oneLtTargetNN :
        (1 : NNReal) < (5 : NNReal) * p * widthBound :=
      lt_of_not_ge small
    have oneLeTarget :
        (1 : ENNReal) ≤
          (5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal) := by
      exact (ENNReal.coe_le_coe.mpr oneLtTargetNN.le)
    exact (probability_le_one n p atMostOne
      (fun rho => formula.CanonicalDepthAtLeast rho pathLength)).trans
        (by simpa using pow_le_pow_left' oneLeTarget pathLength)

/-- Canonical `5pt` switching lemma, including width-zero DNFs. -/
theorem probability_canonicalDepthAtLeast_le_five
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength := by
  cases widthBound with
  | zero =>
      cases pathLength with
      | zero =>
          simpa using probability_le_one n p atMostOne
            (fun rho => formula.CanonicalDepthAtLeast rho 0)
      | succ length =>
          rw [probability_canonicalDepthAtLeast_eq_zero_of_widthAtMost_zero
            formula bounded (Nat.succ length) (Nat.succ_pos length)
            p atMostOne]
          exact bot_le
  | succ width =>
      exact probability_canonicalDepthAtLeast_le_five_of_pos
        formula bounded pathLength p atMostOne

end RandomRestriction
end AC0
end Algebraic
