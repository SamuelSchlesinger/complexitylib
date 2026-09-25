/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.CanonicalEncoding

/-!
# The canonical DNF switching injection

This module packages the trace-level replay decoder into a single injection on
the canonical-depth bad event. For each bad restriction, classical choice
selects an exact-length path supplied by the structural depth theorem and the
typed source-term trace proved for that path. This is proof-level witness
selection, not enumeration or optimization.

The resulting encoder extends the bad restriction by the trace's satisfying
assignment and stores one bounded position and two bits per path query. The
explicit decoder is a left inverse, hence the encoder is injective on the bad
event.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Switching

/-- A chosen exact-length canonical path witnessing the bad event. -/
noncomputable def chosenPath
    (formula : DNF n)
    (rho : PartialAssignment n)
    (pathLength : Nat)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    DNF.CanonicalPath formula rho pathLength :=
  Classical.choice (formula.exists_canonicalPath rho pathLength deep)

/-- The chosen source-term block trace carried by `chosenPath`. -/
noncomputable def chosenTrace
    (formula : DNF n)
    (rho : PartialAssignment n)
    (pathLength : Nat)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    DNF.CanonicalTrace formula rho
      (chosenPath formula rho pathLength deep).steps :=
  Classical.choice (formula.canonicalTrace_of_path rho
    (chosenPath formula rho pathLength deep).follows)

/-- A harmless total advice value used outside the bad event. -/
def defaultAdvice
    [NeZero widthBound]
    (pathLength : Nat) : Advice widthBound pathLength :=
  fun _ => ⟨Fin.ofNat widthBound 0, false, false⟩

/-- Satisfying extension chosen for a bad restriction; the empty assignment is
used outside the event to keep the probability encoder total. -/
noncomputable def canonicalExtension
    {widthBound : Nat}
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n) : PartialAssignment n :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    (chosenTrace formula rho pathLength deep).satisfyingAssignment
      (widthBound := widthBound)
  else
    PartialAssignment.empty

/-- Total restriction/advice encoding used by the canonical switching
injection. -/
noncomputable def canonicalEncoding
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n) :
    PartialAssignment n × Advice widthBound pathLength :=
  if deep : formula.CanonicalDepthAtLeast rho pathLength then
    let path := chosenPath formula rho pathLength deep
    let trace := chosenTrace formula rho pathLength deep
    (rho.refine
        (trace.satisfyingAssignment (widthBound := widthBound)),
      trace.advice (widthBound := widthBound) path.length_steps)
  else
    (rho, defaultAdvice pathLength)

/-- On the bad event, the encoding output restriction is refinement by the
chosen satisfying extension. -/
theorem canonicalEncoding_fst_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalEncoding (widthBound := widthBound) formula pathLength rho).1 =
      rho.refine
        (canonicalExtension (widthBound := widthBound) formula pathLength rho) := by
  simp [canonicalEncoding, canonicalExtension, deep]

/-- The chosen extension fixes exactly the requested path length. -/
theorem canonicalExtension_fixedCount_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalExtension (widthBound := widthBound)
      formula pathLength rho).fixedCount = pathLength := by
  simp only [canonicalExtension, dite_eq_left deep]
  exact (chosenPath formula rho pathLength deep).satisfyingAssignment_fixedCount
    (chosenTrace formula rho pathLength deep)

/-- The chosen extension fixes only coordinates live in the bad restriction.
-/
theorem canonicalExtension_fixesOnlyLive_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    (canonicalExtension (widthBound := widthBound)
      formula pathLength rho).fixedVariables ⊆ rho.liveVariables := by
  simp only [canonicalExtension, dite_eq_left deep]
  exact (chosenPath formula rho pathLength deep).satisfyingAssignment_fixesOnlyLive
    (chosenTrace formula rho pathLength deep)

/-- The explicit decoder recovers every restriction in the bad event from its
chosen encoding. -/
theorem decode_canonicalEncoding_of_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (rho : PartialAssignment n)
    (deep : formula.CanonicalDepthAtLeast rho pathLength) :
    decode formula
      (canonicalEncoding (widthBound := widthBound) formula pathLength rho) =
      rho := by
  simp only [canonicalEncoding, dite_eq_left deep]
  exact (chosenPath formula rho pathLength deep).decode_satisfyingEncoding
    (chosenTrace formula rho pathLength deep) bounded

/-- The canonical encoder is injective when restricted to the canonical-depth
bad event. -/
theorem canonicalEncoding_injectiveOn_deep
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat) :
    ∀ left, formula.CanonicalDepthAtLeast left pathLength →
      ∀ right, formula.CanonicalDepthAtLeast right pathLength →
        canonicalEncoding (widthBound := widthBound)
            formula pathLength left =
          canonicalEncoding (widthBound := widthBound)
            formula pathLength right →
          left = right := by
  intro left leftDeep right rightDeep equal
  have decodedEqual := congrArg (decode formula) equal
  rw [decode_canonicalEncoding_of_deep formula bounded pathLength left leftDeep,
    decode_canonicalEncoding_of_deep formula bounded pathLength right
      rightDeep] at decodedEqual
  exact decodedEqual

end Switching

namespace DNF

/-- Under a width-zero hypothesis, every typed canonical trace has an empty
query transcript. -/
theorem CanonicalTrace.steps_eq_nil_of_widthAtMost_zero
    {formula : DNF n}
    {rho : PartialAssignment n}
    {steps : List (DecisionTree.PathStep n)}
    (trace : formula.CanonicalTrace rho steps)
    (bounded : formula.WidthAtMost 0) :
    steps = [] := by
  cases trace with
  | nil => rfl
  | start found support_eq nonempty block =>
      rename_i term indices
      have termBound : term.width ≤ 0 :=
        bounded term (firstSurvivingIn_mem rho formula.terms found)
      have lengthLe : (liveSupport term rho).length ≤ term.width := by
        calc
          (liveSupport term rho).length ≤ term.orderedSupport.length :=
            List.length_filter_le _ _
          _ = term.width := term.length_orderedSupport
      have livePositive : 0 < (liveSupport term rho).length := by
        rw [support_eq]
        exact List.length_pos_iff.mpr nonempty
      omega

/-- A width-zero DNF cannot have positive canonical decision-tree depth under
any restriction. -/
theorem not_canonicalDepthAtLeast_of_widthAtMost_zero
    (formula : DNF n)
    (bounded : formula.WidthAtMost 0)
    (rho : PartialAssignment n)
    (pathLength : Nat)
    (positive : 0 < pathLength) :
    ¬formula.CanonicalDepthAtLeast rho pathLength := by
  intro deep
  obtain ⟨path⟩ := formula.exists_canonicalPath rho pathLength deep
  obtain ⟨trace⟩ := formula.canonicalTrace_of_path rho path.follows
  have stepsNil := trace.steps_eq_nil_of_widthAtMost_zero bounded
  have lengthZero := path.length_steps
  rw [stepsNil] at lengthZero
  simp at lengthZero
  omega

end DNF

namespace RandomRestriction

open scoped ENNReal

/-- Exact division-free canonical switching bound. The factor `(4t)^s` is the
cardinality of one bounded position and two bits for each of the `s` path
queries. -/
theorem probability_canonicalDepthAtLeast_scaled_le
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    (fixedWeight p : ENNReal) ^ pathLength *
        probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
        (p : ENNReal) ^ pathLength := by
  have encoded := probability_scaled_le_of_refinement_encoding
    n p atMostOne
    (fun rho => formula.CanonicalDepthAtLeast rho pathLength)
    (Switching.Advice widthBound pathLength) pathLength
    (Switching.canonicalExtension (widthBound := widthBound)
      formula pathLength)
    (Switching.canonicalEncoding (widthBound := widthBound)
      formula pathLength)
    (Switching.canonicalEncoding_injectiveOn_deep
      formula bounded pathLength)
    (Switching.canonicalEncoding_fst_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixesOnlyLive_of_deep
      (widthBound := widthBound) formula pathLength)
    (Switching.canonicalExtension_fixedCount_of_deep
      (widthBound := widthBound) formula pathLength)
  rw [Switching.card_advice] at encoded
  simpa only [Nat.cast_pow] using encoded

/-- Under the standard small-`p` hypothesis, the probability of either fixed
Boolean value is at least `4/9`. -/
theorem four_ninths_le_fixedWeight
    (p : NNReal)
    (small : p ≤ 1 / 9) :
    (4 / 9 : NNReal) ≤ fixedWeight p := by
  rw [fixedWeight]
  apply (le_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
  apply le_tsub_of_add_le_left
  calc
    p + (4 / 9 : NNReal) * 2 ≤
        (1 / 9 : NNReal) + (4 / 9 : NNReal) * 2 := by
      simpa [add_comm] using
        add_le_add_right small ((4 / 9 : NNReal) * 2)
    _ = 1 := by norm_num

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

private theorem four_ninths_pow_mul_nine_pow
    (p : NNReal)
    (widthBound pathLength : Nat) :
    ((4 / 9 : NNReal) : ENNReal) ^ pathLength *
        ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength =
      ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
        (p : ENNReal) ^ pathLength := by
  have numeric : (((4 / 9 : NNReal) : ENNReal) * 9) = 4 := by
    norm_cast
    norm_num
  calc
    ((4 / 9 : NNReal) : ENNReal) ^ pathLength *
          ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
            pathLength =
        (((4 / 9 : NNReal) : ENNReal) *
          ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal))) ^
            pathLength := by
      exact (mul_pow _ _ pathLength).symm
    _ = ((4 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength := by
      congr 1
      calc
        ((4 / 9 : NNReal) : ENNReal) *
              (9 * (p : ENNReal) * (widthBound : ENNReal)) =
            (((4 / 9 : NNReal) : ENNReal) * 9) *
              (p : ENNReal) * (widthBound : ENNReal) := by
          ring
        _ = 4 * (p : ENNReal) * (widthBound : ENNReal) := by rw [numeric]
    _ = ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
          (p : ENNReal) ^ pathLength := by
      push_cast
      rw [mul_pow]
      ring

/-- Standard `9pt` corollary of the canonical switching injection. This is
the weighted Razborov--Beame/Thapen constant obtained from one bounded
position and two advice bits per query. -/
theorem probability_canonicalDepthAtLeast_le_nine_of_pos
    [NeZero widthBound]
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (small : p ≤ 1 / 9) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
        pathLength := by
  let factor : ENNReal := ((4 / 9 : NNReal) : ENNReal) ^ pathLength
  let target : ENNReal :=
    ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^ pathLength
  have fixedLower : ((4 / 9 : NNReal) : ENNReal) ≤
      (fixedWeight p : ENNReal) :=
    ENNReal.coe_le_coe.mpr (four_ninths_le_fixedWeight p small)
  have factorLower : factor ≤ (fixedWeight p : ENNReal) ^ pathLength :=
    pow_le_pow_left' fixedLower pathLength
  have scaled := probability_canonicalDepthAtLeast_scaled_le
    formula bounded pathLength p atMostOne
  have upgraded :
      factor * probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
        ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
          (p : ENNReal) ^ pathLength :=
    (mul_le_mul_of_nonneg_right factorLower bot_le).trans scaled
  have factored :
      factor * target =
        ((4 * widthBound : Nat) : ENNReal) ^ pathLength *
          (p : ENNReal) ^ pathLength := by
    exact four_ninths_pow_mul_nine_pow p widthBound pathLength
  apply le_of_mul_le_mul_left_finite
      (factor := factor)
  · dsimp [factor]
    apply pow_ne_zero
    norm_cast
    norm_num
  · dsimp [factor]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  · exact upgraded.trans_eq factored.symm

/-- For a width-zero DNF and positive threshold, the canonical-depth event has
probability zero. -/
theorem probability_canonicalDepthAtLeast_eq_zero_of_widthAtMost_zero
    (formula : DNF n)
    (bounded : formula.WidthAtMost 0)
    (pathLength : Nat)
    (positive : 0 < pathLength)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) = 0 := by
  calc
    probability n p atMostOne
          (fun rho => formula.CanonicalDepthAtLeast rho pathLength) =
        probability n p atMostOne (fun _ => False) := by
      apply probability_congr
      intro rho
      constructor
      · exact fun deep =>
          (formula.not_canonicalDepthAtLeast_of_widthAtMost_zero
            bounded rho pathLength positive deep).elim
      · exact False.elim
    _ = 0 := probability_false n p atMostOne

/-- Canonical `9pt` switching bound, including width-zero DNFs. -/
theorem probability_canonicalDepthAtLeast_le_nine
    (formula : DNF n)
    (bounded : formula.WidthAtMost widthBound)
    (pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1)
    (small : p ≤ 1 / 9) :
    probability n p atMostOne
        (fun rho => formula.CanonicalDepthAtLeast rho pathLength) ≤
      ((9 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
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
      exact probability_canonicalDepthAtLeast_le_nine_of_pos
        formula bounded pathLength p atMostOne small

end RandomRestriction
end AC0
end Algebraic
