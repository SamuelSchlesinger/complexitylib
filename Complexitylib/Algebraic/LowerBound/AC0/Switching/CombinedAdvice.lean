/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Combined block advice for the switching lemma

This module isolates the finite counting argument that improves the elementary
one-position/two-bit switching encoding. Following the combined encoding in
Beame's *A Switching Lemma Primer*, a term block records an unordered subset of
source-term positions and the path bits relative to the assignment satisfying
that term. Every block followed by another block has a nonzero difference
string; only the final block may use the all-zero string.

`CombinedAdvice width pathLength` packages exactly those block sequences. Its
cardinality is at most `((5 * width - 1) / 2) ^ pathLength` for positive width.
This is an abstract structural count: it does not enumerate formulas, paths,
or circuits.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Switching

/-- Advice for one source-term block. Positions form a subset because the
canonical path queries them in source order; sorting the subset recovers that
order. Each Boolean says whether the path value differs from the value that
satisfies the corresponding literal. -/
structure BlockAdvice (width length : Nat) where
  /-- Queried source-term positions. -/
  positions : {set : Finset (Fin width) // set.card = length}
  /-- Difference bits, indexed in increasing source-position order. -/
  differences : Fin length → Bool
  deriving DecidableEq

/-- A block has a mismatch when its path falsifies at least one of the source
term's literals. -/
def BlockAdvice.HasMismatch (block : BlockAdvice width length) : Prop :=
  block.differences ≠ fun _ => false

/-- A nonfinal block, whose difference string must be nonzero before the
canonical construction can move to a later source term. -/
abbrev ContinuingBlockAdvice (width length : Nat) :=
  {block : BlockAdvice width length // block.HasMismatch}

/-- A sequence of source-term blocks occupying exactly `pathLength` queries.
The last block is arbitrary; every block with a recursive tail is continuing
and therefore carries a mismatch. -/
def CombinedAdvice (width : Nat) : Nat → Type
  | 0 => PUnit
  | pathLength + 1 =>
      (blockLengthMinusOne : Fin (Nat.min width (pathLength + 1))) ×
        if blockLengthMinusOne.val = pathLength then
          BlockAdvice width (blockLengthMinusOne.val + 1)
        else
          ContinuingBlockAdvice width (blockLengthMinusOne.val + 1) ×
            CombinedAdvice width
              (pathLength - blockLengthMinusOne.val)

/-- The finite enumeration inherited from bounded position subsets and Boolean
difference strings. -/
noncomputable instance blockAdviceFintype :
    Fintype (BlockAdvice width length) := by
  classical
  let equiv : BlockAdvice width length ≃
      ({set : Finset (Fin width) // set.card = length} ×
        (Fin length → Bool)) :=
    { toFun := fun block => (block.positions, block.differences)
      invFun := fun pair => ⟨pair.1, pair.2⟩
      left_inv := by intro block; cases block; rfl
      right_inv := by intro pair; cases pair; rfl }
  exact Fintype.ofEquiv _ equiv.symm

/-- Proof-irrelevant finiteness obtained by strong induction on total path
length. -/
noncomputable instance combinedAdviceFinite (width pathLength : Nat) :
    Finite (CombinedAdvice width pathLength) := by
  induction pathLength using Nat.strong_induction_on with
  | h pathLength inductionHypothesis =>
      classical
      cases pathLength with
      | zero =>
          simp only [CombinedAdvice]
          infer_instance
      | succ remaining =>
          simp only [CombinedAdvice]
          let _ : ∀ index : Fin (Nat.min width (remaining + 1)),
              Fintype (CombinedAdvice width (remaining - index.val)) :=
            fun index => @Fintype.ofFinite
              (CombinedAdvice width (remaining - index.val))
              (inductionHypothesis _ (by omega))
          let _ : ∀ index : Fin (Nat.min width (remaining + 1)),
              Fintype (if index.val = remaining then
                BlockAdvice width (index.val + 1)
              else
                ContinuingBlockAdvice width (index.val + 1) ×
                  CombinedAdvice width (remaining - index.val)) :=
            fun index => by split <;> infer_instance
          exact @Finite.of_fintype _ (by infer_instance)

/-- Combined advice is finite at every path length. -/
noncomputable instance combinedAdviceFintype (width pathLength : Nat) :
    Fintype (CombinedAdvice width pathLength) := Fintype.ofFinite _

/-- Continuing blocks form a finite subtype of block advice. -/
noncomputable instance continuingBlockAdviceFintype (width length : Nat) :
    Fintype (ContinuingBlockAdvice width length) := Fintype.ofFinite _

/-- A length-`length` block chooses that many of the `width` positions and one
Boolean difference bit per position. -/
theorem card_blockAdvice (width length : Nat) :
    Fintype.card (BlockAdvice width length) =
      width.choose length * 2 ^ length := by
  let equiv : BlockAdvice width length ≃
      ({set : Finset (Fin width) // set.card = length} ×
        (Fin length → Bool)) :=
    { toFun := fun block => (block.positions, block.differences)
      invFun := fun pair => ⟨pair.1, pair.2⟩
      left_inv := by intro block; cases block; rfl
      right_inv := by intro pair; cases pair; rfl }
  rw [Fintype.card_congr equiv]
  simp

private theorem card_nonzeroDifference (length : Nat) :
    Fintype.card {differences : Fin length → Bool //
        differences ≠ fun _ => false} =
      2 ^ length - 1 := by
  rw [Fintype.card_subtype_compl
    (fun differences : Fin length → Bool =>
      differences = fun _ => false)]
  simp

/-- Requiring a mismatch removes exactly the all-zero difference string. -/
theorem card_continuingBlockAdvice (width length : Nat) :
    Fintype.card (ContinuingBlockAdvice width length) =
      width.choose length * (2 ^ length - 1) := by
  let equiv : ContinuingBlockAdvice width length ≃
      ({set : Finset (Fin width) // set.card = length} ×
        {differences : Fin length → Bool //
          differences ≠ fun _ => false}) :=
    { toFun := fun block =>
        (block.val.positions, ⟨block.val.differences, block.property⟩)
      invFun := fun pair =>
        ⟨⟨pair.1, pair.2.val⟩, pair.2.property⟩
      left_inv := by intro block; cases block with | mk block property => cases block; rfl
      right_inv := by intro pair; cases pair with | mk positions differences => cases differences; rfl }
  rw [Fintype.card_congr equiv]
  simp

/-- Exact first-block recurrence for the combined advice cardinality. -/
theorem card_combinedAdvice_succ (width pathLength : Nat) :
    Nat.card (CombinedAdvice width (pathLength + 1)) =
      ∑ index : Fin (Nat.min width (pathLength + 1)),
        if index.val = pathLength then
          width.choose (index.val + 1) * 2 ^ (index.val + 1)
        else
          (width.choose (index.val + 1) *
              (2 ^ (index.val + 1) - 1)) *
            Nat.card
              (CombinedAdvice width (pathLength - index.val)) := by
  rw [show pathLength + 1 = Nat.succ pathLength by omega]
  simp only [CombinedAdvice]
  let _ : ∀ index : Fin (Nat.min width (pathLength + 1)),
      Finite (if index.val = pathLength then
        BlockAdvice width (index.val + 1)
      else
        ContinuingBlockAdvice width (index.val + 1) ×
          CombinedAdvice width (pathLength - index.val)) :=
    fun index => by split <;> infer_instance
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro index _
  split <;>
    simp [Nat.card_eq_fintype_card, card_blockAdvice,
      card_continuingBlockAdvice]

private theorem exp_six_sevenths_le_twelve_fifths :
    Real.exp (6 / 7 : Real) ≤ 12 / 5 := by
  calc
    Real.exp (6 / 7 : Real) ≤
        (∑ m ∈ Finset.range 4,
          (6 / 7 : Real) ^ m / m.factorial) +
        (6 / 7 : Real) ^ 4 * (4 + 1) / ((4 : Nat).factorial * 4) := by
      exact Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
    _ ≤ 12 / 5 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem positive_binomial_sum_le_exp
    (width cutoff : Nat)
    (beta : Real)
    (betaPositive : 0 < beta) :
    (∑ index : Fin (Nat.min width cutoff),
        (width.choose (index.val + 1) : Real) *
          (2 / beta) ^ (index.val + 1)) ≤
      Real.exp (2 * width / beta) - 1 := by
  change (∑ index : Fin (Nat.min width cutoff),
      (fun index : Nat =>
        (width.choose (index + 1) : Real) *
          (2 / beta) ^ (index + 1)) index) ≤ _
  let summand : Nat → Real := fun index =>
    (width.choose (index + 1) : Real) *
      (2 / beta) ^ (index + 1)
  have sumEq :
      (∑ index : Fin (Nat.min width cutoff), summand index.val) =
        ∑ index ∈ Finset.range (Nat.min width cutoff), summand index :=
    Fin.sum_univ_eq_sum_range summand (Nat.min width cutoff)
  change (∑ index : Fin (Nat.min width cutoff), summand index.val) ≤ _
  rw [sumEq]
  dsimp only [summand]
  have termwise : ∀ index ∈ Finset.range (Nat.min width cutoff),
      (width.choose (index + 1) : Real) *
          (2 / beta) ^ (index + 1) ≤
        (2 * width / beta) ^ (index + 1) /
          (index + 1).factorial := by
    intro index _
    have chooseBound : (width.choose (index + 1) : Real) ≤
        (width : Real) ^ (index + 1) / (index + 1).factorial :=
      Nat.choose_le_pow_div (index + 1) width
    have multiplierNonnegative : 0 ≤ (2 / beta : Real) ^ (index + 1) := by
      positivity
    calc
      (width.choose (index + 1) : Real) *
            (2 / beta) ^ (index + 1) ≤
          ((width : Real) ^ (index + 1) /
            (index + 1).factorial) *
              (2 / beta) ^ (index + 1) :=
        mul_le_mul_of_nonneg_right chooseBound multiplierNonnegative
      _ = (2 * width / beta) ^ (index + 1) /
          (index + 1).factorial := by
        field_simp [ne_of_gt betaPositive, Nat.factorial_ne_zero]
        ring
  calc
    (∑ index ∈ Finset.range (Nat.min width cutoff),
        (width.choose (index + 1) : Real) *
          (2 / beta) ^ (index + 1)) ≤
        ∑ index ∈ Finset.range (Nat.min width cutoff),
          (2 * width / beta) ^ (index + 1) /
            (index + 1).factorial := by
      exact Finset.sum_le_sum termwise
    _ ≤ Real.exp (2 * width / beta) - 1 := by
      have series := Real.sum_le_exp_of_nonneg
        (show 0 ≤ (2 * width / beta : Real) by positivity)
        (Nat.min width cutoff + 1)
      rw [Finset.sum_range_succ'] at series
      norm_num [Nat.factorial] at series ⊢
      linarith

private noncomputable def combinedAdviceBase (width : Nat) : Real :=
  ((5 : Real) * width - 1) / 2

private theorem combinedAdviceBase_pos
    {width : Nat}
    (positive : 0 < width) :
    0 < combinedAdviceBase width := by
  unfold combinedAdviceBase
  have widthOne : (1 : Real) ≤ width := by exact_mod_cast positive
  nlinarith

private theorem scaled_width_le_six_sevenths
    {width : Nat}
    (atLeastThree : 3 ≤ width) :
    2 * (width : Real) / combinedAdviceBase width ≤ 6 / 7 := by
  have basePositive : 0 < combinedAdviceBase width :=
    combinedAdviceBase_pos (by omega)
  rw [div_le_iff₀ basePositive]
  unfold combinedAdviceBase
  norm_num
  have widthThree : (3 : Real) ≤ width := by exact_mod_cast atLeastThree
  nlinarith

private theorem two_fifths_le_width_div_combinedAdviceBase
    {width : Nat}
    (positive : 0 < width) :
    (2 / 5 : Real) ≤ width / combinedAdviceBase width := by
  have basePositive : 0 < combinedAdviceBase width :=
    combinedAdviceBase_pos positive
  rw [le_div_iff₀ basePositive]
  unfold combinedAdviceBase
  norm_num
  linarith

private noncomputable def normalizedContribution
    (width total : Nat)
    (index : Fin (Nat.min width total)) : Real :=
  let length := index.val + 1
  if length = total then
    (width.choose length : Real) * 2 ^ length /
      combinedAdviceBase width ^ length
  else
    (width.choose length : Real) * (2 ^ length - 1) /
      combinedAdviceBase width ^ length

private theorem normalizedContribution_plus_first_le
    {width total : Nat}
    (widthPositive : 0 < width)
    (totalAtLeastTwo : 2 ≤ total)
    (index : Fin (Nat.min width total)) :
    normalizedContribution width total index +
        (if index.val = 0 then
          (width : Real) / combinedAdviceBase width else 0) ≤
      (width.choose (index.val + 1) : Real) *
        2 ^ (index.val + 1) /
          combinedAdviceBase width ^ (index.val + 1) := by
  have basePositive : 0 < combinedAdviceBase width :=
    combinedAdviceBase_pos widthPositive
  by_cases indexZero : index.val = 0
  · have notFinal : index.val + 1 ≠ total := by omega
    have oneNotFinal : 1 ≠ total := by omega
    simp [normalizedContribution, indexZero,
      oneNotFinal, Nat.choose_one_right]
    field_simp [ne_of_gt basePositive]
    norm_num
  · simp only [indexZero, ite_false, add_zero]
    by_cases final : index.val + 1 = total
    · simp only [normalizedContribution, final, ite_true]
      rfl
    · simp only [normalizedContribution, final, ite_false]
      gcongr
      norm_num

private theorem normalizedContribution_sum_add_first_le
    {width total : Nat}
    (widthPositive : 0 < width)
    (totalAtLeastTwo : 2 ≤ total) :
    (∑ index : Fin (Nat.min width total),
        normalizedContribution width total index) +
        (width : Real) / combinedAdviceBase width ≤
      ∑ index : Fin (Nat.min width total),
        (width.choose (index.val + 1) : Real) *
          2 ^ (index.val + 1) /
            combinedAdviceBase width ^ (index.val + 1) := by
  classical
  have totalPositive : 0 < total := by omega
  have minPositive : 0 < Nat.min width total :=
    lt_min widthPositive totalPositive
  let first : Fin (Nat.min width total) := ⟨0, minPositive⟩
  have firstSum :
      (∑ index : Fin (Nat.min width total),
        if index.val = 0 then
          (width : Real) / combinedAdviceBase width else 0) =
        (width : Real) / combinedAdviceBase width := by
    apply Finset.sum_eq_single first
    · intro index _ indexNe
      have valNe : index.val ≠ 0 := by
        intro equal
        apply indexNe
        exact Fin.ext equal
      simp [valNe]
    · simp
  have pointwise := fun index : Fin (Nat.min width total) =>
    normalizedContribution_plus_first_le widthPositive totalAtLeastTwo index
  have summed := Finset.sum_le_sum fun index (_present : index ∈
      (Finset.univ : Finset (Fin (Nat.min width total))) ) => pointwise index
  simpa [Finset.sum_add_distrib, firstSum] using summed

private theorem normalizedContribution_sum_le_one_of_three_le
    {width total : Nat}
    (widthAtLeastThree : 3 ≤ width)
    (totalAtLeastTwo : 2 ≤ total) :
    (∑ index : Fin (Nat.min width total),
      normalizedContribution width total index) ≤ 1 := by
  have widthPositive : 0 < width := by omega
  have basePositive : 0 < combinedAdviceBase width :=
    combinedAdviceBase_pos widthPositive
  have splitBound := normalizedContribution_sum_add_first_le
    widthPositive totalAtLeastTwo
  have positiveBound := positive_binomial_sum_le_exp
    width total (combinedAdviceBase width) basePositive
  have positiveRewrite :
      (∑ index : Fin (Nat.min width total),
          (width.choose (index.val + 1) : Real) *
            2 ^ (index.val + 1) /
              combinedAdviceBase width ^ (index.val + 1)) =
        ∑ index : Fin (Nat.min width total),
          (width.choose (index.val + 1) : Real) *
            (2 / combinedAdviceBase width) ^ (index.val + 1) := by
    apply Finset.sum_congr rfl
    intro index _
    rw [div_pow]
    rw [mul_div_assoc]
  rw [positiveRewrite] at splitBound
  have normalizedLe :
      (∑ index : Fin (Nat.min width total),
          normalizedContribution width total index) ≤
        Real.exp (2 * width / combinedAdviceBase width) - 1 -
          (width : Real) / combinedAdviceBase width := by
    linarith
  have exponentialArgument :
      2 * (width : Real) / combinedAdviceBase width ≤ 6 / 7 :=
    scaled_width_le_six_sevenths widthAtLeastThree
  have exponentialBound :
      Real.exp (2 * width / combinedAdviceBase width) ≤ 12 / 5 := by
    calc
      Real.exp (2 * width / combinedAdviceBase width) ≤
          Real.exp (6 / 7) := Real.exp_le_exp.mpr exponentialArgument
      _ ≤ 12 / 5 := exp_six_sevenths_le_twelve_fifths
  have firstLower :
      (2 / 5 : Real) ≤ width / combinedAdviceBase width :=
    two_fifths_le_width_div_combinedAdviceBase widthPositive
  linarith

private theorem normalizedContribution_sum_le_one_of_total_eq_one
    {width : Nat}
    (widthPositive : 0 < width) :
    (∑ index : Fin (Nat.min width 1),
      normalizedContribution width 1 index) ≤ 1 := by
  classical
  have minEq : Nat.min width 1 = 1 := Nat.min_eq_right widthPositive
  let first : Fin (Nat.min width 1) := ⟨0, by omega⟩
  have sumEq :
      (∑ index : Fin (Nat.min width 1),
        normalizedContribution width 1 index) =
        normalizedContribution width 1 first := by
    apply Finset.sum_eq_single first
    · intro index _ indexNe
      exfalso
      apply indexNe
      apply Fin.ext
      have below := index.isLt
      have valueZero : index.val = 0 := by omega
      simpa [first] using valueZero
    · simp
  rw [sumEq]
  simp [first, normalizedContribution,
    Nat.choose_one_right]
  have widthOne : (1 : Real) ≤ width := by exact_mod_cast widthPositive
  have basePositive : 0 < combinedAdviceBase width :=
    combinedAdviceBase_pos widthPositive
  rw [div_le_iff₀ basePositive]
  unfold combinedAdviceBase
  nlinarith

private theorem normalizedContribution_sum_le_one_width_one
    {total : Nat}
    (totalPositive : 0 < total) :
    (∑ index : Fin (Nat.min 1 total),
      normalizedContribution 1 total index) ≤ 1 := by
  classical
  have minEq : Nat.min 1 total = 1 := Nat.min_eq_left totalPositive
  let first : Fin (Nat.min 1 total) := ⟨0, by omega⟩
  have sumEq :
      (∑ index : Fin (Nat.min 1 total),
        normalizedContribution 1 total index) =
        normalizedContribution 1 total first := by
    apply Finset.sum_eq_single first
    · intro index _ indexNe
      exfalso
      apply indexNe
      apply Fin.ext
      have below := index.isLt
      have valueZero : index.val = 0 := by omega
      simpa [first] using valueZero
    · simp
  rw [sumEq]
  by_cases final : total = 1
  · subst total
    norm_num [first, normalizedContribution, combinedAdviceBase]
  · have oneNotFinal : 1 ≠ total := Ne.symm final
    norm_num [first, normalizedContribution, combinedAdviceBase, oneNotFinal]

private theorem normalizedContribution_sum_le_one_width_two
    {total : Nat}
    (totalPositive : 0 < total) :
    (∑ index : Fin (Nat.min 2 total),
      normalizedContribution 2 total index) ≤ 1 := by
  classical
  by_cases totalOne : total = 1
  · subst total
    exact normalizedContribution_sum_le_one_of_total_eq_one (by omega)
  · have totalAtLeastTwo : 2 ≤ total := by omega
    have minEq : Nat.min 2 total = 2 := Nat.min_eq_left totalAtLeastTwo
    let first : Fin (Nat.min 2 total) := ⟨0, by omega⟩
    let second : Fin (Nat.min 2 total) := ⟨1, by omega⟩
    have univEq :
        (Finset.univ : Finset (Fin (Nat.min 2 total))) =
          {first, second} := by
      ext index
      have below := index.isLt
      have cases : index.val = 0 ∨ index.val = 1 := by omega
      rcases cases with valueZero | valueOne
      · have equal : index = first := by
          apply Fin.ext
          simpa [first] using valueZero
        simp [equal]
      · have equal : index = second := by
          apply Fin.ext
          simpa [second] using valueOne
        simp [equal]
    rw [show (∑ index : Fin (Nat.min 2 total),
        normalizedContribution 2 total index) =
          normalizedContribution 2 total first +
            normalizedContribution 2 total second by
      rw [univEq]
      simp [first, second]]
    by_cases totalTwo : total = 2
    · subst total
      norm_num [first, second, normalizedContribution, combinedAdviceBase]
    · have oneNotFinal : 1 ≠ total := by omega
      have twoNotFinal : 2 ≠ total := by omega
      norm_num [first, second, normalizedContribution, combinedAdviceBase,
        oneNotFinal, twoNotFinal]

private theorem normalizedContribution_sum_le_one
    {width total : Nat}
    (widthPositive : 0 < width)
    (totalPositive : 0 < total) :
    (∑ index : Fin (Nat.min width total),
      normalizedContribution width total index) ≤ 1 := by
  by_cases totalOne : total = 1
  · subst total
    exact normalizedContribution_sum_le_one_of_total_eq_one widthPositive
  have totalAtLeastTwo : 2 ≤ total := by omega
  rcases lt_trichotomy width 2 with widthSmall | widthTwo | widthLarge
  · have widthOne : width = 1 := by omega
    subst width
    exact normalizedContribution_sum_le_one_width_one totalPositive
  · subst width
    exact normalizedContribution_sum_le_one_width_two totalPositive
  · exact normalizedContribution_sum_le_one_of_three_le
      (by omega) totalAtLeastTwo

/-- Combined block advice has at most `((5 * width - 1) / 2)^pathLength`
elements. The subtraction occurs in `Real`, and positive width makes the base
positive. -/
theorem natCard_combinedAdvice_cast_le
    (width pathLength : Nat)
    (widthPositive : 0 < width) :
    (Nat.card (CombinedAdvice width pathLength) : Real) ≤
      (((5 : Real) * width - 1) / 2) ^ pathLength := by
  change (Nat.card (CombinedAdvice width pathLength) : Real) ≤
    combinedAdviceBase width ^ pathLength
  induction pathLength using Nat.strong_induction_on with
  | h pathLength inductionHypothesis =>
      cases pathLength with
      | zero =>
          simp [CombinedAdvice]
      | succ remaining =>
          let total := remaining + 1
          have totalPositive : 0 < total := by simp [total]
          have basePositive : 0 < combinedAdviceBase width :=
            combinedAdviceBase_pos widthPositive
          have recurrence := card_combinedAdvice_succ width remaining
          have castRecurrence :
              (Nat.card (CombinedAdvice width total) : Real) =
                ∑ index : Fin (Nat.min width total),
                  if index.val = remaining then
                    (width.choose (index.val + 1) : Real) *
                      2 ^ (index.val + 1)
                  else
                    ((width.choose (index.val + 1) *
                        (2 ^ (index.val + 1) - 1) : Nat) : Real) *
                      Nat.card (CombinedAdvice width
                        (remaining - index.val)) := by
            dsimp [total]
            exact_mod_cast recurrence
          rw [castRecurrence]
          calc
            (∑ index : Fin (Nat.min width total),
                if index.val = remaining then
                  (width.choose (index.val + 1) : Real) *
                    2 ^ (index.val + 1)
                else
                  ((width.choose (index.val + 1) *
                      (2 ^ (index.val + 1) - 1) : Nat) : Real) *
                    Nat.card (CombinedAdvice width
                      (remaining - index.val))) ≤
                ∑ index : Fin (Nat.min width total),
                  normalizedContribution width total index *
                    combinedAdviceBase width ^ total := by
              apply Finset.sum_le_sum
              intro index _
              have indexLe : index.val ≤ remaining := by
                have belowTotal : index.val < total :=
                  index.isLt.trans_le (Nat.min_le_right width total)
                dsimp [total] at belowTotal
                omega
              by_cases final : index.val = remaining
              · simp only [final, ite_true]
                have lengthEq : index.val + 1 = total := by
                  simp [total, final]
                simp only [normalizedContribution, lengthEq, ite_true]
                exact (div_mul_cancel₀ _
                  (pow_ne_zero _ (ne_of_gt basePositive))).symm.le
              · simp only [final, ite_false]
                have indexLt : index.val < remaining := by omega
                have tailLt : remaining - index.val < total := by
                  simp only [total]
                  omega
                have tailBound := inductionHypothesis
                  (remaining - index.val) tailLt
                have coefficientNonnegative :
                    0 ≤ ((width.choose (index.val + 1) *
                      (2 ^ (index.val + 1) - 1) : Nat) : Real) := by
                  positivity
                have multiplied := mul_le_mul_of_nonneg_left tailBound
                  coefficientNonnegative
                have lengthNotTotal : index.val + 1 ≠ total := by
                  simp only [total]
                  omega
                simp only [normalizedContribution, lengthNotTotal, ite_false]
                calc
                  ((width.choose (index.val + 1) *
                      (2 ^ (index.val + 1) - 1) : Nat) : Real) *
                        Nat.card (CombinedAdvice width
                          (remaining - index.val)) ≤
                      ((width.choose (index.val + 1) *
                        (2 ^ (index.val + 1) - 1) : Nat) : Real) *
                          combinedAdviceBase width ^
                            (remaining - index.val) := multiplied
                  _ = ((width.choose (index.val + 1) : Real) *
                        (2 ^ (index.val + 1) - 1) /
                          combinedAdviceBase width ^ (index.val + 1)) *
                      combinedAdviceBase width ^ total := by
                    have oneLe : 1 ≤ 2 ^ (index.val + 1) :=
                      Nat.one_le_two_pow
                    rw [Nat.cast_mul, Nat.cast_sub oneLe, Nat.cast_pow]
                    norm_num
                    have exponentEq :
                        (index.val + 1) + (remaining - index.val) = total := by
                      simp only [total]
                      omega
                    have powerEq :
                        combinedAdviceBase width ^ (index.val + 1) *
                            combinedAdviceBase width ^ (remaining - index.val) =
                          combinedAdviceBase width ^ total := by
                      rw [← pow_add, exponentEq]
                    rw [← powerEq]
                    field_simp [ne_of_gt basePositive]
            _ = combinedAdviceBase width ^ total *
                (∑ index : Fin (Nat.min width total),
                  normalizedContribution width total index) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro index _
              ring
            _ ≤ combinedAdviceBase width ^ total * 1 := by
              exact mul_le_mul_of_nonneg_left
                (normalizedContribution_sum_le_one
                  widthPositive totalPositive) (by positivity)
            _ = combinedAdviceBase width ^ total := by ring

/-- `Fintype.card` form of the combined-advice cardinality bound. -/
theorem card_combinedAdvice_cast_le
    (width pathLength : Nat)
    (widthPositive : 0 < width) :
    (Fintype.card (CombinedAdvice width pathLength) : Real) ≤
      (((5 : Real) * width - 1) / 2) ^ pathLength := by
  simpa only [Nat.card_eq_fintype_card] using
    natCard_combinedAdvice_cast_le width pathLength widthPositive

end Switching
end AC0
end Algebraic
