/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Defs
public import Complexitylib.Algebraic.MassProduction.SortingSemantics.Boolean
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.FinCases

/-!
# Semantic correctness internals for Batcher sorting networks
-/

@[expose] public section

namespace Algebraic
namespace MassProduction
namespace Sorting
namespace Semantics
namespace Internal

private def threshold [LinearOrder α] (pivot value : α) : Bool :=
  decide (pivot ≤ value)

private theorem threshold_mono [LinearOrder α] (pivot : α) :
    Monotone (threshold pivot) := by
  intro first second hle
  simp only [threshold, decide_eq_true_eq, Bool.le_iff_imp]
  exact fun hpivot => hpivot.trans hle

@[simp] private theorem threshold_min [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (min first second) =
      min (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.min_eq_and, Bool.decide_and, le_min_iff]

@[simp] private theorem threshold_max [LinearOrder α]
    (pivot first second : α) :
    threshold pivot (max first second) =
      max (threshold pivot first) (threshold pivot second) := by
  simp only [threshold, Bool.max_eq_or, Bool.decide_or, le_max_iff]

private theorem SequenceBitonic.threshold [LinearOrder α] {n : ℕ}
    {sequence : Fin n → α} (hsequence : SequenceBitonic sequence)
    (pivot : α) :
    SequenceBitonic (fun i => threshold pivot (sequence i)) := by
  intro i j k l hij hjk hkl
  have h := hsequence i j k l hij hjk hkl
  constructor
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.1
  · rw [← threshold_min, ← threshold_max]
    exact threshold_mono pivot h.2

@[simp] theorem finAppend_addNat_self {n : ℕ}
    (first second : Fin n → α) (i : Fin n) :
    Fin.append first second (i.addNat n) = second i := by
  rw [show i.addNat n = Fin.natAdd n i by
    apply Fin.ext
    exact Nat.add_comm _ _, Fin.append_right]

theorem appendSequence_left_value {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α)
    (index : Fin (n + m)) (hleft : index.val < n) :
    appendSequence first second index = first ⟨index.val, hleft⟩ := by
  have heq : index = Fin.castAdd m ⟨index.val, hleft⟩ := by
    apply Fin.ext
    rfl
  calc
    appendSequence first second index =
        appendSequence first second (Fin.castAdd m ⟨index.val, hleft⟩) :=
      congrArg (appendSequence first second) heq
    _ = first ⟨index.val, hleft⟩ := Fin.append_left _ _ _

theorem appendSequence_right_value {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α)
    (index : Fin (n + m)) (hright : ¬index.val < n) :
    appendSequence first second index =
      second ⟨index.val - n, by omega⟩ := by
  let rightIndex : Fin m := ⟨index.val - n, by omega⟩
  have heq : index = Fin.natAdd n rightIndex := by
    apply Fin.ext
    change index.val = n + (index.val - n)
    omega
  calc
    appendSequence first second index =
        appendSequence first second (Fin.natAdd n rightIndex) :=
      congrArg (appendSequence first second) heq
    _ = second rightIndex := Fin.append_right _ _ _
    _ = second ⟨index.val - n, by omega⟩ := by rfl

private def selectFour {n : ℕ} (i j k l : Fin n) : Fin 4 → Fin n :=
  ![i, j, k, l]

@[simp] private theorem selectFour_zero {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 0 = i := rfl

@[simp] private theorem selectFour_one {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 1 = j := rfl

@[simp] private theorem selectFour_two {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 2 = k := rfl

@[simp] private theorem selectFour_three {n : ℕ} (i j k l : Fin n) :
    selectFour i j k l 3 = l := rfl

private theorem selectFour_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (selectFour i j k l) := by
  intro first second hlt
  fin_cases first <;> fin_cases second <;>
    simp_all [selectFour] <;> omega

private def embedEight {n : ℕ} (i j k l : Fin n) : Fin 8 → Fin (n + n) :=
  fun index =>
    if hleft : index.val < 4 then
      Fin.castAdd n (selectFour i j k l ⟨index.val, hleft⟩)
    else
      Fin.natAdd n
        (selectFour i j k l ⟨index.val - 4, by omega⟩)

private theorem embedEight_strictMono {n : ℕ} (i j k l : Fin n)
    (hij : i < j) (hjk : j < k) (hkl : k < l) :
    StrictMono (embedEight i j k l) := by
  intro first second hlt
  unfold embedEight
  split_ifs with hfirst hsecond
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        (selectFour i j k l ⟨second.val, hsecond⟩).val
    apply selectFour_strictMono i j k l hij hjk hkl
    exact hlt
  · change
      (selectFour i j k l ⟨first.val, hfirst⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by omega⟩).val
    have hbound := (selectFour i j k l ⟨first.val, hfirst⟩).isLt
    omega
  · exfalso
    omega
  · change
      n + (selectFour i j k l ⟨first.val - 4, by omega⟩).val <
        n + (selectFour i j k l ⟨second.val - 4, by omega⟩).val
    apply Nat.add_lt_add_left
    apply selectFour_strictMono i j k l hij hjk hkl
    simp only [Fin.mk_lt_mk]
    omega

private theorem SequenceBitonic.comp_strictMono
    [LinearOrder α] {n m : ℕ} {sequence : Fin n → α}
    (hsequence : SequenceBitonic sequence) {embed : Fin m → Fin n}
    (hembed : StrictMono embed) :
    SequenceBitonic (fun index => sequence (embed index)) := by
  intro i j k l hij hjk hkl
  exact hsequence _ _ _ _ (hembed hij) (hembed hjk) (hembed hkl)

private theorem localEight_bitonic [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : SequenceBitonic (appendSequence first second))
    (i j k l : Fin n) (hij : i < j) (hjk : j < k) (hkl : k < l) :
    SequenceBitonic
      ![first i, first j, first k, first l,
        second i, second j, second k, second l] := by
  have hselected := SequenceBitonic.comp_strictMono hsequence
    (embedEight_strictMono i j k l hij hjk hkl)
  have hequal :
      (fun index => appendSequence first second (embedEight i j k l index)) =
        ![first i, first j, first k, first l,
          second i, second j, second k, second l] := by
    funext index
    fin_cases index <;>
      simp [appendSequence, embedEight, selectFour]
  rw [hequal] at hselected
  exact hselected

theorem pointwiseMin_bitonic [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : SequenceBitonic (appendSequence first second)) :
    SequenceBitonic (pointwiseMin first second) := by
  intro i j k l hij hjk hkl
  let localSequence : Fin 8 → α :=
    ![first i, first j, first k, first l,
      second i, second j, second k, second l]
  have hlocal : SequenceBitonic localSequence :=
    localEight_bitonic first second hsequence
      i j k l hij hjk hkl
  have hhalf (pivot : α) :
      boolHalfMin (fun index => threshold pivot (localSequence index)) =
        fun index => threshold pivot
          (pointwiseMin first second (selectFour i j k l index)) := by
    funext index
    fin_cases index <;>
      simp [boolHalfMin, localSequence, pointwiseMin, selectFour]
  constructor
  · let pivot := min (pointwiseMin first second i)
      (pointwiseMin first second k)
    have hbool := (boolBitonicHalves _
      (SequenceBitonic.threshold hlocal pivot)).1
    have hineq := hbool (0 : Fin 4) 1 2 3
      (by omega) (by omega) (by omega)
    by_contra hnot
    have hpivot : threshold pivot pivot = true := by simp [threshold]
    have hright : threshold pivot
        (max (pointwiseMin first second j)
          (pointwiseMin first second l)) = false := by
      simp only [threshold, decide_eq_false_iff_not]
      exact hnot
    rw [hhalf pivot] at hineq
    simp only [selectFour_zero, selectFour_one, selectFour_two,
      selectFour_three] at hineq
    have hfirst := hineq.1
    rw [← threshold_min, ← threshold_max] at hfirst
    rw [hpivot, hright] at hfirst
    exact Bool.noConfusion ((Bool.le_iff_imp.mp hfirst) rfl)
  · let pivot := min (pointwiseMin first second j)
      (pointwiseMin first second l)
    have hbool := (boolBitonicHalves _
      (SequenceBitonic.threshold hlocal pivot)).1
    have hineq := hbool (0 : Fin 4) 1 2 3
      (by omega) (by omega) (by omega)
    by_contra hnot
    have hpivot : threshold pivot pivot = true := by simp [threshold]
    have hright : threshold pivot
        (max (pointwiseMin first second i)
          (pointwiseMin first second k)) = false := by
      simp only [threshold, decide_eq_false_iff_not]
      exact hnot
    rw [hhalf pivot] at hineq
    simp only [selectFour_zero, selectFour_one, selectFour_two,
      selectFour_three] at hineq
    have hsecond := hineq.2
    rw [← threshold_min, ← threshold_max] at hsecond
    rw [hpivot, hright] at hsecond
    exact Bool.noConfusion ((Bool.le_iff_imp.mp hsecond) rfl)

theorem pointwiseMax_bitonic [LinearOrder α] {n : ℕ}
    (first second : Fin n → α)
    (hsequence : SequenceBitonic (appendSequence first second)) :
    SequenceBitonic (pointwiseMax first second) := by
  intro i j k l hij hjk hkl
  let localSequence : Fin 8 → α :=
    ![first i, first j, first k, first l,
      second i, second j, second k, second l]
  have hlocal : SequenceBitonic localSequence :=
    localEight_bitonic first second hsequence
      i j k l hij hjk hkl
  have hhalf (pivot : α) :
      boolHalfMax (fun index => threshold pivot (localSequence index)) =
        fun index => threshold pivot
          (pointwiseMax first second (selectFour i j k l index)) := by
    funext index
    fin_cases index <;>
      simp [boolHalfMax, localSequence, pointwiseMax, selectFour]
  constructor
  · let pivot := min (pointwiseMax first second i)
      (pointwiseMax first second k)
    have hbool := (boolBitonicHalves _
      (SequenceBitonic.threshold hlocal pivot)).2
    have hineq := hbool (0 : Fin 4) 1 2 3
      (by omega) (by omega) (by omega)
    by_contra hnot
    have hpivot : threshold pivot pivot = true := by simp [threshold]
    have hright : threshold pivot
        (max (pointwiseMax first second j)
          (pointwiseMax first second l)) = false := by
      simp only [threshold, decide_eq_false_iff_not]
      exact hnot
    rw [hhalf pivot] at hineq
    simp only [selectFour_zero, selectFour_one, selectFour_two,
      selectFour_three] at hineq
    have hfirst := hineq.1
    rw [← threshold_min, ← threshold_max] at hfirst
    rw [hpivot, hright] at hfirst
    exact Bool.noConfusion ((Bool.le_iff_imp.mp hfirst) rfl)
  · let pivot := min (pointwiseMax first second j)
      (pointwiseMax first second l)
    have hbool := (boolBitonicHalves _
      (SequenceBitonic.threshold hlocal pivot)).2
    have hineq := hbool (0 : Fin 4) 1 2 3
      (by omega) (by omega) (by omega)
    by_contra hnot
    have hpivot : threshold pivot pivot = true := by simp [threshold]
    have hright : threshold pivot
        (max (pointwiseMax first second i)
          (pointwiseMax first second k)) = false := by
      simp only [threshold, decide_eq_false_iff_not]
      exact hnot
    rw [hhalf pivot] at hineq
    simp only [selectFour_zero, selectFour_one, selectFour_two,
      selectFour_three] at hineq
    have hsecond := hineq.2
    rw [← threshold_min, ← threshold_max] at hsecond
    rw [hpivot, hright] at hsecond
    exact Bool.noConfusion ((Bool.le_iff_imp.mp hsecond) rfl)

theorem pointwiseMin_allLE_pointwiseMax
    [LinearOrder α] {n : ℕ} (first second : Fin n → α)
    (hsequence : SequenceBitonic (appendSequence first second)) :
    SequenceAllLE (pointwiseMin first second)
      (pointwiseMax first second) := by
  intro i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have h := hsequence (Fin.castAdd n i) (Fin.castAdd n j)
        (Fin.natAdd n i) (Fin.natAdd n j)
        hij (by change j.val < n + i.val; omega)
        (by change n + i.val < n + j.val; omega)
    simpa [appendSequence, pointwiseMin, pointwiseMax] using h.1
  · subst j
    exact (min_le_left _ _).trans (le_max_left _ _)
  · have h := hsequence (Fin.castAdd n j) (Fin.castAdd n i)
        (Fin.natAdd n j) (Fin.natAdd n i)
        hij (by change i.val < n + j.val; omega)
        (by change n + j.val < n + i.val; omega)
    simpa [appendSequence, pointwiseMin, pointwiseMax] using h.2

theorem increasing_append_decreasing_bitonic
    [LinearOrder α] {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α)
    (hfirst : SequenceIncreasing first)
    (hsecond : SequenceDecreasing second) :
    SequenceBitonic (appendSequence first second) := by
  intro i j k l hij hjk hkl
  by_cases hk : k.val < n
  · have hi : i.val < n := by omega
    have hj : j.val < n := by omega
    by_cases hl : l.val < n
    · rw [appendSequence_left_value first second i hi,
          appendSequence_left_value first second j hj,
          appendSequence_left_value first second k hk,
          appendSequence_left_value first second l hl]
      have hfi := hfirst (⟨i.val, hi⟩ : Fin n) ⟨j.val, hj⟩ hij
      have hfj := hfirst (⟨j.val, hj⟩ : Fin n) ⟨k.val, hk⟩ hjk
      constructor
      · exact (min_le_left _ _).trans (hfi.trans (le_max_left _ _))
      · exact (min_le_left _ _).trans (hfj.trans (le_max_right _ _))
    · rw [appendSequence_left_value first second i hi,
          appendSequence_left_value first second j hj,
          appendSequence_left_value first second k hk,
          appendSequence_right_value first second l hl]
      have hfi := hfirst (⟨i.val, hi⟩ : Fin n) ⟨j.val, hj⟩ hij
      have hfj := hfirst (⟨j.val, hj⟩ : Fin n) ⟨k.val, hk⟩ hjk
      constructor
      · exact (min_le_left _ _).trans (hfi.trans (le_max_left _ _))
      · exact (min_le_left _ _).trans (hfj.trans (le_max_right _ _))
  · by_cases hj : j.val < n
    · have hi : i.val < n := by omega
      have hkg : k.val - n < m := by omega
      have hlg : l.val - n < m := by omega
      rw [appendSequence_left_value first second i hi,
          appendSequence_left_value first second j hj,
          appendSequence_right_value first second k hk,
          appendSequence_right_value first second l (by omega)]
      have hfi := hfirst (⟨i.val, hi⟩ : Fin n) ⟨j.val, hj⟩ hij
      have hkl : (⟨k.val - n, hkg⟩ : Fin m) <
          ⟨l.val - n, hlg⟩ := by
        change k.val - n < l.val - n
        omega
      have hgl := hsecond _ _ hkl
      constructor
      · exact (min_le_left _ _).trans (hfi.trans (le_max_left _ _))
      · exact (min_le_right _ _).trans (hgl.trans (le_max_right _ _))
    · have hjg : j.val - n < m := by omega
      have hkg : k.val - n < m := by omega
      have hlg : l.val - n < m := by omega
      have hjk' : (⟨j.val - n, hjg⟩ : Fin m) <
          ⟨k.val - n, hkg⟩ := by
        change j.val - n < k.val - n
        omega
      have hkl' : (⟨k.val - n, hkg⟩ : Fin m) <
          ⟨l.val - n, hlg⟩ := by
        change k.val - n < l.val - n
        omega
      have hgj := hsecond _ _ hjk'
      have hgk := hsecond _ _ hkl'
      by_cases hi : i.val < n
      · rw [appendSequence_left_value first second i hi,
            appendSequence_right_value first second j hj,
            appendSequence_right_value first second k hk,
            appendSequence_right_value first second l (by omega)]
        constructor
        · exact (min_le_right _ _).trans (hgj.trans (le_max_left _ _))
        · exact (min_le_right _ _).trans (hgk.trans (le_max_right _ _))
      · rw [appendSequence_right_value first second i hi,
            appendSequence_right_value first second j hj,
            appendSequence_right_value first second k hk,
            appendSequence_right_value first second l (by omega)]
        constructor
        · exact (min_le_right _ _).trans (hgj.trans (le_max_left _ _))
        · exact (min_le_right _ _).trans (hgk.trans (le_max_right _ _))

@[simp] theorem recordFirstHalf_joinRecordHalves {depth : ℕ}
    (first second : Fin (networkRecords depth) → α) :
    recordFirstHalf (joinRecordHalves first second) = first := by
  funext index
  exact Fin.append_left _ _ _

@[simp] theorem recordSecondHalf_joinRecordHalves {depth : ℕ}
    (first second : Fin (networkRecords depth) → α) :
    recordSecondHalf (joinRecordHalves first second) = second := by
  funext index
  exact Fin.append_right _ _ _

theorem joinRecordHalves_split {depth : ℕ}
    (input : Fin (networkRecords (depth + 1)) → α) :
    joinRecordHalves (recordFirstHalf input) (recordSecondHalf input) = input := by
  exact Fin.append_castAdd_natAdd

theorem increasing_append [Preorder α] {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α)
    (hfirst : SequenceIncreasing first)
    (hsecond : SequenceIncreasing second)
    (hcross : SequenceAllLE first second) :
    SequenceIncreasing (appendSequence first second) := by
  intro i j hij
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · rw [appendSequence_left_value first second i hi,
          appendSequence_left_value first second j hj]
      exact hfirst _ _ hij
    · rw [appendSequence_left_value first second i hi,
          appendSequence_right_value first second j hj]
      exact hcross _ _
  · have hj : ¬j.val < n := by omega
    rw [appendSequence_right_value first second i hi,
        appendSequence_right_value first second j hj]
    apply hsecond
    change i.val - n < j.val - n
    omega

theorem decreasing_append [Preorder α] {n m : ℕ}
    (first : Fin n → α) (second : Fin m → α)
    (hfirst : SequenceDecreasing first)
    (hsecond : SequenceDecreasing second)
    (hcross : SequenceAllLE second first) :
    SequenceDecreasing (appendSequence first second) := by
  intro i j hij
  by_cases hj : j.val < n
  · have hi : i.val < n := by omega
    rw [appendSequence_left_value first second i hi,
        appendSequence_left_value first second j hj]
    exact hfirst _ _ hij
  · by_cases hi : i.val < n
    · rw [appendSequence_left_value first second i hi,
          appendSequence_right_value first second j hj]
      exact hcross _ _
    · rw [appendSequence_right_value first second i hi,
          appendSequence_right_value first second j hj]
      apply hsecond
      change i.val - n < j.val - n
      omega

theorem append_rangeContained {n m n' m' : ℕ}
    {first : Fin n → α} {second : Fin m → α}
    {firstInput : Fin n' → α} {secondInput : Fin m' → α}
    (hfirst : SequenceRangeContained first firstInput)
    (hsecond : SequenceRangeContained second secondInput) :
    SequenceRangeContained (appendSequence first second)
      (appendSequence firstInput secondInput) := by
  intro output
  refine Fin.addCases (fun i => ?_) (fun i => ?_) output
  · obtain ⟨source, hsource⟩ := hfirst i
    exact ⟨Fin.castAdd m' source, by
      simpa [appendSequence] using hsource⟩
  · obtain ⟨source, hsource⟩ := hsecond i
    exact ⟨Fin.natAdd n' source, by
      simpa [appendSequence] using hsource⟩

theorem append_rangeContained_same {n m k : ℕ}
    {first : Fin n → α} {second : Fin m → α} {input : Fin k → α}
    (hfirst : SequenceRangeContained first input)
    (hsecond : SequenceRangeContained second input) :
    SequenceRangeContained (appendSequence first second) input := by
  intro output
  refine Fin.addCases (fun i => ?_) (fun i => ?_) output
  · simpa [appendSequence] using hfirst i
  · simpa [appendSequence] using hsecond i

theorem pointwiseMin_rangeContained [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) :
    SequenceRangeContained (pointwiseMin first second)
      (appendSequence first second) := by
  intro output
  by_cases hle : first output ≤ second output
  · exact ⟨Fin.castAdd n output, by
      simp [pointwiseMin, appendSequence, min_eq_left hle]⟩
  · have hle' : second output ≤ first output := le_of_not_ge hle
    exact ⟨Fin.natAdd n output, by
      simp [pointwiseMin, appendSequence, min_eq_right hle']⟩

theorem pointwiseMax_rangeContained [LinearOrder α] {n : ℕ}
    (first second : Fin n → α) :
    SequenceRangeContained (pointwiseMax first second)
      (appendSequence first second) := by
  intro output
  by_cases hle : first output ≤ second output
  · exact ⟨Fin.natAdd n output, by
      simp [pointwiseMax, appendSequence, max_eq_right hle]⟩
  · have hle' : second output ≤ first output := le_of_not_ge hle
    exact ⟨Fin.castAdd n output, by
      simp [pointwiseMax, appendSequence, max_eq_left hle']⟩

theorem orderedCompareLayer_rangeContained [LinearOrder α]
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    SequenceRangeContained (orderedCompareLayer depth ascending input) input := by
  let first := recordFirstHalf input
  let second := recordSecondHalf input
  have hsplit : appendSequence first second = input :=
    joinRecordHalves_split input
  cases ascending with
  | false =>
      refine (append_rangeContained_same
        (pointwiseMax_rangeContained first second)
        (pointwiseMin_rangeContained first second)).trans ?_
      intro index
      exact ⟨index, congrFun hsplit index⟩
  | true =>
      refine (append_rangeContained_same
        (pointwiseMin_rangeContained first second)
        (pointwiseMax_rangeContained first second)).trans ?_
      intro index
      exact ⟨index, congrFun hsplit index⟩

theorem orderedBitonicMerge_rangeContained [LinearOrder α]
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    SequenceRangeContained (orderedBitonicMerge depth ascending input) input := by
  induction depth generalizing ascending with
  | zero =>
      intro output
      exact ⟨output, rfl⟩
  | succ depth ih =>
      let compared := orderedCompareLayer depth ascending input
      let first := recordFirstHalf compared
      let second := recordSecondHalf compared
      have hrecursive := append_rangeContained
        (ih ascending first) (ih ascending second)
      have hsplit : appendSequence first second = compared :=
        joinRecordHalves_split compared
      have htoCompared : SequenceRangeContained
          (joinRecordHalves
            (orderedBitonicMerge depth ascending first)
            (orderedBitonicMerge depth ascending second)) compared := by
        refine hrecursive.trans ?_
        intro index
        exact ⟨index, congrFun hsplit index⟩
      have htoInput := htoCompared.trans
        (orderedCompareLayer_rangeContained depth ascending input)
      simpa only [orderedBitonicMerge, compared, first, second] using htoInput

theorem orderedBitonicMerge_allLE [LinearOrder α] {depth : ℕ}
    (ascending : Bool)
    (first second : Fin (networkRecords depth) → α)
    (hcross : SequenceAllLE first second) :
    SequenceAllLE (orderedBitonicMerge depth ascending first)
      (orderedBitonicMerge depth ascending second) := by
  intro i j
  obtain ⟨sourceFirst, hfirst⟩ :=
    orderedBitonicMerge_rangeContained depth ascending first i
  obtain ⟨sourceSecond, hsecond⟩ :=
    orderedBitonicMerge_rangeContained depth ascending second j
  rw [hfirst, hsecond]
  exact hcross sourceFirst sourceSecond

theorem orderedBitonicMerge_sorted [LinearOrder α]
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α)
    (hbitonic : SequenceBitonic input) :
    SequenceSorted ascending (orderedBitonicMerge depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
      cases ascending <;>
        simp only [SequenceSorted, Bool.false_eq_true, ↓reduceIte,
          orderedBitonicMerge, SequenceIncreasing, SequenceDecreasing,
          networkRecords] <;>
        intro i j hij <;> omega
  | succ depth ih =>
      let first := recordFirstHalf input
      let second := recordSecondHalf input
      have hsplit : appendSequence first second = input :=
        joinRecordHalves_split input
      have hpairs : SequenceBitonic (appendSequence first second) := by
        rw [hsplit]
        exact hbitonic
      have hmin := pointwiseMin_bitonic first second hpairs
      have hmax := pointwiseMax_bitonic first second hpairs
      have hcross := pointwiseMin_allLE_pointwiseMax
        first second hpairs
      cases ascending with
      | false =>
          have hfirst := ih false (pointwiseMax first second) hmax
          have hsecond := ih false (pointwiseMin first second) hmin
          have hmergedCross := orderedBitonicMerge_allLE false
            (pointwiseMin first second) (pointwiseMax first second) hcross
          have hjoined := decreasing_append
            (orderedBitonicMerge depth false (pointwiseMax first second))
            (orderedBitonicMerge depth false (pointwiseMin first second))
            hfirst hsecond hmergedCross
          simpa only [SequenceSorted, Bool.false_eq_true, ↓reduceIte,
            orderedBitonicMerge, orderedCompareLayer,
            recordFirstHalf_joinRecordHalves,
            recordSecondHalf_joinRecordHalves,
            networkRecords_succ, first, second,
            appendSequence_eq_joinRecordHalves] using hjoined
      | true =>
          have hfirst := ih true (pointwiseMin first second) hmin
          have hsecond := ih true (pointwiseMax first second) hmax
          have hmergedCross := orderedBitonicMerge_allLE true
            (pointwiseMin first second) (pointwiseMax first second) hcross
          have hjoined := increasing_append
            (orderedBitonicMerge depth true (pointwiseMin first second))
            (orderedBitonicMerge depth true (pointwiseMax first second))
            hfirst hsecond hmergedCross
          simpa only [SequenceSorted, ↓reduceIte, orderedBitonicMerge,
            orderedCompareLayer, recordFirstHalf_joinRecordHalves,
            recordSecondHalf_joinRecordHalves,
            networkRecords_succ, first, second,
            appendSequence_eq_joinRecordHalves] using hjoined

theorem orderedBitonicSort_sorted [LinearOrder α]
    (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    SequenceSorted ascending (orderedBitonicSort depth ascending input) := by
  induction depth generalizing ascending with
  | zero =>
      cases ascending <;>
        simp only [SequenceSorted, Bool.false_eq_true, ↓reduceIte,
          orderedBitonicSort, SequenceIncreasing, SequenceDecreasing,
          networkRecords] <;>
        intro i j hij <;> omega
  | succ depth ih =>
      let first := recordFirstHalf input
      let second := recordSecondHalf input
      have hfirst : SequenceIncreasing (orderedBitonicSort depth true first) :=
        by simpa only [SequenceSorted, Bool.true_eq, ↓reduceIte] using
          ih true first
      have hsecond : SequenceDecreasing
          (orderedBitonicSort depth false second) := by
        simpa only [SequenceSorted, Bool.false_eq_true, ↓reduceIte] using
          ih false second
      have hprepared := increasing_append_decreasing_bitonic
        (orderedBitonicSort depth true first)
        (orderedBitonicSort depth false second) hfirst hsecond
      have hmerged := orderedBitonicMerge_sorted (depth + 1)
        ascending
        (joinRecordHalves
          (orderedBitonicSort depth true first)
          (orderedBitonicSort depth false second)) hprepared
      simpa only [orderedBitonicSort, first, second] using hmerged

private noncomputable def keyedSourceRight [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (pair : Fin (networkRecords depth)) : Prop :=
  let shouldSwap :=
    key (input (pair.addNat (networkRecords depth))) <
      key (input (Fin.castAdd (networkRecords depth) pair))
  if ascending then shouldSwap else ¬shouldSwap

private noncomputable instance instDecidableKeyedSourceRight
    [LinearOrder κ] (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (pair : Fin (networkRecords depth)) :
    Decidable (keyedSourceRight key depth ascending input pair) :=
  Classical.propDecidable _

private theorem keyedCompareSource_left [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (pair : Fin (networkRecords depth)) :
    keyedCompareSource key depth ascending input
        (Fin.castAdd (networkRecords depth) pair) =
      if keyedSourceRight key depth ascending input pair then
        pair.addNat (networkRecords depth)
      else Fin.castAdd (networkRecords depth) pair := by
  unfold keyedCompareSource
  dsimp only
  have hleft :
      (Fin.castAdd (networkRecords depth) pair).val <
        networkRecords depth := pair.isLt
  rw [dite_eq_left hleft]
  unfold keyedSourceRight
  rw [Fin.natAdd_eq_addNat]
  congr 1

private theorem keyedCompareSource_right [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α)
    (pair : Fin (networkRecords depth)) :
    keyedCompareSource key depth ascending input
        (pair.addNat (networkRecords depth)) =
      if keyedSourceRight key depth ascending input pair then
        Fin.castAdd (networkRecords depth) pair
      else pair.addNat (networkRecords depth) := by
  unfold keyedCompareSource keyedSourceRight
  simp [networkRecords_succ]

private theorem keyedCompareSource_involutive [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    Function.Involutive (keyedCompareSource key depth ascending input) := by
  intro output
  refine Fin.addCases (fun pair => ?_) (fun pair => ?_) output
  · rw [keyedCompareSource_left]
    by_cases hsource :
      keyedSourceRight key depth ascending input pair
    · rw [ite_eq_left hsource, keyedCompareSource_right, ite_eq_left hsource]
    · rw [ite_eq_right hsource, keyedCompareSource_left, ite_eq_right hsource]
  · rw [Fin.natAdd_eq_addNat, keyedCompareSource_right]
    by_cases hsource :
      keyedSourceRight key depth ascending input pair
    · rw [ite_eq_left hsource, keyedCompareSource_left, ite_eq_left hsource]
    · rw [ite_eq_right hsource, keyedCompareSource_right, ite_eq_right hsource]

theorem keyedCompareLayer_permutes [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    SequencePermutes (keyedCompareLayer key depth ascending input) input := by
  let source := keyedCompareSource key depth ascending input
  have hinvolutive : Function.Involutive source :=
    keyedCompareSource_involutive key depth ascending input
  let permutation : Equiv.Perm (Fin (networkRecords (depth + 1))) :=
    { toFun := source
      invFun := source
      left_inv := hinvolutive
      right_inv := hinvolutive }
  have hfunction : keyedCompareLayer key depth ascending input =
      input ∘ permutation := rfl
  unfold SequencePermutes
  rw [hfunction]
  exact permutation.ofFn_comp_perm input

theorem keyedBitonicMerge_permutes [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    SequencePermutes (keyedBitonicMerge key depth ascending input) input := by
  induction depth generalizing ascending with
  | zero => exact SequencePermutes.refl input
  | succ depth ih =>
      let compared := keyedCompareLayer key depth ascending input
      let first := recordFirstHalf compared
      let second := recordSecondHalf compared
      have hrecursive := SequencePermutes.append
        (ih ascending first) (ih ascending second)
      have hsplit : joinRecordHalves first second = compared :=
        Fin.append_castAdd_natAdd
      have htoCompared : SequencePermutes
          (joinRecordHalves
            (keyedBitonicMerge key depth ascending first)
            (keyedBitonicMerge key depth ascending second)) compared := by
        rw [← hsplit]
        exact hrecursive
      have hresult := htoCompared.trans
        (keyedCompareLayer_permutes key depth ascending input)
      simpa only [keyedBitonicMerge, compared, first, second] using hresult

theorem keyedBitonicSort_permutes [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    SequencePermutes (keyedBitonicSort key depth ascending input) input := by
  induction depth generalizing ascending with
  | zero => exact SequencePermutes.refl input
  | succ depth ih =>
      let first := recordFirstHalf input
      let second := recordSecondHalf input
      let prepared := joinRecordHalves
        (keyedBitonicSort key depth true first)
        (keyedBitonicSort key depth false second)
      have hprepared : SequencePermutes prepared input := by
        have hrecursive := SequencePermutes.append
          (ih true first) (ih false second)
        have hsplit : joinRecordHalves first second = input :=
          Fin.append_castAdd_natAdd
        rw [← hsplit]
        exact hrecursive
      have hmerge := keyedBitonicMerge_permutes key (depth + 1)
        ascending prepared
      have hresult := hmerge.trans hprepared
      simpa only [keyedBitonicSort, prepared, first, second] using hresult

private theorem key_keyedCompareLayer [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords (depth + 1)) → α) :
    (fun output => key (keyedCompareLayer key depth ascending input output)) =
      orderedCompareLayer depth ascending (fun index => key (input index)) := by
  funext output
  refine Fin.addCases (fun pair => ?_) (fun pair => ?_) output
  · unfold keyedCompareLayer
    rw [keyedCompareSource_left]
    cases ascending with
    | false =>
        by_cases hswap :
          key (input (pair.addNat (networkRecords depth))) <
            key (input (Fin.castAdd (networkRecords depth) pair))
        · simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMax, max_eq_left hswap.le]
        · have hle := le_of_not_gt hswap
          simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMax, max_eq_right hle]
    | true =>
        by_cases hswap :
          key (input (pair.addNat (networkRecords depth))) <
            key (input (Fin.castAdd (networkRecords depth) pair))
        · simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMin, min_eq_right hswap.le]
        · have hle := le_of_not_gt hswap
          simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMin, min_eq_left hle]
  · unfold keyedCompareLayer
    rw [Fin.natAdd_eq_addNat, keyedCompareSource_right]
    cases ascending with
    | false =>
        by_cases hswap :
          key (input (pair.addNat (networkRecords depth))) <
            key (input (Fin.castAdd (networkRecords depth) pair))
        · simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMin, min_eq_right hswap.le]
        · have hle := le_of_not_gt hswap
          simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMin, min_eq_left hle]
    | true =>
        by_cases hswap :
          key (input (pair.addNat (networkRecords depth))) <
            key (input (Fin.castAdd (networkRecords depth) pair))
        · simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMax, max_eq_left hswap.le]
        · have hle := le_of_not_gt hswap
          simp [keyedSourceRight, hswap, orderedCompareLayer,
            joinRecordHalves, recordFirstHalf, recordSecondHalf,
            pointwiseMax, max_eq_right hle]

private theorem key_joinRecordHalves (key : α → κ) {depth : ℕ}
    (first second : Fin (networkRecords depth) → α) :
    (fun output => key (joinRecordHalves first second output)) =
      joinRecordHalves (fun output => key (first output))
        (fun output => key (second output)) := by
  funext output
  refine Fin.addCases (fun i => ?_) (fun i => ?_) output <;>
    simp [joinRecordHalves]

private theorem key_keyedBitonicMerge [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    (fun output => key (keyedBitonicMerge key depth ascending input output)) =
      orderedBitonicMerge depth ascending (fun index => key (input index)) := by
  induction depth generalizing ascending with
  | zero => rfl
  | succ depth ih =>
      let compared := keyedCompareLayer key depth ascending input
      let orderedCompared :=
        orderedCompareLayer depth ascending (fun index => key (input index))
      have hcompared : (fun index => key (compared index)) = orderedCompared :=
        key_keyedCompareLayer key depth ascending input
      have hfirst :
          (fun index => key (recordFirstHalf compared index)) =
            recordFirstHalf orderedCompared := by
        funext index
        exact congrFun hcompared (Fin.castAdd (networkRecords depth) index)
      have hsecond :
          (fun index => key (recordSecondHalf compared index)) =
            recordSecondHalf orderedCompared := by
        funext index
        exact congrFun hcompared (Fin.natAdd (networkRecords depth) index)
      have hleft := ih ascending (recordFirstHalf compared)
      have hright := ih ascending (recordSecondHalf compared)
      rw [hfirst] at hleft
      rw [hsecond] at hright
      rw [show (fun output =>
          key (keyedBitonicMerge key (depth + 1) ascending input output)) =
          fun output => key (joinRecordHalves
            (keyedBitonicMerge key depth ascending (recordFirstHalf compared))
            (keyedBitonicMerge key depth ascending (recordSecondHalf compared))
            output) by rfl]
      rw [key_joinRecordHalves, hleft, hright]
      rfl

theorem key_keyedBitonicSort [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    (fun output => key (keyedBitonicSort key depth ascending input output)) =
      orderedBitonicSort depth ascending (fun index => key (input index)) := by
  induction depth generalizing ascending with
  | zero => rfl
  | succ depth ih =>
      let first := recordFirstHalf input
      let second := recordSecondHalf input
      let prepared := joinRecordHalves
        (keyedBitonicSort key depth true first)
        (keyedBitonicSort key depth false second)
      let orderedPrepared := joinRecordHalves
        (orderedBitonicSort depth true (fun index => key (first index)))
        (orderedBitonicSort depth false (fun index => key (second index)))
      have hprepared : (fun index => key (prepared index)) = orderedPrepared := by
        dsimp only [prepared, orderedPrepared]
        rw [key_joinRecordHalves, ih true first, ih false second]
      have hmerge := key_keyedBitonicMerge key (depth + 1)
        ascending prepared
      rw [hprepared] at hmerge
      have hfirstKey : (fun index => key (first index)) =
          recordFirstHalf (fun index => key (input index)) := rfl
      have hsecondKey : (fun index => key (second index)) =
          recordSecondHalf (fun index => key (input index)) := rfl
      dsimp only [orderedPrepared] at hmerge
      rw [hfirstKey, hsecondKey] at hmerge
      simpa only [keyedBitonicSort, orderedBitonicSort, prepared,
        first, second] using hmerge

theorem keyedBitonicSort_sorted [LinearOrder κ]
    (key : α → κ) (depth : ℕ) (ascending : Bool)
    (input : Fin (networkRecords depth) → α) :
    SequenceSorted ascending
      (fun output => key (keyedBitonicSort key depth ascending input output)) := by
  rw [key_keyedBitonicSort]
  exact orderedBitonicSort_sorted depth ascending _

end Internal
end Semantics
end Sorting
end MassProduction
end Algebraic
