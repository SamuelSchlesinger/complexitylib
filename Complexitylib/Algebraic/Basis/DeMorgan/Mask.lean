/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Operations

/-!
# Sharp native gate bounds for input subcube indicators

Positive literals are collected in one conjunction and negative literals in
one negated disjunction. A nonempty mask on `k` input coordinates, or its
complement, therefore needs at most `k` native gates.
-/

@[expose] public section

namespace Algebraic.DeMorgan

/-- Conjunction of selected positive input literals. -/
def allInputs (coordinates : Finset (Fin n)) : ScalarFunction Bool n :=
  fun input => decide (∀ i ∈ coordinates, input i = true)

/-- Disjunction of selected positive input literals. -/
def anyInput (coordinates : Finset (Fin n)) : ScalarFunction Bool n :=
  fun input => decide (∃ i ∈ coordinates, input i = true)

/-- A nonempty conjunction of `k` inputs needs at most `k-1` gates. -/
theorem complexity_allInputs_add_one_le (coordinates : Finset (Fin n))
    (nonempty : coordinates.Nonempty) : complexity (allInputs coordinates) + 1 ≤ coordinates.card := by
  induction coordinates using Finset.induction_on with
  | empty => simp at nonempty
  | @insert i coordinates absent ih =>
    by_cases empty : coordinates = ∅
    · subst coordinates
      have identity : allInputs {i} = fun input => input i := by
        funext input
        simp [allInputs]
      simp [identity]
    · have prior := ih (Finset.nonempty_iff_ne_empty.mpr empty)
      have identity : allInputs (insert i coordinates) =
          fun input => input i && allInputs coordinates input := by
        funext input
        simp [allInputs]
      have bound := complexity_and_le (fun input => input i) (allInputs coordinates)
      rw [← identity, complexity_input] at bound
      rw [Finset.card_insert_of_notMem absent]
      omega

/-- A nonempty disjunction of `k` inputs needs at most `k-1` gates. -/
theorem complexity_anyInput_add_one_le (coordinates : Finset (Fin n))
    (nonempty : coordinates.Nonempty) : complexity (anyInput coordinates) + 1 ≤ coordinates.card := by
  induction coordinates using Finset.induction_on with
  | empty => simp at nonempty
  | @insert i coordinates absent ih =>
    by_cases empty : coordinates = ∅
    · subst coordinates
      have identity : anyInput {i} = fun input => input i := by
        funext input
        simp [anyInput]
      simp [identity]
    · have prior := ih (Finset.nonempty_iff_ne_empty.mpr empty)
      have identity : anyInput (insert i coordinates) =
          fun input => input i || anyInput coordinates input := by
        funext input
        simp [anyInput]
      have bound := complexity_or_le (fun input => input i) (anyInput coordinates)
      rw [← identity, complexity_input] at bound
      rw [Finset.card_insert_of_notMem absent]
      omega

/-- Output `value` exactly on inputs matching the specified coordinates. -/
def mask (coordinates : Finset (Fin n)) (pattern : Fin n → Bool) (value : Bool) : ScalarFunction Bool n :=
  fun input => if ∀ i ∈ coordinates, input i = pattern i then value else !value

private theorem matches_iff (coordinates : Finset (Fin n)) (pattern input : Fin n → Bool) :
    (∀ i ∈ coordinates, input i = pattern i) ↔
      allInputs (coordinates.filter (fun i => pattern i = true)) input = true ∧
        anyInput (coordinates.filter (fun i => pattern i = false)) input = false := by
  simp only [allInputs, anyInput, decide_eq_true_eq, decide_eq_false_iff_not,
    Finset.mem_filter]
  constructor
  · intro agree
    constructor
    · intro i member
      exact (agree i member.1).trans member.2
    · rintro ⟨i, member, value⟩
      have equal := (agree i member.1).trans member.2
      simp_all
  · rintro ⟨positive, negative⟩ i member
    cases expected : pattern i
    · cases actual : input i
      · rfl
      · exact False.elim (negative ⟨i, ⟨member, expected⟩, actual⟩)
    · exact positive i ⟨member, expected⟩

/-- A mask or its complement costs at most one gate per fixed input, except for the empty mask. -/
theorem complexity_mask_le (coordinates : Finset (Fin n)) (pattern : Fin n → Bool) (value : Bool) :
    complexity (mask coordinates pattern value) ≤ max 1 coordinates.card := by
  let positive := coordinates.filter (fun i => pattern i = true)
  let negative := coordinates.filter (fun i => pattern i = false)
  have partition : positive.card + negative.card = coordinates.card := by
    simpa [positive, negative] using Finset.card_filter_add_card_filter_not
      (s := coordinates) (p := fun i => pattern i = true)
  have identity : mask coordinates pattern value = fun input =>
      if value then allInputs positive input && !(anyInput negative input)
      else !(allInputs positive input) || anyInput negative input := by
    funext input
    simp only [mask, matches_iff]
    change (if allInputs positive input = true ∧ anyInput negative input = false then value else !value) = _
    cases value <;> cases allInputs positive input <;> cases anyInput negative input <;> rfl
  by_cases pEmpty : positive = ∅
  · by_cases nEmpty : negative = ∅
    · have equal : mask coordinates pattern value = fun _ => value := by
        rw [identity, pEmpty, nEmpty]
        funext input
        cases value <;> simp [allInputs, anyInput]
      rw [equal]
      exact (complexity_constant_le n value).trans (le_max_left _ _)
    · have bound := complexity_anyInput_add_one_le negative (Finset.nonempty_iff_ne_empty.mpr nEmpty)
      have negated := complexity_not_le (anyInput negative)
      have equal : mask coordinates pattern value = fun input =>
          if value then !(anyInput negative input) else anyInput negative input := by
        rw [identity, pEmpty]
        funext input
        cases value <;> simp [allInputs]
      rw [equal]
      rw [pEmpty, Finset.card_empty] at partition
      cases value
      · change complexity (anyInput negative) ≤ _
        omega
      · change complexity (fun input => !(anyInput negative input)) ≤ _
        omega
  · have pBound := complexity_allInputs_add_one_le positive (Finset.nonempty_iff_ne_empty.mpr pEmpty)
    have pNot := complexity_not_le (allInputs positive)
    by_cases nEmpty : negative = ∅
    · have equal : mask coordinates pattern value = fun input =>
          if value then allInputs positive input else !(allInputs positive input) := by
        rw [identity, nEmpty]
        funext input
        cases value <;> simp [anyInput]
      rw [equal]
      rw [nEmpty, Finset.card_empty] at partition
      cases value
      · change complexity (fun input => !(allInputs positive input)) ≤ _
        omega
      · change complexity (allInputs positive) ≤ _
        omega
    · have nBound := complexity_anyInput_add_one_le negative (Finset.nonempty_iff_ne_empty.mpr nEmpty)
      have nNot := complexity_not_le (anyInput negative)
      have andBound := complexity_and_le (allInputs positive) (fun input => !(anyInput negative input))
      have orBound := complexity_or_le (fun input => !(allInputs positive input)) (anyInput negative)
      rw [identity]
      cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Every single exception to either constant has a circuit of size at most the input width. -/
theorem complexity_point_indicator_le (positive : 0 < n) (point : Fin n → Bool) (value : Bool) :
    complexity (fun input => if input = point then value else !value) ≤ n := by
  have identity : (fun input => if input = point then value else !value) = mask Finset.univ point value := by
    funext input
    simp [mask, funext_iff]
  rw [identity]
  simpa [Nat.max_eq_right positive] using complexity_mask_le Finset.univ point value

end Algebraic.DeMorgan
