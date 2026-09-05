/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Lookup.Defs
import Complexitylib.Circuits.BinaryComparison
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion
import Complexitylib.Circuits.Encoding.FixedWidth.Conversion.Internal
import Complexitylib.Circuits.Encoding.Formula.Batch

/-!
# Fixed-width binary-reference lookup formulas -- proof internals
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace LookupFormula

private theorem unsignedValue_injective {width : Nat} :
    Function.Injective (@BitString.unsignedValue width) := by
  intro left right hvalue
  apply BitString.toList_inj.mp
  apply Nat.fromBitsLE_inj_of_length_eq
  · simp
  · exact hvalue

theorem eval_wordEqual_internal {width : Nat}
    (word : Fin width → BoolFormula) (value : BitString width)
    (assignment : Nat → Bool) :
    (wordEqual word value).eval assignment =
      decide (evaluatedWord word assignment = value) := by
  rw [wordEqual]
  simp only [BoolFormula.eval]
  rw [BoolFormula.eval_unsignedLEOf,
    BoolFormula.eval_unsignedLEOf,
    BitString.unsignedLE_eq_decide,
    BitString.unsignedLE_eq_decide]
  simp only [BoolFormula.eval_ofBool]
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hleft, hright⟩
    apply unsignedValue_injective
    exact Nat.le_antisymm hleft hright
  · intro hequal
    subst value
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

private theorem unsignedValue_referenceBits {width value : Nat}
    (hvalue : value < 2 ^ width) :
    (GateSlot.referenceBits width value).unsignedValue = value := by
  unfold BitString.unsignedValue
  rw [GateSlot.toList_referenceBits,
    Nat.fromBitsLE_toBitsLE hvalue]

theorem eval_select_internal {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula) (assignment : Nat → Bool)
    (hcount : count ≤ 2 ^ width) :
    (select word values).eval assignment =
      if hvalue : (evaluatedWord word assignment).unsignedValue < count then
        (values ⟨(evaluatedWord word assignment).unsignedValue,
          hvalue⟩).eval assignment
      else
        false := by
  rw [select, BoolFormula.eval_disjs]
  by_cases hvalue :
      (evaluatedWord word assignment).unsignedValue < count
  · rw [dite_eq_left hvalue]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hselected
      rw [List.any_eq_true] at hselected
      obtain ⟨formula, hformula, hformulaValue⟩ := hselected
      rw [List.mem_ofFn'] at hformula
      obtain ⟨index, rfl⟩ := hformula
      simp only [candidate, BoolFormula.eval, Bool.and_eq_true,
        eval_wordEqual_internal, decide_eq_true_eq] at hformulaValue
      have hindexFits : index.val < 2 ^ width :=
        lt_of_lt_of_le index.isLt hcount
      have hindexValue := congrArg BitString.unsignedValue hformulaValue.1
      rw [unsignedValue_referenceBits hindexFits] at hindexValue
      have hindex : index =
          ⟨(evaluatedWord word assignment).unsignedValue, hvalue⟩ := by
        apply Fin.ext
        exact hindexValue.symm
      simpa [hindex] using hformulaValue.2
    · intro hselected
      rw [List.any_eq_true]
      let index : Fin count :=
        ⟨(evaluatedWord word assignment).unsignedValue, hvalue⟩
      refine ⟨candidate word values index, ?_, ?_⟩
      · rw [List.mem_ofFn']
        exact ⟨index, rfl⟩
      · simp only [candidate, BoolFormula.eval, Bool.and_eq_true,
          eval_wordEqual_internal, decide_eq_true_eq]
        constructor
        · exact (GateSlot.referenceBits_fromBitsLE_internal (evaluatedWord word assignment)).symm
        · exact hselected
  · rw [dite_eq_right hvalue]
    apply Bool.eq_false_of_not_eq_true
    intro hselected
    rw [List.any_eq_true] at hselected
    obtain ⟨formula, hformula, hformulaValue⟩ := hselected
    rw [List.mem_ofFn'] at hformula
    obtain ⟨index, rfl⟩ := hformula
    simp only [candidate, BoolFormula.eval, Bool.and_eq_true,
      eval_wordEqual_internal, decide_eq_true_eq] at hformulaValue
    have hindexFits : index.val < 2 ^ width :=
      lt_of_lt_of_le index.isLt hcount
    have hindexValue := congrArg BitString.unsignedValue hformulaValue.1
    rw [unsignedValue_referenceBits hindexFits] at hindexValue
    apply hvalue
    rw [hindexValue]
    exact index.isLt

theorem size_wordEqual_internal {width : Nat}
    (word : Fin width → BoolFormula) (value : BitString width)
    (hword : ∀ coordinate, (word coordinate).size = 1) :
    (wordEqual word value).size = (30 : Nat) * width + 3 := by
  have hleft := BoolFormula.size_unsignedLEOf word
    (fun coordinate => BoolFormula.ofBool (value coordinate))
    hword (fun coordinate => BoolFormula.size_ofBool_internal _)
  have hright := BoolFormula.size_unsignedLEOf
    (fun coordinate => BoolFormula.ofBool (value coordinate)) word
    (fun coordinate => BoolFormula.size_ofBool_internal _) hword
  rw [wordEqual]
  simp only [BoolFormula.size, hleft, hright]
  omega

theorem size_select_internal {width count : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula)
    (hword : ∀ coordinate, (word coordinate).size = 1)
    (hvalues : ∀ index, (values index).size = 1) :
    (select word values).size = selectSize width count := by
  have hcandidate (index : Fin count) :
      (candidate word values index).size = 30 * width + 5 := by
    rw [candidate]
    simp only [BoolFormula.size,
      size_wordEqual_internal word
        (GateSlot.referenceBits width index.val) hword,
      hvalues index]
  rw [select, BoolFormula.size_disjs, List.map_ofFn]
  change 1 +
    (List.ofFn fun index : Fin count =>
      (candidate word values index).size + 1).sum = _
  simp_rw [hcandidate]
  simp [selectSize]

private theorem vars_ofBool_empty (value : Bool) :
    (BoolFormula.ofBool value).vars = ∅ := by
  cases value <;> rfl

private theorem vars_wordEqual_lt {width available : Nat}
    (word : Fin width → BoolFormula) (value : BitString width)
    (hword : ∀ coordinate wire,
      wire ∈ (word coordinate).vars → wire < available) :
    ∀ wire ∈ (wordEqual word value).vars, wire < available := by
  intro wire hwire
  simp only [wordEqual, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with hwire | hwire
  · apply BoolFormula.vars_unsignedLEOf_lt_internal
    · exact hword
    · intro coordinate other hother
      rw [vars_ofBool_empty] at hother
      simp at hother
    · exact hwire
  · apply BoolFormula.vars_unsignedLEOf_lt_internal
    · intro coordinate other hother
      rw [vars_ofBool_empty] at hother
      simp at hother
    · exact hword
    · exact hwire

private theorem vars_candidate_lt {width count available : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula) (index : Fin count)
    (hword : ∀ coordinate wire,
      wire ∈ (word coordinate).vars → wire < available)
    (hvalues : ∀ index wire,
      wire ∈ (values index).vars → wire < available) :
    ∀ wire ∈ (candidate word values index).vars, wire < available := by
  intro wire hwire
  simp only [candidate, BoolFormula.vars, Finset.mem_union] at hwire
  rcases hwire with hwire | hwire
  · exact vars_wordEqual_lt word
      (GateSlot.referenceBits width index.val) hword wire hwire
  · exact hvalues index wire hwire

private theorem vars_disjs_lt (available : Nat)
    (formulas : List BoolFormula)
    (hformulas : ∀ formula ∈ formulas,
      ∀ wire ∈ formula.vars, wire < available) :
    ∀ wire ∈ (BoolFormula.disjs formulas).vars, wire < available := by
  induction formulas with
  | nil =>
      simp [BoolFormula.disjs, BoolFormula.vars]
  | cons formula formulas ih =>
      intro wire hwire
      simp only [BoolFormula.disjs, BoolFormula.vars,
        Finset.mem_union] at hwire
      rcases hwire with hwire | hwire
      · exact hformulas formula (by simp) wire hwire
      · apply ih
        · intro tail htail
          exact hformulas tail (by simp [htail])
        · exact hwire

theorem vars_select_lt_internal {width count available : Nat}
    (word : Fin width → BoolFormula)
    (values : Fin count → BoolFormula)
    (hword : ∀ coordinate wire,
      wire ∈ (word coordinate).vars → wire < available)
    (hvalues : ∀ index wire,
      wire ∈ (values index).vars → wire < available) :
    ∀ wire ∈ (select word values).vars, wire < available := by
  unfold select
  apply vars_disjs_lt available
  intro formula hformula
  rw [List.mem_ofFn'] at hformula
  obtain ⟨index, rfl⟩ := hformula
  exact vars_candidate_lt word values index hword hvalues

end LookupFormula

end FixedWidth

end CircuitCode

end Complexity
