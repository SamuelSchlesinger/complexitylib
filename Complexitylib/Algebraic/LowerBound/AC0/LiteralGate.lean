/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AC0
public import Complexitylib.Algebraic.LowerBound.AC0.NormalForm

/-!
# Literal-input AC0 gates as bounded normal forms

A bottom AND or OR gate reads a finite family of signed input literals. Equal
duplicates are harmless, while opposite occurrences of one variable make the
conjunction false and the disjunction true. This module converts those cases
symbolically to a DNF or CNF and proves semantic correctness and a width bound
by the original fan-in.

The representative literal stored for each input coordinate is selected only
at proof level. No truth-table enumeration or optimal-form search is defined.
-/

@[expose] public section

namespace Algebraic.AC0

namespace LiteralFamily

/-- No coordinate occurs with two different satisfying values. -/
def Compatible (literals : Fin literalCount -> Literal n) : Prop :=
  forall left right,
    (literals left).index = (literals right).index ->
      (literals left).value = (literals right).value

/-- Compatibility of a finite literal family is decidable. -/
instance compatibleDecidable (literals : Fin literalCount -> Literal n) :
    Decidable (Compatible literals) := by
  unfold Compatible
  infer_instance

/-- Partial assignment obtained by choosing the value of one occurrence of
each coordinate. Its semantic specifications assume compatibility. -/
noncomputable def requirements
    (literals : Fin literalCount -> Literal n) : PartialAssignment n :=
  fun index =>
    if present : Exists fun argument => (literals argument).index = index then
      some (literals (Classical.choose present)).value
    else
      none

/-- Literal set carried by the representative partial assignment. -/
noncomputable def toLiteralSet
    (literals : Fin literalCount -> Literal n) : LiteralSet n :=
  ⟨requirements literals⟩

/-- For a compatible family, the representative assignment contains exactly
the input literals occurring in the family. -/
theorem requirements_eq_some_iff
    (literals : Fin literalCount -> Literal n)
    (compatible : Compatible literals)
    (index : Fin n)
    (value : Bool) :
    requirements literals index = some value ↔
      Exists fun argument =>
        (literals argument).index = index ∧
          (literals argument).value = value := by
  classical
  unfold requirements
  split
  next present =>
    constructor
    · intro equal
      refine ⟨Classical.choose present, Classical.choose_spec present, ?_⟩
      injection equal
    · rintro ⟨argument, argumentIndex, argumentValue⟩
      congr 1
      calc
        (literals (Classical.choose present)).value =
            (literals argument).value :=
          compatible _ _ (Classical.choose_spec present |>.trans
            argumentIndex.symm)
        _ = value := argumentValue
  next absent =>
    constructor
    · intro impossible
      simp at impossible
    · rintro ⟨argument, argumentIndex, _⟩
      exact False.elim (absent ⟨argument, argumentIndex⟩)

/-- Every coordinate in the representative literal set occurs in the source
family. -/
theorem support_toLiteralSet_subset
    (literals : Fin literalCount -> Literal n) :
    (toLiteralSet literals).support ⊆
      Finset.univ.image fun argument => (literals argument).index := by
  classical
  intro index present
  rw [LiteralSet.mem_support] at present
  change requirements literals index ≠ none at present
  unfold requirements at present
  split at present
  next witness =>
    exact Finset.mem_image.mpr
      ⟨Classical.choose witness, Finset.mem_univ _,
        Classical.choose_spec witness⟩
  next absent => simp at present

/-- Collapsing repeated coordinates cannot make width exceed fan-in. -/
theorem width_toLiteralSet_le
    (literals : Fin literalCount -> Literal n) :
    (toLiteralSet literals).width ≤ literalCount := by
  calc
    (toLiteralSet literals).width ≤
        (Finset.univ.image fun argument =>
          (literals argument).index).card :=
      Finset.card_le_card (support_toLiteralSet_subset literals)
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = literalCount := Fintype.card_fin literalCount

/-- A compatible family and its representative term have the same
conjunctive semantics. -/
theorem term_satisfiedBy_toLiteralSet_iff
    (literals : Fin literalCount -> Literal n)
    (compatible : Compatible literals)
    (input : Fin n -> Bool) :
    Term.SatisfiedBy (toLiteralSet literals) input ↔
      forall argument,
        input (literals argument).index = (literals argument).value := by
  constructor
  · intro satisfied argument
    apply satisfied (literals argument).index (literals argument).value
    change requirements literals (literals argument).index =
      some (literals argument).value
    exact (requirements_eq_some_iff literals compatible _ _).2
      ⟨argument, rfl, rfl⟩
  · intro allSatisfied index value required
    change requirements literals index = some value at required
    obtain ⟨argument, argumentIndex, argumentValue⟩ :=
      (requirements_eq_some_iff literals compatible index value).1 required
    rw [← argumentValue, ← argumentIndex]
    exact allSatisfied argument

/-- A compatible family and its representative clause have the same
disjunctive semantics. -/
theorem clause_satisfiedBy_toLiteralSet_iff
    (literals : Fin literalCount -> Literal n)
    (compatible : Compatible literals)
    (input : Fin n -> Bool) :
    Clause.SatisfiedBy (toLiteralSet literals) input ↔
      Exists fun argument =>
        input (literals argument).index = (literals argument).value := by
  constructor
  · rintro ⟨index, value, required, inputValue⟩
    change requirements literals index = some value at required
    obtain ⟨argument, argumentIndex, argumentValue⟩ :=
      (requirements_eq_some_iff literals compatible index value).1 required
    refine ⟨argument, ?_⟩
    rw [argumentIndex, argumentValue]
    exact inputValue
  · rintro ⟨argument, inputValue⟩
    refine ⟨(literals argument).index, (literals argument).value, ?_,
      inputValue⟩
    change requirements literals (literals argument).index =
      some (literals argument).value
    exact (requirements_eq_some_iff literals compatible _ _).2
      ⟨argument, rfl, rfl⟩

/-- Failure of compatibility supplies two opposite occurrences of one
coordinate. -/
theorem exists_conflict_of_not_compatible
    (literals : Fin literalCount -> Literal n)
    (notCompatible : ¬Compatible literals) :
    Exists fun left => Exists fun right =>
      (literals left).index = (literals right).index ∧
        (literals left).value ≠ (literals right).value := by
  classical
  unfold Compatible at notCompatible
  push Not at notCompatible
  exact notCompatible

/-- An incompatible literal family cannot be satisfied conjunctively. -/
theorem not_all_satisfied_of_not_compatible
    (literals : Fin literalCount -> Literal n)
    (notCompatible : ¬Compatible literals)
    (input : Fin n -> Bool) :
    ¬(forall argument,
      input (literals argument).index = (literals argument).value) := by
  obtain ⟨left, right, sameIndex, different⟩ :=
    exists_conflict_of_not_compatible literals notCompatible
  intro allSatisfied
  apply different
  rw [← allSatisfied left, ← allSatisfied right, sameIndex]

/-- Every input satisfies some literal in an incompatible family. -/
theorem exists_satisfied_of_not_compatible
    (literals : Fin literalCount -> Literal n)
    (notCompatible : ¬Compatible literals)
    (input : Fin n -> Bool) :
    Exists fun argument =>
      input (literals argument).index = (literals argument).value := by
  obtain ⟨left, right, sameIndex, different⟩ :=
    exists_conflict_of_not_compatible literals notCompatible
  by_cases leftSatisfied :
      input (literals left).index = (literals left).value
  · exact ⟨left, leftSatisfied⟩
  · refine ⟨right, ?_⟩
    cases leftValue : (literals left).value <;>
      cases rightValue : (literals right).value <;>
      cases inputValue : input (literals left).index <;>
      simp_all

/-- A literal-input AND gate as a DNF: one term when compatible, otherwise
constant false. -/
noncomputable def conjunction
    (literals : Fin literalCount -> Literal n) : DNF n :=
  if Compatible literals then
    ⟨[toLiteralSet literals]⟩
  else
    DNF.bottom

/-- A literal-input OR gate as a CNF: one clause when compatible, otherwise
constant true. -/
noncomputable def disjunction
    (literals : Fin literalCount -> Literal n) : CNF n :=
  if Compatible literals then
    ⟨[toLiteralSet literals]⟩
  else
    CNF.top

/-- The DNF conversion computes the original unbounded conjunction. -/
theorem conjunction_eval
    (literals : Fin literalCount -> Literal n)
    (input : Fin n -> Bool) :
    (conjunction literals).eval input =
      interpretation (.and literalCount) (fun argument =>
        (literals argument).eval input) := by
  by_cases compatible : Compatible literals
  · rw [conjunction, ite_eq_left compatible]
    apply Bool.eq_iff_iff.mpr
    simp only [DNF.eval_eq_true, List.mem_singleton,
      interpretation_and_eq_true, Literal.eval_eq_true]
    simp [term_satisfiedBy_toLiteralSet_iff literals compatible input]
  · rw [conjunction, ite_eq_right compatible, DNF.eval_bottom]
    symm
    apply Bool.eq_false_iff.mpr
    intro allTrue
    have allSatisfied : forall argument,
        input (literals argument).index = (literals argument).value :=
      fun argument => Literal.eval_eq_true _ _ |>.1
        ((interpretation_and_eq_true _).1 allTrue argument)
    exact not_all_satisfied_of_not_compatible
      literals compatible input allSatisfied

/-- The CNF conversion computes the original unbounded disjunction. -/
theorem disjunction_eval
    (literals : Fin literalCount -> Literal n)
    (input : Fin n -> Bool) :
    (disjunction literals).eval input =
      interpretation (.or literalCount) (fun argument =>
        (literals argument).eval input) := by
  by_cases compatible : Compatible literals
  · rw [disjunction, ite_eq_left compatible]
    apply Bool.eq_iff_iff.mpr
    simp only [CNF.eval_eq_true, List.mem_singleton,
      interpretation_or_eq_true, Literal.eval_eq_true]
    simp [clause_satisfiedBy_toLiteralSet_iff literals compatible input]
  · rw [disjunction, ite_eq_right compatible, CNF.eval_top]
    symm
    apply (interpretation_or_eq_true _).2
    obtain ⟨argument, satisfied⟩ :=
      exists_satisfied_of_not_compatible literals compatible input
    exact ⟨argument, (Literal.eval_eq_true _ _).2 satisfied⟩

/-- The conjunction DNF has width at most the gate fan-in. -/
theorem conjunction_widthAtMost
    (literals : Fin literalCount -> Literal n) :
    (conjunction literals).WidthAtMost literalCount := by
  by_cases compatible : Compatible literals
  · rw [conjunction, ite_eq_left compatible]
    intro term present
    simp only [List.mem_singleton] at present
    subst term
    exact width_toLiteralSet_le literals
  · rw [conjunction, ite_eq_right compatible]
    intro term present
    simp [DNF.bottom] at present

/-- The disjunction CNF has width at most the gate fan-in. -/
theorem disjunction_widthAtMost
    (literals : Fin literalCount -> Literal n) :
    (disjunction literals).WidthAtMost literalCount := by
  by_cases compatible : Compatible literals
  · rw [disjunction, ite_eq_left compatible]
    intro clause present
    simp only [List.mem_singleton] at present
    subst clause
    exact width_toLiteralSet_le literals
  · rw [disjunction, ite_eq_right compatible]
    intro clause present
    simp [CNF.top] at present

end LiteralFamily
end Algebraic.AC0
