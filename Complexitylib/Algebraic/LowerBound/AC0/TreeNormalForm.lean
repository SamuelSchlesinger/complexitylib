/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Duality

/-!
# Bounded normal forms from decision trees

A decision tree of depth `d` has both an exact width-`d` DNF and an exact
width-`d` CNF. This module constructs the DNF structurally from accepting
paths, then obtains the CNF by De Morgan duality.

Repeated queries require care: conjoining a branch literal keeps an identical
literal already present in a term, discards a contradictory term, and inserts
the literal only when its coordinate is absent. Thus the construction applies
to arbitrary decision trees and does not assume a read-once normal form. It is
a symbolic tree traversal, not truth-table enumeration or depth optimization.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Term

/-- Conjoin one literal with a noncontradictory term. A conflicting repeated
literal makes the conjunction false, represented by `none`. -/
def conjoinLiteral
    (term : Term n)
    (literal : Literal n) : Option (Term n) :=
  match term.requirements literal.index with
  | none =>
      some ⟨term.requirements.refine
        (PartialAssignment.fix literal.index literal.value)⟩
  | some existing =>
      if existing = literal.value then some term else none

/-- `conjoinLiteral` has exactly the semantics of Boolean conjunction. -/
theorem conjoinLiteral_sound
    (term : Term n)
    (literal : Literal n)
    (input : Fin n -> Bool) :
    (term.conjoinLiteral literal).elim false
        (fun result => result.eval input) =
      (term.eval input && literal.eval input) := by
  cases existing : term.requirements literal.index with
  | none =>
      simp only [conjoinLiteral, existing, Option.elim_some]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Term.eval_eq_true, Literal.eval_eq_true]
      constructor
      · intro resultSatisfied
        constructor
        · intro index value requirement
          apply resultSatisfied index value
          simp [PartialAssignment.refine, requirement]
        · apply resultSatisfied literal.index literal.value
          simp [PartialAssignment.refine, existing,
            PartialAssignment.fix]
      · rintro ⟨termSatisfied, literalSatisfied⟩ index value requirement
        cases source : term.requirements index with
        | none =>
            have fixed :
                PartialAssignment.fix literal.index literal.value index =
                  some value := by
              simpa [PartialAssignment.refine, source] using requirement
            by_cases equal : index = literal.index
            · subst index
              have valueEqual : literal.value = value := by
                simpa [PartialAssignment.fix] using fixed
              simpa [valueEqual] using literalSatisfied
            · simp [PartialAssignment.fix, equal] at fixed
        | some sourceValue =>
            have valueEqual : sourceValue = value := by
              simpa [PartialAssignment.refine, source] using requirement
            subst value
            exact termSatisfied index sourceValue source
  | some existingValue =>
      by_cases equal : existingValue = literal.value
      · subst existingValue
        simp only [conjoinLiteral, existing]
        have literalFollows :
            term.eval input = true -> literal.eval input = true := by
          intro termTrue
          apply (Literal.eval_eq_true literal input).2
          exact (Term.eval_eq_true term input).1 termTrue
            literal.index literal.value existing
        cases termValue : term.eval input <;> simp [termValue, literalFollows]
      · simp only [conjoinLiteral, existing, ite_eq_right equal,
          Option.elim_none]
        symm
        apply Bool.eq_false_iff.mpr
        intro conjunctionTrue
        have termTrue : term.eval input = true :=
          (Bool.and_eq_true_iff.mp conjunctionTrue).1
        have literalTrue : literal.eval input = true :=
          (Bool.and_eq_true_iff.mp conjunctionTrue).2
        have inputExisting := (Term.eval_eq_true term input).1 termTrue
          literal.index existingValue existing
        have inputLiteral := (Literal.eval_eq_true literal input).1 literalTrue
        exact equal (inputExisting.symm.trans inputLiteral)

/-- Conjoining one literal increases term width by at most one. -/
theorem width_conjoinLiteral_le
    (term result : Term n)
    (literal : Literal n)
    (conjoined : term.conjoinLiteral literal = some result) :
    result.width <= term.width + 1 := by
  cases existing : term.requirements literal.index with
  | none =>
      rw [conjoinLiteral, existing] at conjoined
      injection conjoined with resultEqual
      subst result
      change
        (term.requirements.refine
          (PartialAssignment.fix literal.index literal.value)).fixedVariables.card <=
        term.requirements.fixedVariables.card + 1
      rw [PartialAssignment.fixedVariables_refine,
        PartialAssignment.fixedVariables_fix]
      simpa using Finset.card_union_le
        term.requirements.fixedVariables ({literal.index} : Finset (Fin n))
  | some existingValue =>
      by_cases equal : existingValue = literal.value
      · simp [conjoinLiteral, existing, equal] at conjoined
        subst result
        omega
      · simp [conjoinLiteral, existing, equal] at conjoined

end Term

namespace DNF

/-- Conjoin every term of a DNF with one literal, discarding contradictory
terms. -/
def conjoinLiteral
    (formula : DNF n)
    (literal : Literal n) : DNF n :=
  ⟨formula.terms.filterMap fun term => term.conjoinLiteral literal⟩

/-- Formula-level literal conjunction is semantically exact. -/
@[simp] theorem eval_conjoinLiteral
    (formula : DNF n)
    (literal : Literal n)
    (input : Fin n -> Bool) :
    (formula.conjoinLiteral literal).eval input =
      (formula.eval input && literal.eval input) := by
  change (formula.terms.filterMap fun term => term.conjoinLiteral literal).any
      (fun term => term.eval input) =
    (formula.terms.any (fun term => term.eval input) && literal.eval input)
  induction formula.terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      have sound := Term.conjoinLiteral_sound term literal input
      cases termValue : term.eval input <;>
        cases restValue : terms.any (fun current => current.eval input) <;>
          cases literalValue : literal.eval input <;>
            cases conjoined : term.conjoinLiteral literal <;>
              simp [conjoined, termValue, restValue, literalValue,
                inductionHypothesis] at sound ⊢ <;>
              assumption

/-- Literal conjunction raises a DNF width bound by at most one. -/
theorem WidthAtMost.conjoinLiteral
    {formula : DNF n}
    {bound : Nat}
    (bounded : formula.WidthAtMost bound)
    (literal : Literal n) :
    (formula.conjoinLiteral literal).WidthAtMost (bound + 1) := by
  intro result present
  obtain ⟨term, termPresent, conjoined⟩ := List.mem_filterMap.1 present
  exact (Term.width_conjoinLiteral_le term result literal conjoined).trans
    (Nat.add_le_add_right (bounded term termPresent) 1)

/-- Disjunction of two ordered DNFs by concatenating their term lists. -/
def disjoin (left right : DNF n) : DNF n :=
  ⟨left.terms ++ right.terms⟩

/-- DNF list concatenation computes Boolean disjunction. -/
@[simp] theorem eval_disjoin
    (left right : DNF n)
    (input : Fin n -> Bool) :
    (left.disjoin right).eval input =
      (left.eval input || right.eval input) := by
  simp [disjoin, eval, List.any_append]

/-- Concatenating two DNFs preserves a common width bound. -/
theorem WidthAtMost.disjoin
    {left right : DNF n}
    {bound : Nat}
    (leftBounded : left.WidthAtMost bound)
    (rightBounded : right.WidthAtMost bound) :
    (left.disjoin right).WidthAtMost bound := by
  intro term present
  rcases List.mem_append.mp present with inLeft | inRight
  · exact leftBounded term inLeft
  · exact rightBounded term inRight

end DNF

namespace DecisionTree

/-- Structural DNF expansion of a decision tree. Each accepting path becomes
a term; incompatible repeated queries are discarded while matching repeats
do not increase width. -/
def toDNF : DecisionTree n -> DNF n
  | .leaf false => DNF.bottom
  | .leaf true => DNF.top
  | .query index onFalse onTrue =>
      ((toDNF onFalse).conjoinLiteral ⟨index, false⟩).disjoin
        ((toDNF onTrue).conjoinLiteral ⟨index, true⟩)

/-- The structural DNF computes exactly the source decision tree. -/
@[simp] theorem eval_toDNF
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    tree.toDNF.eval input = tree.eval input := by
  induction tree with
  | leaf value => cases value <;> simp [toDNF]
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      cases inputValue : input index <;>
        simp [toDNF, eval, inputValue, falseHypothesis, trueHypothesis,
          Literal.eval]

/-- Every term in the structural DNF has width at most the tree depth. -/
theorem widthAtMost_toDNF
    (tree : DecisionTree n) :
    tree.toDNF.WidthAtMost tree.depth := by
  induction tree with
  | leaf value =>
      cases value
      · intro term present
        simp [toDNF, DNF.bottom] at present
      · intro term present
        simp only [toDNF, DNF.top, List.mem_singleton] at present
        subst term
        simp
  | query index onFalse onTrue falseHypothesis trueHypothesis =>
      apply DNF.WidthAtMost.disjoin
      · exact (falseHypothesis.conjoinLiteral ⟨index, false⟩).mono (by
          simp [depth])
      · exact (trueHypothesis.conjoinLiteral ⟨index, true⟩).mono (by
          simp [depth])

/-- De Morgan-derived structural CNF expansion of a decision tree. -/
def toCNF (tree : DecisionTree n) : CNF n :=
  tree.negate.toDNF.negate

/-- The structural CNF computes exactly the source decision tree. -/
@[simp] theorem eval_toCNF
    (tree : DecisionTree n)
    (input : Fin n -> Bool) :
    tree.toCNF.eval input = tree.eval input := by
  simp [toCNF]

/-- Every clause in the structural CNF has width at most the tree depth. -/
theorem widthAtMost_toCNF
    (tree : DecisionTree n) :
    tree.toCNF.WidthAtMost tree.depth := by
  simpa [toCNF] using (widthAtMost_toDNF tree.negate).negate

/-- Any function of decision-tree depth at most `bound` has an exact
width-`bound` DNF representation. -/
theorem exists_dnf_widthAtMost_of_depthAtMost
    {function : ScalarFunction Bool n}
    {bound : Nat}
    (bounded : DepthAtMost function bound) :
    Exists fun formula : DNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input = function input := by
  obtain ⟨tree, computes, depthBound⟩ := bounded
  exact ⟨tree.toDNF, (widthAtMost_toDNF tree).mono depthBound,
    fun input => (eval_toDNF tree input).trans (computes input)⟩

/-- Any function of decision-tree depth at most `bound` has an exact
width-`bound` CNF representation. -/
theorem exists_cnf_widthAtMost_of_depthAtMost
    {function : ScalarFunction Bool n}
    {bound : Nat}
    (bounded : DepthAtMost function bound) :
    Exists fun formula : CNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input = function input := by
  obtain ⟨tree, computes, depthBound⟩ := bounded
  exact ⟨tree.toCNF, (widthAtMost_toCNF tree).mono depthBound,
    fun input => (eval_toCNF tree input).trans (computes input)⟩

end DecisionTree

end AC0
end Algebraic
