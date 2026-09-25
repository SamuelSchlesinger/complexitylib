/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.DecisionTree

/-!
# De Morgan duality for bounded normal forms

Negating every literal turns a term into its complementary clause and a clause
into its complementary term. Mapping this operation across the outer list
gives exact DNF/CNF duals. This module proves semantic complementation, width
preservation, compatibility with restriction, and invariance of semantic
decision-tree depth under output negation.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace LiteralSet

/-- Flip the satisfying value of every literal in a literal set. -/
def negate (set : LiteralSet n) : LiteralSet n :=
  ⟨fun index => (set.requirements index).map fun value => !value⟩

@[simp] theorem negate_requirements
    (set : LiteralSet n)
    (index : Fin n) :
    set.negate.requirements index =
      (set.requirements index).map fun value => !value :=
  rfl

@[simp] theorem negate_negate (set : LiteralSet n) :
    set.negate.negate = set := by
  cases set with
  | mk requirements =>
      apply congrArg LiteralSet.mk
      funext index
      cases value : requirements index <;> simp [negate, value]

@[simp] theorem support_negate (set : LiteralSet n) :
    set.negate.support = set.support := by
  ext index
  simp [mem_support, negate]

@[simp] theorem width_negate (set : LiteralSet n) :
    set.negate.width = set.width := by
  simp [width]

/-- A fixed value satisfies a negated literal exactly when it conflicts with
the source literal. -/
theorem negate_hitBy_iff_conflictsWith
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    set.negate.HitBy rho ↔ set.ConflictsWith rho := by
  constructor
  · rintro ⟨index, value, negatedValue, fixedValue⟩
    cases sourceValue : set.requirements index with
    | none => simp [negate, sourceValue] at negatedValue
    | some source =>
        have equal : value = !source := by
          simpa [negate, sourceValue] using negatedValue.symm
        subst value
        refine ⟨index, source, !source, sourceValue, fixedValue, ?_⟩
        cases source <;> decide
  · rintro ⟨index, required, fixed, requiredValue, fixedValue, different⟩
    have equal : fixed = !required := by
      cases required <;> cases fixed <;> simp_all
    subst fixed
    exact ⟨index, !required, by simp [negate, requiredValue], fixedValue⟩

/-- A fixed value conflicts with a negated literal exactly when it satisfies
the source literal. -/
theorem negate_conflictsWith_iff_hitBy
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    set.negate.ConflictsWith rho ↔ set.HitBy rho := by
  simpa only [negate_negate] using
    (negate_hitBy_iff_conflictsWith set.negate rho).symm

/-- Removing fixed coordinates commutes with literal negation. -/
theorem residual_negate
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    set.negate.residual rho = (set.residual rho).negate := by
  cases set with
  | mk requirements =>
      apply congrArg LiteralSet.mk
      funext index
      cases fixed : rho index <;> simp [residual, negate, fixed]

end LiteralSet

namespace Clause

/-- A clause made of the negated literals is true exactly when the source term
is false. -/
@[simp] theorem eval_negate_term
    (term : Term n)
    (input : Fin n -> Bool) :
    Clause.eval term.negate input = !Term.eval term input := by
  by_cases satisfied : term.SatisfiedBy input
  · have termTrue : Term.eval term input = true :=
      (Term.eval_eq_true term input).2 satisfied
    rw [termTrue]
    simp only [Bool.not_true]
    apply Bool.eq_false_iff.mpr
    intro negatedTrue
    obtain ⟨index, value, negatedValue, inputValue⟩ :=
      (Clause.eval_eq_true term.negate input).1 negatedTrue
    cases sourceValue : term.requirements index with
    | none => simp [LiteralSet.negate, sourceValue] at negatedValue
    | some source =>
        have equal : value = !source := by
          simpa [LiteralSet.negate, sourceValue] using negatedValue.symm
        subst value
        have sourceInput := satisfied index source sourceValue
        cases source <;> simp_all
  · have termFalse : Term.eval term input = false := by
      apply Bool.eq_false_iff.mpr
      intro termTrue
      exact satisfied ((Term.eval_eq_true term input).1 termTrue)
    rw [termFalse]
    simp only [Bool.not_false]
    apply (Clause.eval_eq_true term.negate input).2
    by_contra noNegatedLiteral
    apply satisfied
    intro index value requirement
    by_contra different
    apply noNegatedLiteral
    refine ⟨index, !value, ?_, ?_⟩
    · simp [LiteralSet.negate, requirement]
    · exact (Bool.not_eq_iff.mpr (Ne.symm different)).symm

/-- Clause restriction of a negated term is the negation of term
restriction. -/
theorem restrict_negate_term
    (term : Term n)
    (rho : PartialAssignment n) :
    Clause.restrict term.negate rho =
      (Term.restrict term rho).map LiteralSet.negate := by
  by_cases conflict : term.ConflictsWith rho
  · have hit : term.negate.HitBy rho :=
      (LiteralSet.negate_hitBy_iff_conflictsWith term rho).2 conflict
    simp [Clause.restrict, Term.restrict, conflict, hit]
  · have notHit : ¬term.negate.HitBy rho := fun hit =>
      conflict ((LiteralSet.negate_hitBy_iff_conflictsWith term rho).1 hit)
    simp [Clause.restrict, Term.restrict, conflict, notHit,
      LiteralSet.residual_negate]

end Clause

namespace Term

/-- A term made of the negated literals is true exactly when the source clause
is false. -/
@[simp] theorem eval_negate_clause
    (clause : Clause n)
    (input : Fin n -> Bool) :
    Term.eval clause.negate input = !Clause.eval clause input := by
  have dual := Clause.eval_negate_term clause.negate input
  have negated := congrArg (fun value => !value) dual
  simpa using negated.symm

/-- Term restriction of a negated clause is the negation of clause
restriction. -/
theorem restrict_negate_clause
    (clause : Clause n)
    (rho : PartialAssignment n) :
    Term.restrict clause.negate rho =
      (Clause.restrict clause rho).map LiteralSet.negate := by
  by_cases hit : clause.HitBy rho
  · have conflict : clause.negate.ConflictsWith rho :=
      (LiteralSet.negate_conflictsWith_iff_hitBy clause rho).2 hit
    simp [Term.restrict, Clause.restrict, hit, conflict]
  · have notConflict : ¬clause.negate.ConflictsWith rho := fun conflict =>
      hit ((LiteralSet.negate_conflictsWith_iff_hitBy clause rho).1 conflict)
    simp [Term.restrict, Clause.restrict, hit, notConflict,
      LiteralSet.residual_negate]

end Term

namespace DNF

/-- De Morgan dual of a DNF: negate every term into a clause. -/
def negate (formula : DNF n) : CNF n :=
  ⟨formula.terms.map LiteralSet.negate⟩

@[simp] theorem negate_clauses (formula : DNF n) :
    formula.negate.clauses = formula.terms.map LiteralSet.negate :=
  rfl

/-- De Morgan duality complements DNF semantics. -/
@[simp] theorem eval_negate
    (formula : DNF n)
    (input : Fin n -> Bool) :
    formula.negate.eval input = !formula.eval input := by
  change (formula.terms.map LiteralSet.negate).all
      (fun clause => Clause.eval clause input) =
    !(formula.terms.any fun term => Term.eval term input)
  induction formula.terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      simp only [List.map_cons, List.all_cons, List.any_cons,
        Clause.eval_negate_term, inductionHypothesis]
      cases Term.eval term input <;>
        cases terms.any (fun current => Term.eval current input) <;> rfl

/-- De Morgan duality preserves a width bound. -/
theorem WidthAtMost.negate
    {formula : DNF n}
    {bound : Nat}
    (bounded : formula.WidthAtMost bound) :
    formula.negate.WidthAtMost bound := by
  intro clause present
  obtain ⟨term, termPresent, rfl⟩ := List.mem_map.1 present
  simpa using bounded term termPresent

end DNF

namespace CNF

/-- De Morgan dual of a CNF: negate every clause into a term. -/
def negate (formula : CNF n) : DNF n :=
  ⟨formula.clauses.map LiteralSet.negate⟩

@[simp] theorem negate_terms (formula : CNF n) :
    formula.negate.terms = formula.clauses.map LiteralSet.negate :=
  rfl

/-- De Morgan duality complements CNF semantics. -/
@[simp] theorem eval_negate
    (formula : CNF n)
    (input : Fin n -> Bool) :
    formula.negate.eval input = !formula.eval input := by
  change (formula.clauses.map LiteralSet.negate).any
      (fun term => Term.eval term input) =
    !(formula.clauses.all fun clause => Clause.eval clause input)
  induction formula.clauses with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      simp only [List.map_cons, List.any_cons, List.all_cons,
        Term.eval_negate_clause, inductionHypothesis]
      cases Clause.eval clause input <;>
        cases clauses.all (fun current => Clause.eval current input) <;> rfl

/-- De Morgan duality preserves a width bound. -/
theorem WidthAtMost.negate
    {formula : CNF n}
    {bound : Nat}
    (bounded : formula.WidthAtMost bound) :
    formula.negate.WidthAtMost bound := by
  intro term present
  obtain ⟨clause, clausePresent, rfl⟩ := List.mem_map.1 present
  simpa using bounded clause clausePresent

end CNF

@[simp] theorem DNF.negate_negate (formula : DNF n) :
    formula.negate.negate = formula := by
  cases formula with
  | mk terms =>
      apply congrArg DNF.mk
      simp [DNF.negate, Function.comp_def]

@[simp] theorem CNF.negate_negate (formula : CNF n) :
    formula.negate.negate = formula := by
  cases formula with
  | mk clauses =>
      apply congrArg CNF.mk
      simp [CNF.negate, Function.comp_def]

/-- DNF restriction commutes exactly with De Morgan duality. -/
theorem DNF.negate_restrict
    (formula : DNF n)
    (rho : PartialAssignment n) :
    (formula.restrict rho).negate = formula.negate.restrict rho := by
  cases formula with
  | mk terms =>
      apply congrArg CNF.mk
      simp only [DNF.negate, DNF.restrict]
      induction terms with
      | nil => rfl
      | cons term terms inductionHypothesis =>
          simp only [List.filterMap_cons, List.map_cons]
          rw [Clause.restrict_negate_term]
          cases restricted : Term.restrict term rho <;>
            simp [inductionHypothesis]

/-- CNF restriction commutes exactly with De Morgan duality. -/
theorem CNF.negate_restrict
    (formula : CNF n)
    (rho : PartialAssignment n) :
    (formula.restrict rho).negate = formula.negate.restrict rho := by
  cases formula with
  | mk clauses =>
      apply congrArg DNF.mk
      simp only [CNF.negate, CNF.restrict]
      induction clauses with
      | nil => rfl
      | cons clause clauses inductionHypothesis =>
          simp only [List.filterMap_cons, List.map_cons]
          rw [Term.restrict_negate_clause]
          cases restricted : Clause.restrict clause rho <;>
            simp [inductionHypothesis]

namespace DecisionTree

/-- Negating all leaves preserves an upper bound on semantic decision-tree
depth. -/
theorem DepthAtMost.negate
    {function : ScalarFunction Bool n}
    {bound : Nat}
    (bounded : DepthAtMost function bound) :
    DepthAtMost (fun input => !(function input)) bound := by
  obtain ⟨tree, computes, depthBound⟩ := bounded
  exact ⟨tree.negate, computes.negate, by simpa⟩

/-- Semantic upper decision-tree depth is invariant under output negation. -/
@[simp] theorem depthAtMost_negate_iff
    (function : ScalarFunction Bool n)
    (bound : Nat) :
    DepthAtMost (fun input => !(function input)) bound ↔
      DepthAtMost function bound := by
  constructor
  · intro bounded
    simpa using bounded.negate
  · exact DepthAtMost.negate

/-- Negating all leaves preserves a lower bound on semantic decision-tree
depth. -/
theorem DepthAtLeast.negate
    {function : ScalarFunction Bool n}
    {bound : Nat}
    (lower : DepthAtLeast function bound) :
    DepthAtLeast (fun input => !(function input)) bound := by
  intro tree computes
  have computesSource : tree.negate.Computes function := by
    simpa using computes.negate
  simpa using lower tree.negate computesSource

/-- Semantic lower decision-tree depth is invariant under output negation. -/
@[simp] theorem depthAtLeast_negate_iff
    (function : ScalarFunction Bool n)
    (bound : Nat) :
    DepthAtLeast (fun input => !(function input)) bound ↔
      DepthAtLeast function bound := by
  constructor
  · intro lower
    simpa using lower.negate
  · exact DepthAtLeast.negate

end DecisionTree
end AC0
end Algebraic
