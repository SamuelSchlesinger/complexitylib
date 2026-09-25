/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.PartialAssignment
public import Mathlib.Data.List.Basic

/-!
# Literals and bounded-width normal forms

This module supplies the finite syntax used by switching arguments. A literal
stores the value that makes it true. A `LiteralSet` stores at most one literal
per variable by using a partial assignment, so contradictory terms and
tautological clauses are excluded by construction. Ordered lists of such sets
form DNF and CNF formulas; the order will later make the canonical decision
tree deterministic.

Restriction keeps the original variable names. A term falsified by a fixed
literal is dropped from a DNF, while a clause satisfied by a fixed literal is
dropped from a CNF. Empty terms and clauses represent the Boolean constants
true and false respectively.
-/

@[expose] public section

namespace Algebraic
namespace AC0

/-- A signed Boolean variable, represented by the value that makes the literal
true. Thus `value = true` is a positive literal and `value = false` is a
negative literal. -/
structure Literal (n : Nat) where
  /-- The input coordinate read by the literal. -/
  index : Fin n
  /-- The Boolean value that satisfies the literal. -/
  value : Bool
  deriving DecidableEq

namespace Literal

/-- Evaluate a literal on a complete Boolean input. -/
def eval (literal : Literal n) (input : Fin n -> Bool) : Bool :=
  decide (input literal.index = literal.value)

@[simp] theorem eval_eq_true
    (literal : Literal n)
    (input : Fin n -> Bool) :
    literal.eval input = true ↔ input literal.index = literal.value := by
  simp [eval]

/-- Boolean negation of a literal. -/
def negate (literal : Literal n) : Literal n :=
  { literal with value := !literal.value }

@[simp] theorem negate_index (literal : Literal n) :
    literal.negate.index = literal.index := rfl

@[simp] theorem negate_value (literal : Literal n) :
    literal.negate.value = !literal.value := rfl

@[simp] theorem negate_negate (literal : Literal n) :
    literal.negate.negate = literal := by
  cases literal with
  | mk index value => cases value <;> rfl

@[simp] theorem eval_negate
    (literal : Literal n)
    (input : Fin n -> Bool) :
    literal.negate.eval input = !(literal.eval input) := by
  cases literal with
  | mk index value =>
      cases value <;> cases input index <;> simp [negate, eval]

end Literal

/-- A finite, noncontradictory collection of literals. The partial assignment
records the truth value required of each variable that occurs. -/
structure LiteralSet (n : Nat) where
  /-- Partial map from occurring variables to their satisfying values. -/
  requirements : PartialAssignment n
  deriving DecidableEq

namespace LiteralSet

/-- The empty collection of literals. -/
def empty : LiteralSet n :=
  ⟨PartialAssignment.empty⟩

/-- The one-element collection containing a literal. -/
def singleton (literal : Literal n) : LiteralSet n :=
  ⟨PartialAssignment.fix literal.index literal.value⟩

/-- Variables occurring in a literal collection. -/
def support (set : LiteralSet n) : Finset (Fin n) :=
  set.requirements.fixedVariables

@[simp] theorem mem_support
    (set : LiteralSet n)
    (index : Fin n) :
    index ∈ set.support ↔ set.requirements index ≠ none := by
  simp [support]

/-- Width of a literal collection. -/
def width (set : LiteralSet n) : Nat :=
  set.support.card

@[simp] theorem support_empty :
    (empty : LiteralSet n).support = {} := by
  apply Finset.ext
  intro index
  simp [support, empty]

@[simp] theorem width_empty :
    (empty : LiteralSet n).width = 0 := by
  simp [width]

/-- Remove the literals whose variables have been fixed by `rho`. This
operation does not itself check whether those fixed values satisfy or falsify
the removed literals. -/
def residual
    (set : LiteralSet n)
    (rho : PartialAssignment n) : LiteralSet n :=
  ⟨fun index =>
    match rho index with
    | none => set.requirements index
    | some _ => none⟩

@[simp] theorem residual_requirements_of_live
    (set : LiteralSet n)
    (rho : PartialAssignment n)
    {index : Fin n}
    (live : rho index = none) :
    (set.residual rho).requirements index = set.requirements index := by
  simp [residual, live]

@[simp] theorem residual_requirements_of_fixed
    (set : LiteralSet n)
    (rho : PartialAssignment n)
    {index : Fin n}
    {value : Bool}
    (fixed : rho index = some value) :
    (set.residual rho).requirements index = none := by
  simp [residual, fixed]

/-- Restriction only removes variables from a literal collection. -/
theorem support_residual_subset
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    (set.residual rho).support ⊆ set.support := by
  intro index present
  rw [mem_support] at present ⊢
  cases fixed : rho index with
  | none => simpa [residual, fixed] using present
  | some value => simp [residual, fixed] at present

/-- Every literal remaining after restriction is on a variable left live by
the restriction. -/
theorem support_residual_subset_live
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    (set.residual rho).support ⊆ rho.liveVariables := by
  intro index present
  rw [PartialAssignment.mem_liveVariables]
  cases fixed : rho index with
  | none => rfl
  | some value =>
      rw [mem_support] at present
      simp [residual, fixed] at present

/-- Restriction cannot increase the width of a literal collection. -/
theorem width_residual_le
    (set : LiteralSet n)
    (rho : PartialAssignment n) :
    (set.residual rho).width ≤ set.width :=
  Finset.card_le_card (support_residual_subset set rho)

/-- Some fixed literal of `set` is falsified by `rho`. -/
def ConflictsWith
    (set : LiteralSet n)
    (rho : PartialAssignment n) : Prop :=
  Exists fun index => Exists fun required => Exists fun fixed =>
    set.requirements index = some required ∧
      rho index = some fixed ∧ required ≠ fixed

instance conflictsWithDecidable
    (set : LiteralSet n)
    (rho : PartialAssignment n) : Decidable (set.ConflictsWith rho) := by
  unfold ConflictsWith
  infer_instance

/-- A conflict witnessed by an existing fixed variable persists under every
later refinement. -/
theorem ConflictsWith.refine
    {set : LiteralSet n}
    {rho : PartialAssignment n}
    (conflict : set.ConflictsWith rho)
    (extension : PartialAssignment n) :
    set.ConflictsWith (rho.refine extension) := by
  obtain ⟨index, required, fixed, setValue, rhoValue, different⟩ := conflict
  refine ⟨index, required, fixed, setValue, ?_, different⟩
  simp [PartialAssignment.refine, rhoValue]

/-- Some fixed literal of `set` is satisfied by `rho`. -/
def HitBy
    (set : LiteralSet n)
    (rho : PartialAssignment n) : Prop :=
  Exists fun index => Exists fun value =>
    set.requirements index = some value ∧ rho index = some value

instance hitByDecidable
    (set : LiteralSet n)
    (rho : PartialAssignment n) : Decidable (set.HitBy rho) := by
  unfold HitBy
  infer_instance

end LiteralSet

/-- A conjunction of distinct-variable literals. -/
abbrev Term (n : Nat) := LiteralSet n

namespace Term

/-- A complete input satisfies a term when it gives every occurring literal
its required value. -/
def SatisfiedBy
    (term : Term n)
    (input : Fin n -> Bool) : Prop :=
  forall index value,
    term.requirements index = some value -> input index = value

instance satisfiedByDecidable
    (term : Term n)
    (input : Fin n -> Bool) : Decidable (term.SatisfiedBy input) := by
  unfold SatisfiedBy
  infer_instance

/-- Boolean semantics of a term. The empty term is true. -/
def eval (term : Term n) (input : Fin n -> Bool) : Bool :=
  decide (term.SatisfiedBy input)

@[simp] theorem eval_eq_true
    (term : Term n)
    (input : Fin n -> Bool) :
    term.eval input = true ↔ term.SatisfiedBy input := by
  simp [eval]

@[simp] theorem eval_empty (input : Fin n -> Bool) :
    Term.eval (LiteralSet.empty : Term n) input = true := by
  simp [eval, SatisfiedBy, LiteralSet.empty]

/-- Restrict a term. `none` denotes a term made constantly false by a
conflicting fixed literal; otherwise the remaining live literals are returned.
-/
def restrict
    (term : Term n)
    (rho : PartialAssignment n) : Option (Term n) :=
  if term.ConflictsWith rho then none else some (term.residual rho)

/-- A conflicting partial assignment makes a term false under every completion.
-/
theorem eval_apply_eq_false_of_conflicts
    (term : Term n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    (conflict : term.ConflictsWith rho) :
    term.eval (rho.apply input) = false := by
  apply Bool.eq_false_iff.mpr
  intro trueValue
  obtain ⟨index, required, fixed, termValue, rhoValue, different⟩ := conflict
  have satisfies := (eval_eq_true term (rho.apply input)).1 trueValue
  have appliedRequired := satisfies index required termValue
  have appliedFixed := PartialAssignment.apply_of_fixed rho input rhoValue
  exact different (appliedRequired.symm.trans appliedFixed)

/-- In the absence of a conflict, evaluating the residual term is exactly
evaluation of the original term under the partial assignment. -/
theorem eval_residual_eq_eval_apply_of_not_conflicts
    (term : Term n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    (noConflict : ¬term.ConflictsWith rho) :
    Term.eval (term.residual rho) input = term.eval (rho.apply input) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true]
  constructor
  · intro residualSatisfied index required termValue
    cases rhoValue : rho index with
    | none =>
        rw [PartialAssignment.apply_of_live rho input rhoValue]
        apply residualSatisfied index required
        simpa [LiteralSet.residual, rhoValue] using termValue
    | some fixed =>
        have equal : required = fixed := by
          by_contra different
          exact noConflict ⟨index, required, fixed, termValue,
            rhoValue, different⟩
        simp [PartialAssignment.apply, rhoValue, equal]
  · intro sourceSatisfied index required residualValue
    cases rhoValue : rho index with
    | none =>
        have termValue : term.requirements index = some required := by
          simpa [LiteralSet.residual, rhoValue] using residualValue
        simpa [PartialAssignment.apply, rhoValue] using
          sourceSatisfied index required termValue
    | some fixed =>
        simp [LiteralSet.residual, rhoValue] at residualValue

/-- Total semantic specification of term restriction. -/
theorem restrict_sound
    (term : Term n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (term.restrict rho).elim false
        (fun residual => Term.eval residual input) =
      term.eval (rho.apply input) := by
  by_cases conflict : term.ConflictsWith rho
  · rw [restrict, ite_eq_left conflict]
    exact (eval_apply_eq_false_of_conflicts term rho input conflict).symm
  · rw [restrict, ite_eq_right conflict]
    exact eval_residual_eq_eval_apply_of_not_conflicts
      term rho input conflict

/-- Any residual returned by term restriction has no greater width than the
source term. -/
theorem width_restrict_le
    (term residual : Term n)
    (rho : PartialAssignment n)
    (restricted : term.restrict rho = some residual) :
    residual.width ≤ term.width := by
  by_cases conflict : term.ConflictsWith rho
  · simp [restrict, conflict] at restricted
  · rw [restrict, ite_eq_right conflict] at restricted
    injection restricted with equal
    subst residual
    exact LiteralSet.width_residual_le term rho

end Term

/-- A disjunction of distinct-variable literals. -/
abbrev Clause (n : Nat) := LiteralSet n

namespace Clause

/-- A complete input satisfies a clause when it satisfies at least one
occurring literal. -/
def SatisfiedBy
    (clause : Clause n)
    (input : Fin n -> Bool) : Prop :=
  Exists fun index => Exists fun value =>
    clause.requirements index = some value ∧ input index = value

instance satisfiedByDecidable
    (clause : Clause n)
    (input : Fin n -> Bool) : Decidable (clause.SatisfiedBy input) := by
  unfold SatisfiedBy
  infer_instance

/-- Boolean semantics of a clause. The empty clause is false. -/
def eval (clause : Clause n) (input : Fin n -> Bool) : Bool :=
  decide (clause.SatisfiedBy input)

@[simp] theorem eval_eq_true
    (clause : Clause n)
    (input : Fin n -> Bool) :
    clause.eval input = true ↔ clause.SatisfiedBy input := by
  simp [eval]

@[simp] theorem eval_empty (input : Fin n -> Bool) :
    Clause.eval (LiteralSet.empty : Clause n) input = false := by
  simp [eval, SatisfiedBy, LiteralSet.empty]

/-- Restrict a clause. `none` denotes a clause made constantly true by a
satisfied fixed literal; otherwise the remaining live literals are returned.
-/
def restrict
    (clause : Clause n)
    (rho : PartialAssignment n) : Option (Clause n) :=
  if clause.HitBy rho then none else some (clause.residual rho)

/-- A fixed literal satisfying a clause makes it true under every completion.
-/
theorem eval_apply_eq_true_of_hit
    (clause : Clause n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    (hit : clause.HitBy rho) :
    clause.eval (rho.apply input) = true := by
  apply (eval_eq_true clause (rho.apply input)).2
  obtain ⟨index, value, clauseValue, rhoValue⟩ := hit
  exact ⟨index, value, clauseValue,
    PartialAssignment.apply_of_fixed rho input rhoValue⟩

/-- If no fixed literal satisfies a clause, evaluating the residual clause is
exactly evaluation of the original clause under the partial assignment. -/
theorem eval_residual_eq_eval_apply_of_not_hit
    (clause : Clause n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool)
    (noHit : ¬clause.HitBy rho) :
    Clause.eval (clause.residual rho) input =
      clause.eval (rho.apply input) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true]
  constructor
  · rintro ⟨index, value, residualValue, inputValue⟩
    cases rhoValue : rho index with
    | none =>
        have clauseValue : clause.requirements index = some value := by
          simpa [LiteralSet.residual, rhoValue] using residualValue
        refine ⟨index, value, clauseValue, ?_⟩
        simpa [PartialAssignment.apply, rhoValue] using inputValue
    | some fixed =>
        simp [LiteralSet.residual, rhoValue] at residualValue
  · rintro ⟨index, value, clauseValue, appliedValue⟩
    cases rhoValue : rho index with
    | none =>
        refine ⟨index, value, ?_, ?_⟩
        · simpa [LiteralSet.residual, rhoValue] using clauseValue
        · simpa [PartialAssignment.apply, rhoValue] using appliedValue
    | some fixed =>
        have equal : fixed = value :=
          (PartialAssignment.apply_of_fixed rho input rhoValue).symm.trans
            appliedValue
        exfalso
        apply noHit
        refine ⟨index, value, clauseValue, ?_⟩
        simpa [equal] using rhoValue

/-- Total semantic specification of clause restriction. -/
theorem restrict_sound
    (clause : Clause n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (clause.restrict rho).elim true
        (fun residual => Clause.eval residual input) =
      clause.eval (rho.apply input) := by
  by_cases hit : clause.HitBy rho
  · rw [restrict, ite_eq_left hit]
    exact (eval_apply_eq_true_of_hit clause rho input hit).symm
  · rw [restrict, ite_eq_right hit]
    exact eval_residual_eq_eval_apply_of_not_hit clause rho input hit

/-- Any residual returned by clause restriction has no greater width than the
source clause. -/
theorem width_restrict_le
    (clause residual : Clause n)
    (rho : PartialAssignment n)
    (restricted : clause.restrict rho = some residual) :
    residual.width ≤ clause.width := by
  by_cases hit : clause.HitBy rho
  · simp [restrict, hit] at restricted
  · rw [restrict, ite_eq_right hit] at restricted
    injection restricted with equal
    subst residual
    exact LiteralSet.width_residual_le clause rho

end Clause

/-- An ordered disjunction of terms. Ordering is semantically irrelevant but
is retained for the canonical decision-tree construction. -/
structure DNF (n : Nat) where
  /-- Terms in the deterministic order used by canonical constructions. -/
  terms : List (Term n)
  deriving DecidableEq

namespace DNF

/-- Boolean semantics of a DNF. The empty list is false. -/
def eval (formula : DNF n) (input : Fin n -> Bool) : Bool :=
  formula.terms.any fun term => Term.eval term input

@[simp] theorem eval_eq_true
    (formula : DNF n)
    (input : Fin n -> Bool) :
    formula.eval input = true ↔
      Exists fun term => term ∈ formula.terms ∧ term.SatisfiedBy input := by
  rw [eval, List.any_eq_true]
  simp only [Term.eval_eq_true]

/-- The constantly false DNF. -/
def bottom : DNF n :=
  ⟨[]⟩

/-- The constantly true DNF, represented by one empty term. -/
def top : DNF n :=
  ⟨[LiteralSet.empty]⟩

@[simp] theorem eval_bottom (input : Fin n -> Bool) :
    (bottom : DNF n).eval input = false := rfl

@[simp] theorem eval_top (input : Fin n -> Bool) :
    (top : DNF n).eval input = true := by
  simp [eval, top]

/-- Every term in the DNF has width at most `bound`. -/
def WidthAtMost (formula : DNF n) (bound : Nat) : Prop :=
  forall term, term ∈ formula.terms -> term.width ≤ bound

/-- Restrict each term and discard those made constantly false. -/
def restrict
    (formula : DNF n)
    (rho : PartialAssignment n) : DNF n :=
  ⟨formula.terms.filterMap fun term => Term.restrict term rho⟩

/-- Restricting a DNF preserves its Boolean function exactly. -/
theorem restrict_sound
    (formula : DNF n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (formula.restrict rho).eval input =
      formula.eval (rho.apply input) := by
  change
    (formula.terms.filterMap fun term => Term.restrict term rho).any
        (fun term => Term.eval term input) =
      formula.terms.any (fun term => Term.eval term (rho.apply input))
  induction formula.terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      cases restrictedValue : Term.restrict term rho with
      | none =>
          have termSound := Term.restrict_sound term rho input
          rw [restrictedValue] at termSound
          simp only [Option.elim_none] at termSound
          simp [restrictedValue, ← termSound, inductionHypothesis]
      | some residual =>
          have termSound := Term.restrict_sound term rho input
          rw [restrictedValue] at termSound
          simp only [Option.elim_some] at termSound
          simp [restrictedValue, termSound, inductionHypothesis]

/-- Restriction preserves an upper bound on DNF term width. -/
theorem widthAtMost_restrict
    (formula : DNF n)
    (rho : PartialAssignment n)
    {bound : Nat}
    (bounded : formula.WidthAtMost bound) :
    (formula.restrict rho).WidthAtMost bound := by
  intro residual residualPresent
  obtain ⟨term, termPresent, restricted⟩ :=
    List.mem_filterMap.1 residualPresent
  exact (Term.width_restrict_le term residual rho restricted).trans
    (bounded term termPresent)

/-- A DNF width bound remains valid after increasing the allowance. -/
theorem WidthAtMost.mono
    {formula : DNF n}
    {smaller larger : Nat}
    (bounded : formula.WidthAtMost smaller)
    (le : smaller ≤ larger) :
    formula.WidthAtMost larger := by
  intro term present
  exact (bounded term present).trans le

end DNF

/-- An ordered conjunction of clauses. Ordering is retained so dual arguments
can use the same canonical conventions as DNF. -/
structure CNF (n : Nat) where
  /-- Clauses in a retained deterministic order. -/
  clauses : List (Clause n)
  deriving DecidableEq

namespace CNF

/-- Boolean semantics of a CNF. The empty list is true. -/
def eval (formula : CNF n) (input : Fin n -> Bool) : Bool :=
  formula.clauses.all fun clause => Clause.eval clause input

@[simp] theorem eval_eq_true
    (formula : CNF n)
    (input : Fin n -> Bool) :
    formula.eval input = true ↔
      forall clause, clause ∈ formula.clauses ->
        clause.SatisfiedBy input := by
  rw [eval, List.all_eq_true]
  simp only [Clause.eval_eq_true]

/-- The constantly true CNF. -/
def top : CNF n :=
  ⟨[]⟩

/-- The constantly false CNF, represented by one empty clause. -/
def bottom : CNF n :=
  ⟨[LiteralSet.empty]⟩

@[simp] theorem eval_top (input : Fin n -> Bool) :
    (top : CNF n).eval input = true := rfl

@[simp] theorem eval_bottom (input : Fin n -> Bool) :
    (bottom : CNF n).eval input = false := by
  simp [eval, bottom]

/-- Every clause in the CNF has width at most `bound`. -/
def WidthAtMost (formula : CNF n) (bound : Nat) : Prop :=
  forall clause, clause ∈ formula.clauses -> clause.width ≤ bound

/-- Restrict each clause and discard those made constantly true. -/
def restrict
    (formula : CNF n)
    (rho : PartialAssignment n) : CNF n :=
  ⟨formula.clauses.filterMap fun clause => Clause.restrict clause rho⟩

/-- Restricting a CNF preserves its Boolean function exactly. -/
theorem restrict_sound
    (formula : CNF n)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (formula.restrict rho).eval input =
      formula.eval (rho.apply input) := by
  change
    (formula.clauses.filterMap fun clause => Clause.restrict clause rho).all
        (fun clause => Clause.eval clause input) =
      formula.clauses.all (fun clause => Clause.eval clause (rho.apply input))
  induction formula.clauses with
  | nil => rfl
  | cons clause clauses inductionHypothesis =>
      cases restrictedValue : Clause.restrict clause rho with
      | none =>
          have clauseSound := Clause.restrict_sound clause rho input
          rw [restrictedValue] at clauseSound
          simp only [Option.elim_none] at clauseSound
          simp [restrictedValue, ← clauseSound, inductionHypothesis]
      | some residual =>
          have clauseSound := Clause.restrict_sound clause rho input
          rw [restrictedValue] at clauseSound
          simp only [Option.elim_some] at clauseSound
          simp [restrictedValue, clauseSound, inductionHypothesis]

/-- Restriction preserves an upper bound on CNF clause width. -/
theorem widthAtMost_restrict
    (formula : CNF n)
    (rho : PartialAssignment n)
    {bound : Nat}
    (bounded : formula.WidthAtMost bound) :
    (formula.restrict rho).WidthAtMost bound := by
  intro residual residualPresent
  obtain ⟨clause, clausePresent, restricted⟩ :=
    List.mem_filterMap.1 residualPresent
  exact (Clause.width_restrict_le clause residual rho restricted).trans
    (bounded clause clausePresent)

/-- A CNF width bound remains valid after increasing the allowance. -/
theorem WidthAtMost.mono
    {formula : CNF n}
    {smaller larger : Nat}
    (bounded : formula.WidthAtMost smaller)
    (le : smaller ≤ larger) :
    formula.WidthAtMost larger := by
  intro clause present
  exact (bounded clause present).trans le

end CNF

end AC0
end Algebraic
