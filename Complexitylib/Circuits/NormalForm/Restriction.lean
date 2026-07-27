/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.NormalForm.Defs
public import Complexitylib.Circuits.Restriction

/-!
# Restricting CNF and DNF formulas

Restriction performs the semantic simplification needed by switching-lemma
arguments:

* a satisfied CNF clause or falsified DNF term is removed;
* fixed literals with the neutral value are removed from their clause or term;
* free literals retain their order.

The result preserves evaluation and cannot increase clause/term count or width.

## Main results

* `CNF.eval_restrict` / `DNF.eval_restrict` -- semantic preservation.
* `CNF.complexity_restrict_le` / `DNF.complexity_restrict_le`.
* `CNF.width_restrict_le` / `DNF.width_restrict_le`.
-/

@[expose] public section

namespace Complexity

namespace Literal

/-- Evaluate a literal when its variable is fixed, or return `none` when the
variable remains free. -/
def restrictValue (ρ : Restriction.On N)
    (literal : Literal N) : Option Bool :=
  match ρ literal.var with
  | none => none
  | some value =>
      some (if literal.polarity then value else !value)

/-- A literal survives restriction exactly when its variable is free. -/
theorem restrictValue_eq_none_iff (ρ : Restriction.On N)
    (literal : Literal N) :
    literal.restrictValue ρ = none ↔
      ρ literal.var = none := by
  cases hvalue : ρ literal.var with
  | none => simp [restrictValue, hvalue]
  | some value =>
      cases literal.polarity <;> cases value <;>
        simp [restrictValue, hvalue]

/-- A fixed literal evaluates to true exactly when its variable is fixed to
the literal's polarity. -/
theorem restrictValue_eq_some_true_iff (ρ : Restriction.On N)
    (literal : Literal N) :
    literal.restrictValue ρ = some true ↔
      ρ literal.var = some literal.polarity := by
  cases hρ : ρ literal.var with
  | none => simp [restrictValue, hρ]
  | some value =>
      cases value <;> cases hpolarity : literal.polarity <;>
        simp [restrictValue, hρ, hpolarity]

/-- A fixed literal evaluates to false exactly when its variable is fixed
opposite to the literal's polarity. -/
theorem restrictValue_eq_some_false_iff (ρ : Restriction.On N)
    (literal : Literal N) :
    literal.restrictValue ρ = some false ↔
      ρ literal.var = some (!literal.polarity) := by
  cases hρ : ρ literal.var with
  | none => simp [restrictValue, hρ]
  | some value =>
      cases value <;> cases hpolarity : literal.polarity <;>
        simp [restrictValue, hρ, hpolarity]

/-- Restriction turns literal negation into Boolean negation of the fixed
value, while leaving a free literal free. -/
theorem restrictValue_neg (ρ : Restriction.On N)
    (literal : Literal N) :
    literal.neg.restrictValue ρ =
      (literal.restrictValue ρ).map (!·) := by
  cases hρ : ρ literal.var with
  | none => simp [restrictValue, Literal.neg, hρ]
  | some value =>
      cases literal.polarity <;> cases value <;>
        simp [restrictValue, Literal.neg, hρ]

/-- Restricting a literal by a left-biased composite first consults the first
restriction and then the second one. -/
theorem restrictValue_comp (first second : Restriction.On N)
    (literal : Literal N) :
    literal.restrictValue (Restriction.On.comp first second) =
      (literal.restrictValue first).or
        (literal.restrictValue second) := by
  cases hfirst : first literal.var with
  | none =>
      cases hsecond : second literal.var <;>
        cases literal.polarity <;>
        simp [restrictValue, Restriction.On.comp, hfirst, hsecond]
  | some value =>
      cases value <;> cases literal.polarity <;>
        simp [restrictValue, Restriction.On.comp, hfirst]

/-- A literal evaluated after applying a restriction is either its fixed value
or its value on the remaining assignment. -/
theorem eval_applyTo (ρ : Restriction.On N) (x : BitString N)
    (literal : Literal N) :
    literal.eval (ρ.applyTo x) =
      (literal.restrictValue ρ).getD (literal.eval x) := by
  cases h : ρ literal.var with
  | none =>
      simp [Restriction.On.applyTo, restrictValue, Literal.eval, h]
  | some value =>
      cases literal.polarity <;> cases value <;>
        simp [Restriction.On.applyTo, restrictValue, Literal.eval, h]

end Literal

namespace CNF

/-- Restrict one clause.

`none` means that a fixed true literal satisfies the clause. `some reduced`
contains the remaining free literals; `some []` is an unsatisfied empty clause. -/
def restrictClause (ρ : Restriction.On N) :
    List (Literal N) → Option (List (Literal N))
  | [] => some []
  | literal :: clause =>
      match literal.restrictValue ρ with
      | some true => none
      | some false => restrictClause ρ clause
      | none => (restrictClause ρ clause).map (literal :: ·)

/-- Simplify a CNF under a finite-arity restriction. -/
def restrict (ρ : Restriction.On N) (φ : CNF N) : CNF N :=
  ⟨φ.clauses.filterMap (restrictClause ρ)⟩

private theorem any_restrictClause (ρ : Restriction.On N)
    (x : BitString N) (clause : List (Literal N)) :
    (match restrictClause ρ clause with
    | none => true
    | some reduced =>
        reduced.any fun literal => literal.eval x) =
      clause.any fun literal => literal.eval (ρ.applyTo x) := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      rw [List.any_cons, Literal.eval_applyTo]
      cases h : literal.restrictValue ρ with
      | none =>
          cases hr : restrictClause ρ clause with
          | none =>
              rw [hr] at ih
              simp only at ih
              simp only [restrictClause, h, hr, Option.map_none,
                Option.getD_none]
              rw [← ih]
              simp
          | some reduced =>
              rw [hr] at ih
              simp only at ih
              simp only [restrictClause, h, hr, Option.map_some,
                List.any_cons, Option.getD_none]
              rw [ih]
      | some value =>
          cases value with
          | false =>
              simp only [restrictClause, h, Option.getD_some]
              exact ih
          | true =>
              simp [restrictClause, h, Option.getD_some]

/-- Restricting a CNF and then evaluating it agrees with evaluating the
original CNF after applying the restriction to its assignment. -/
theorem eval_restrict (ρ : Restriction.On N) (x : BitString N)
    (φ : CNF N) :
    (restrict ρ φ).eval x = φ.eval (ρ.applyTo x) := by
  rcases φ with ⟨clauses⟩
  change (List.filterMap (restrictClause ρ) clauses).all
      (fun clause => clause.any fun literal => literal.eval x) =
    clauses.all
      (fun clause =>
        clause.any fun literal => literal.eval (ρ.applyTo x))
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      have hclause := any_restrictClause ρ x clause
      cases h : restrictClause ρ clause with
      | none =>
          rw [h] at hclause
          simp only at hclause
          simp only [List.filterMap_cons, h, List.all_cons]
          rw [ih, ← hclause]
          simp
      | some reduced =>
          rw [h] at hclause
          simp only at hclause
          simp only [List.filterMap_cons, h, List.all_cons]
          rw [ih, hclause]

private theorem length_restrictClause_le (ρ : Restriction.On N)
    {clause reduced : List (Literal N)}
    (h : restrictClause ρ clause = some reduced) :
    reduced.length ≤ clause.length := by
  induction clause generalizing reduced with
  | nil =>
      simp [restrictClause] at h
      subst reduced
      rfl
  | cons literal clause ih =>
      cases hl : literal.restrictValue ρ with
      | none =>
          simp only [restrictClause, hl] at h
          cases hr : restrictClause ρ clause with
          | none => simp [hr] at h
          | some tail =>
              simp [hr] at h
              subst reduced
              simpa only [List.length_cons] using
                Nat.succ_le_succ (ih hr)
      | some value =>
          cases value with
          | false =>
              simp only [restrictClause, hl] at h
              exact (ih h).trans (Nat.le_succ _)
          | true => simp [restrictClause, hl] at h

private theorem mem_restrictClause (ρ : Restriction.On N)
    {clause reduced : List (Literal N)}
    (hrestrict : restrictClause ρ clause = some reduced)
    {literal : Literal N} (hmem : literal ∈ reduced) :
    literal ∈ clause ∧ ρ literal.var = none := by
  induction clause generalizing reduced with
  | nil =>
      simp [restrictClause] at hrestrict
      subst reduced
      simp at hmem
  | cons head tail ih =>
      cases hvalue : head.restrictValue ρ with
      | none =>
          cases htail : restrictClause ρ tail with
          | none =>
              simp [restrictClause, hvalue, htail] at hrestrict
          | some reducedTail =>
              simp [restrictClause, hvalue, htail] at hrestrict
              subst reduced
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨by simp,
                  (Literal.restrictValue_eq_none_iff ρ literal).mp
                    hvalue⟩
              · have hresult := ih htail hmem
                exact ⟨by simp [hresult.1], hresult.2⟩
      | some value =>
          cases value with
          | false =>
              simp only [restrictClause, hvalue] at hrestrict
              have hresult := ih hrestrict hmem
              exact ⟨by simp [hresult.1], hresult.2⟩
          | true =>
              simp [restrictClause, hvalue] at hrestrict

/-- Restriction cannot increase a CNF's number of clauses. -/
theorem complexity_restrict_le (ρ : Restriction.On N) (φ : CNF N) :
    (restrict ρ φ).complexity ≤ φ.complexity := by
  rcases φ with ⟨clauses⟩
  change
    (List.filterMap (restrictClause ρ) clauses).length ≤ clauses.length
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      rw [List.filterMap_cons]
      cases restrictClause ρ clause <;> simp <;> omega

/-- Restriction cannot increase a CNF's maximum clause width. -/
theorem width_restrict_le (ρ : Restriction.On N) (φ : CNF N) :
    (restrict ρ φ).width ≤ φ.width := by
  rcases φ with ⟨clauses⟩
  change
    (List.filterMap (restrictClause ρ) clauses).foldr
        (fun clause rest => max clause.length rest) 0 ≤
      clauses.foldr (fun clause rest => max clause.length rest) 0
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      rw [List.filterMap_cons]
      cases h : restrictClause ρ clause with
      | none =>
          simp only
          exact ih.trans (le_max_right _ _)
      | some reduced =>
          simp only [List.foldr_cons]
          exact max_le_max (length_restrictClause_le ρ h) ih

/-- Every variable surviving CNF simplification occurred originally and is
free under the restriction. -/
theorem vars_restrict_subset_filter (ρ : Restriction.On N)
    (φ : CNF N) :
    (restrict ρ φ).vars ⊆
      φ.vars.filter fun index => ρ index = none := by
  rcases φ with ⟨clauses⟩
  intro index hindex
  rw [CNF.mem_vars_iff] at hindex
  obtain ⟨reduced, hreduced, literal, hliteral, hvar⟩ :=
    hindex
  simp only [restrict] at hreduced
  rw [List.mem_filterMap] at hreduced
  obtain ⟨clause, hclause, hrestrict⟩ := hreduced
  have hsurvives :=
    mem_restrictClause ρ hrestrict hliteral
  rw [Finset.mem_filter, CNF.mem_vars_iff]
  exact ⟨⟨clause, hclause, literal, hsurvives.1, hvar⟩,
    hvar ▸ hsurvives.2⟩

end CNF

namespace DNF

/-- Restrict one term.

`none` means that a fixed false literal falsifies the term. `some reduced`
contains the remaining free literals; `some []` is a satisfied empty term. -/
def restrictTerm (ρ : Restriction.On N) :
    List (Literal N) → Option (List (Literal N))
  | [] => some []
  | literal :: term =>
      match literal.restrictValue ρ with
      | some false => none
      | some true => restrictTerm ρ term
      | none => (restrictTerm ρ term).map (literal :: ·)

/-- Restricting the negation of a CNF clause agrees with restricting the
clause and negating every surviving literal. -/
theorem restrictTerm_map_neg (ρ : Restriction.On N)
    (clause : List (Literal N)) :
    restrictTerm ρ (clause.map Literal.neg) =
      (CNF.restrictClause ρ clause).map
        (List.map Literal.neg) := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp only [List.map_cons, restrictTerm,
        CNF.restrictClause, Literal.restrictValue_neg]
      cases h : literal.restrictValue ρ with
      | none =>
          rw [ih]
          cases CNF.restrictClause ρ clause <;> rfl
      | some value =>
          cases value with
          | false => exact ih
          | true => rfl

/-- Simplify a DNF under a finite-arity restriction. -/
def restrict (ρ : Restriction.On N) (φ : DNF N) : DNF N :=
  ⟨φ.terms.filterMap (restrictTerm ρ)⟩

/-- A DNF term survives exactly when each of its fixed literals is fixed to
its satisfying polarity. -/
theorem exists_restrictTerm_eq_some_iff
    (ρ : Restriction.On N) (term : List (Literal N)) :
    (∃ reduced, restrictTerm ρ term = some reduced) ↔
      ∀ literal ∈ term,
        ρ literal.var = none ∨
          ρ literal.var = some literal.polarity := by
  induction term with
  | nil => simp [restrictTerm]
  | cons literal tail ih =>
      cases hρ : ρ literal.var with
      | none =>
          simp [restrictTerm, Literal.restrictValue, hρ, ih]
      | some value =>
          cases value <;> cases hpolarity : literal.polarity <;>
            simp [restrictTerm, Literal.restrictValue,
              hρ, hpolarity, ih]

/-- When a term survives, its exact reduction is obtained by retaining
precisely the literals whose variables remain free. -/
theorem restrictTerm_eq_some_filter_iff
    (ρ : Restriction.On N) (term : List (Literal N)) :
    restrictTerm ρ term =
        some (term.filter fun literal => ρ literal.var = none) ↔
      ∀ literal ∈ term,
        ρ literal.var = none ∨
          ρ literal.var = some literal.polarity := by
  induction term with
  | nil => simp [restrictTerm]
  | cons literal tail ih =>
      cases hρ : ρ literal.var with
      | none =>
          simp [restrictTerm, Literal.restrictValue, hρ, ih]
      | some value =>
          cases value <;> cases hpolarity : literal.polarity <;>
            simp [restrictTerm, Literal.restrictValue,
              hρ, hpolarity, ih]

/-- Successively restricting one term agrees exactly with restricting by the
left-biased composite. -/
theorem restrictTerm_comp (first second : Restriction.On N)
    (term : List (Literal N)) :
    restrictTerm (Restriction.On.comp first second) term =
      (restrictTerm first term).bind (restrictTerm second) := by
  induction term with
  | nil => rfl
  | cons literal tail ih =>
      simp only [restrictTerm, Literal.restrictValue_comp]
      cases hfirst : literal.restrictValue first with
      | none =>
          cases hsecond : literal.restrictValue second with
          | none =>
              cases htail : restrictTerm first tail <;>
                simp_all [restrictTerm]
          | some value =>
              cases value <;>
                cases htail : restrictTerm first tail <;>
                simp_all [restrictTerm]
      | some value =>
          cases value <;> simp_all

/-- Once a term is killed, every extension of the restriction also kills it. -/
theorem restrictTerm_comp_eq_none_of_eq_none
    (first second : Restriction.On N)
    (term : List (Literal N))
    (hkilled : restrictTerm first term = none) :
    restrictTerm (Restriction.On.comp first second) term = none := by
  rw [restrictTerm_comp, hkilled]
  rfl

/-- Applying two DNF restrictions successively is syntactically identical to
applying their left-biased composite once. -/
theorem restrict_comp (first second : Restriction.On N)
    (formula : DNF N) :
    restrict second (restrict first formula) =
      restrict (Restriction.On.comp first second) formula := by
  rcases formula with ⟨terms⟩
  simp only [restrict]
  rw [List.filterMap_filterMap]
  congr 1
  apply congrArg (fun operation => terms.filterMap operation)
  funext term
  exact (restrictTerm_comp first second term).symm

private theorem all_restrictTerm (ρ : Restriction.On N)
    (x : BitString N) (term : List (Literal N)) :
    (match restrictTerm ρ term with
    | none => false
    | some reduced =>
        reduced.all fun literal => literal.eval x) =
      term.all fun literal => literal.eval (ρ.applyTo x) := by
  induction term with
  | nil => rfl
  | cons literal term ih =>
      rw [List.all_cons, Literal.eval_applyTo]
      cases h : literal.restrictValue ρ with
      | none =>
          cases hr : restrictTerm ρ term with
          | none =>
              rw [hr] at ih
              simp only at ih
              simp only [restrictTerm, h, hr, Option.map_none,
                Option.getD_none]
              rw [← ih]
              simp
          | some reduced =>
              rw [hr] at ih
              simp only at ih
              simp only [restrictTerm, h, hr, Option.map_some,
                List.all_cons, Option.getD_none]
              rw [ih]
      | some value =>
          cases value with
          | false => simp [restrictTerm, h, Option.getD_some]
          | true =>
              simp only [restrictTerm, h, Option.getD_some]
              exact ih

/-- Restricting a DNF and then evaluating it agrees with evaluating the
original DNF after applying the restriction to its assignment. -/
theorem eval_restrict (ρ : Restriction.On N) (x : BitString N)
    (φ : DNF N) :
    (restrict ρ φ).eval x = φ.eval (ρ.applyTo x) := by
  rcases φ with ⟨terms⟩
  change (List.filterMap (restrictTerm ρ) terms).any
      (fun term => term.all fun literal => literal.eval x) =
    terms.any
      (fun term =>
        term.all fun literal => literal.eval (ρ.applyTo x))
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      have hterm := all_restrictTerm ρ x term
      cases h : restrictTerm ρ term with
      | none =>
          rw [h] at hterm
          simp only at hterm
          simp only [List.filterMap_cons, h, List.any_cons]
          rw [ih, ← hterm]
          simp
      | some reduced =>
          rw [h] at hterm
          simp only at hterm
          simp only [List.filterMap_cons, h, List.any_cons]
          rw [ih, hterm]

private theorem length_restrictTerm_le (ρ : Restriction.On N)
    {term reduced : List (Literal N)}
    (h : restrictTerm ρ term = some reduced) :
    reduced.length ≤ term.length := by
  induction term generalizing reduced with
  | nil =>
      simp [restrictTerm] at h
      subst reduced
      rfl
  | cons literal term ih =>
      cases hl : literal.restrictValue ρ with
      | none =>
          simp only [restrictTerm, hl] at h
          cases hr : restrictTerm ρ term with
          | none => simp [hr] at h
          | some tail =>
              simp [hr] at h
              subst reduced
              simpa only [List.length_cons] using
                Nat.succ_le_succ (ih hr)
      | some value =>
          cases value with
          | false => simp [restrictTerm, hl] at h
          | true =>
              simp only [restrictTerm, hl] at h
              exact (ih h).trans (Nat.le_succ _)

/-- Every literal retained in a restricted DNF term occurred originally and
its variable is free under the restriction. -/
theorem mem_of_mem_restrictTerm (ρ : Restriction.On N)
    {term reduced : List (Literal N)}
    (hrestrict : restrictTerm ρ term = some reduced)
    {literal : Literal N} (hmem : literal ∈ reduced) :
    literal ∈ term ∧ ρ literal.var = none := by
  induction term generalizing reduced with
  | nil =>
      simp [restrictTerm] at hrestrict
      subst reduced
      simp at hmem
  | cons head tail ih =>
      cases hvalue : head.restrictValue ρ with
      | none =>
          cases htail : restrictTerm ρ tail with
          | none =>
              simp [restrictTerm, hvalue, htail] at hrestrict
          | some reducedTail =>
              simp [restrictTerm, hvalue, htail] at hrestrict
              subst reduced
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | hmem
              · exact ⟨by simp,
                  (Literal.restrictValue_eq_none_iff ρ literal).mp
                    hvalue⟩
              · have hresult := ih htail hmem
                exact ⟨by simp [hresult.1], hresult.2⟩
      | some value =>
          cases value with
          | false =>
              simp [restrictTerm, hvalue] at hrestrict
          | true =>
              simp only [restrictTerm, hvalue] at hrestrict
              have hresult := ih hrestrict hmem
              exact ⟨by simp [hresult.1], hresult.2⟩

/-- Restriction cannot increase a DNF's number of terms. -/
theorem complexity_restrict_le (ρ : Restriction.On N) (φ : DNF N) :
    (restrict ρ φ).complexity ≤ φ.complexity := by
  rcases φ with ⟨terms⟩
  change
    (List.filterMap (restrictTerm ρ) terms).length ≤ terms.length
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rw [List.filterMap_cons]
      cases restrictTerm ρ term <;> simp <;> omega

/-- Restriction cannot increase a DNF's maximum term width. -/
theorem width_restrict_le (ρ : Restriction.On N) (φ : DNF N) :
    (restrict ρ φ).width ≤ φ.width := by
  rcases φ with ⟨terms⟩
  change
    (List.filterMap (restrictTerm ρ) terms).foldr
        (fun term rest => max term.length rest) 0 ≤
      terms.foldr (fun term rest => max term.length rest) 0
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rw [List.filterMap_cons]
      cases h : restrictTerm ρ term with
      | none =>
          simp only
          exact ih.trans (le_max_right _ _)
      | some reduced =>
          simp only [List.foldr_cons]
          exact max_le_max (length_restrictTerm_le ρ h) ih

/-- Every variable surviving DNF simplification occurred originally and is
free under the restriction. -/
theorem vars_restrict_subset_filter (ρ : Restriction.On N)
    (φ : DNF N) :
    (restrict ρ φ).vars ⊆
      φ.vars.filter fun index => ρ index = none := by
  rcases φ with ⟨terms⟩
  intro index hindex
  rw [DNF.mem_vars_iff] at hindex
  obtain ⟨reduced, hreduced, literal, hliteral, hvar⟩ :=
    hindex
  simp only [restrict] at hreduced
  rw [List.mem_filterMap] at hreduced
  obtain ⟨term, hterm, hrestrict⟩ := hreduced
  have hsurvives :=
    mem_of_mem_restrictTerm ρ hrestrict hliteral
  rw [Finset.mem_filter, DNF.mem_vars_iff]
  exact ⟨⟨term, hterm, literal, hsurvives.1, hvar⟩,
    hvar ▸ hsurvives.2⟩

end DNF

namespace CNF

/-- Restricting the negation of a DNF term agrees with restricting the term
and negating every surviving literal. -/
theorem restrictClause_map_neg (ρ : Restriction.On N)
    (term : List (Literal N)) :
    restrictClause ρ (term.map Literal.neg) =
      (DNF.restrictTerm ρ term).map
        (List.map Literal.neg) := by
  induction term with
  | nil => rfl
  | cons literal term ih =>
      simp only [List.map_cons, restrictClause,
        DNF.restrictTerm, Literal.restrictValue_neg]
      cases h : literal.restrictValue ρ with
      | none =>
          rw [ih]
          cases DNF.restrictTerm ρ term <;> rfl
      | some value =>
          cases value with
          | false => rfl
          | true => exact ih

/-- Restriction commutes exactly with De Morgan negation from CNF to DNF. -/
theorem neg_restrict (ρ : Restriction.On N)
    (formula : CNF N) :
    (formula.restrict ρ).neg =
      formula.neg.restrict ρ := by
  rcases formula with ⟨clauses⟩
  simp only [CNF.restrict, CNF.neg, DNF.restrict]
  congr 1
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      rw [List.map_cons, List.filterMap_cons,
        List.filterMap_cons, DNF.restrictTerm_map_neg]
      cases CNF.restrictClause ρ clause <;> simp [ih]

end CNF

namespace DNF

/-- Restriction commutes exactly with De Morgan negation from DNF to CNF. -/
theorem neg_restrict (ρ : Restriction.On N)
    (formula : DNF N) :
    (formula.restrict ρ).neg =
      formula.neg.restrict ρ := by
  rcases formula with ⟨terms⟩
  simp only [DNF.restrict, DNF.neg, CNF.restrict]
  congr 1
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rw [List.map_cons, List.filterMap_cons,
        List.filterMap_cons, CNF.restrictClause_map_neg]
      cases DNF.restrictTerm ρ term <;> simp [ih]

end DNF

end Complexity
