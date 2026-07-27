/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Basic
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

/-! # Normal Forms — Core Definitions

This module defines Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF)
Boolean formulas over `N` variables, together with their evaluation semantics,
complexity measures, and De Morgan negation duality.

## Main definitions

* `Literal` — a Boolean variable with a polarity flag (positive or negative)
* `CNF` — a conjunction of clauses (each clause is a disjunction of literals)
* `DNF` — a disjunction of terms (each term is a conjunction of literals)
* `CNF.complexity` — the number of clauses in a CNF formula
* `DNF.complexity` — the number of terms in a DNF formula
* `CNF.width` / `DNF.width` — the largest clause/term length
* `CNF.neg` / `DNF.neg` — De Morgan negation (CNF ↔ DNF)

## Relation to `Complexity.SAT`

`Complexity.Literal`, `Complexity.CNF`, and `Complexity.DNF` are deliberately distinct from
`Complexity.SAT.Lit` and `Complexity.SAT.CNF`. The types here are `Fin`-indexed over a fixed
variable count `N` and are used for circuit lower bounds, whereas the `SAT` versions are
`Nat`-indexed and serve as the language encoding for SAT.
-/

@[expose] public section

namespace Complexity

/-- A literal: a Boolean variable (by index) together with a polarity flag.

`polarity = true` represents the positive literal xᵢ;
`polarity = false` represents the negative literal ¬xᵢ. -/
structure Literal (N : Nat) where
  /-- The index of the Boolean variable this literal refers to. -/
  var : Fin N
  /-- `true` = positive literal (xᵢ); `false` = negative literal (¬xᵢ). -/
  polarity : Bool
  deriving Repr, DecidableEq

-- These record printers intentionally ignore precedence.
attribute [nolint unusedArguments] instReprLiteral.repr

/-- Evaluate a literal on a bit assignment. -/
def Literal.eval (l : Literal N) (x : BitString N) : Bool :=
  if l.polarity then x l.var else !x l.var

/-- Negate a literal by flipping its polarity. -/
def Literal.neg (l : Literal N) : Literal N :=
  { l with polarity := !l.polarity }

/-- Literal negation is an involution. -/
@[simp] theorem Literal.neg_neg (literal : Literal N) :
    literal.neg.neg = literal := by
  rcases literal with ⟨var, polarity⟩
  simp [Literal.neg]

/-- Negating a literal negates its evaluation. -/
theorem Literal.eval_neg (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by
  simp [Literal.neg, Literal.eval]
  cases l.polarity <;> simp

/-- The set of variables occurring in a list of literals. -/
def Literal.vars (literals : List (Literal N)) : Finset (Fin N) :=
  literals.foldr (fun literal support =>
    insert literal.var support) ∅

@[simp] theorem Literal.vars_nil :
    Literal.vars ([] : List (Literal N)) = ∅ := rfl

@[simp] theorem Literal.vars_cons (literal : Literal N)
    (literals : List (Literal N)) :
    Literal.vars (literal :: literals) =
      insert literal.var (Literal.vars literals) := rfl

theorem Literal.mem_vars_iff (literals : List (Literal N))
    (index : Fin N) :
    index ∈ Literal.vars literals ↔
      ∃ literal ∈ literals, literal.var = index := by
  induction literals with
  | nil => simp
  | cons literal literals ih =>
      simp only [Literal.vars_cons, Finset.mem_insert,
        List.mem_cons]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨literal, Or.inl rfl, h.symm⟩
        · obtain ⟨found, hmem, hvar⟩ := h
          exact ⟨found, Or.inr hmem, hvar⟩
      · rintro ⟨found, hmem, hvar⟩
        rcases hmem with rfl | hmem
        · exact Or.inl hvar.symm
        · exact Or.inr ⟨found, hmem, hvar⟩

/-! ## CNF -/

/--
A CNF (Conjunctive Normal Form) formula over `N` Boolean variables.

A CNF is a conjunction of clauses, where each clause is a disjunction of literals.
-/
structure CNF (N : Nat) where
  /-- The clauses of the formula. Each clause is a list of literals. -/
  clauses : List (List (Literal N))
  deriving Repr, DecidableEq

-- These record printers intentionally ignore precedence.
attribute [nolint unusedArguments] instReprCNF.repr

namespace CNF

/-- A CNF formula evaluates to `true` iff every clause contains at least one
satisfied literal. -/
def eval (φ : CNF N) (x : BitString N) : Bool :=
  φ.clauses.all fun clause => clause.any fun l => l.eval x

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length

/-- The width of a CNF is the maximum number of literals in any clause. -/
def width (φ : CNF N) : Nat :=
  φ.clauses.foldr (fun clause rest => max clause.length rest) 0

/-- Every clause length is bounded by the declared CNF width. -/
theorem length_le_width (φ : CNF N)
    (clause : List (Literal N)) (hclause : clause ∈ φ.clauses) :
    clause.length ≤ φ.width := by
  rcases φ with ⟨clauses⟩
  induction clauses with
  | nil => simp at hclause
  | cons head tail ih =>
      simp only [List.mem_cons] at hclause
      simp only [width, List.foldr_cons]
      rcases hclause with rfl | hclause
      · exact le_max_left _ _
      · exact (ih hclause).trans (le_max_right _ _)

/-- A natural number bounds CNF width exactly when it bounds every clause
length. -/
theorem width_le_iff (φ : CNF N) (bound : ℕ) :
    φ.width ≤ bound ↔
      ∀ clause ∈ φ.clauses, clause.length ≤ bound := by
  rcases φ with ⟨clauses⟩
  induction clauses with
  | nil => simp [width]
  | cons clause clauses ih =>
      simp only [width, List.foldr_cons, max_le_iff,
        List.mem_cons, forall_eq_or_imp]
      exact and_congr_right fun _ => ih

/-- The set of variables occurring in a CNF. -/
def vars (φ : CNF N) : Finset (Fin N) :=
  φ.clauses.foldr
    (fun clause rest => Literal.vars clause ∪ rest) ∅

@[simp] theorem vars_nil :
    vars (⟨[]⟩ : CNF N) = ∅ := rfl

@[simp] theorem vars_cons (clause : List (Literal N))
    (clauses : List (List (Literal N))) :
    vars (⟨clause :: clauses⟩ : CNF N) =
      Literal.vars clause ∪ vars ⟨clauses⟩ := rfl

theorem mem_vars_iff (φ : CNF N) (index : Fin N) :
    index ∈ φ.vars ↔
      ∃ clause ∈ φ.clauses,
        ∃ literal ∈ clause, literal.var = index := by
  rcases φ with ⟨clauses⟩
  induction clauses with
  | nil => simp
  | cons clause clauses ih =>
      simp only [vars_cons, Finset.mem_union,
        Literal.mem_vars_iff, List.mem_cons]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · obtain ⟨literal, hmem, hvar⟩ := h
          exact ⟨clause, Or.inl rfl, literal, hmem, hvar⟩
        · obtain ⟨found, hmem, literal, hliteral, hvar⟩ := h
          exact ⟨found, Or.inr hmem, literal, hliteral, hvar⟩
      · rintro ⟨found, hmem, literal, hliteral, hvar⟩
        rcases hmem with rfl | hmem
        · exact Or.inl ⟨literal, hliteral, hvar⟩
        · exact Or.inr ⟨found, hmem, literal, hliteral, hvar⟩

end CNF

/-! ## DNF -/

/--
A DNF (Disjunctive Normal Form) formula over `N` Boolean variables.

A DNF is a disjunction of terms, where each term is a conjunction of literals.
-/
structure DNF (N : Nat) where
  /-- The terms of the formula. Each term is a list of literals. -/
  terms : List (List (Literal N))
  deriving Repr, DecidableEq

-- These record printers intentionally ignore precedence.
attribute [nolint unusedArguments] instReprDNF.repr

namespace DNF

/-- A DNF formula evaluates to `true` iff at least one term has all its
literals satisfied. -/
def eval (φ : DNF N) (x : BitString N) : Bool :=
  φ.terms.any fun term => term.all fun l => l.eval x

/-- The complexity of a DNF formula is its number of terms. -/
def complexity (φ : DNF N) : Nat := φ.terms.length

/-- The width of a DNF is the maximum number of literals in any term. -/
def width (φ : DNF N) : Nat :=
  φ.terms.foldr (fun term rest => max term.length rest) 0

/-- Every term length is bounded by the declared DNF width. -/
theorem length_le_width (φ : DNF N)
    (term : List (Literal N)) (hterm : term ∈ φ.terms) :
    term.length ≤ φ.width := by
  rcases φ with ⟨terms⟩
  induction terms with
  | nil => simp at hterm
  | cons head tail ih =>
      simp only [List.mem_cons] at hterm
      simp only [width, List.foldr_cons]
      rcases hterm with rfl | hterm
      · exact le_max_left _ _
      · exact (ih hterm).trans (le_max_right _ _)

/-- A natural number bounds DNF width exactly when it bounds every term
length. -/
theorem width_le_iff (φ : DNF N) (bound : ℕ) :
    φ.width ≤ bound ↔
      ∀ term ∈ φ.terms, term.length ≤ bound := by
  rcases φ with ⟨terms⟩
  induction terms with
  | nil => simp [width]
  | cons term terms ih =>
      simp only [width, List.foldr_cons, max_le_iff,
        List.mem_cons, forall_eq_or_imp]
      exact and_congr_right fun _ => ih

/-- The set of variables occurring in a DNF. -/
def vars (φ : DNF N) : Finset (Fin N) :=
  φ.terms.foldr
    (fun term rest => Literal.vars term ∪ rest) ∅

@[simp] theorem vars_nil :
    vars (⟨[]⟩ : DNF N) = ∅ := rfl

@[simp] theorem vars_cons (term : List (Literal N))
    (terms : List (List (Literal N))) :
    vars (⟨term :: terms⟩ : DNF N) =
      Literal.vars term ∪ vars ⟨terms⟩ := rfl

theorem mem_vars_iff (φ : DNF N) (index : Fin N) :
    index ∈ φ.vars ↔
      ∃ term ∈ φ.terms,
        ∃ literal ∈ term, literal.var = index := by
  rcases φ with ⟨terms⟩
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [vars_cons, Finset.mem_union,
        Literal.mem_vars_iff, List.mem_cons]
      rw [ih]
      constructor
      · intro h
        rcases h with h | h
        · obtain ⟨literal, hmem, hvar⟩ := h
          exact ⟨term, Or.inl rfl, literal, hmem, hvar⟩
        · obtain ⟨found, hmem, literal, hliteral, hvar⟩ := h
          exact ⟨found, Or.inr hmem, literal, hliteral, hvar⟩
      · rintro ⟨found, hmem, literal, hliteral, hvar⟩
        rcases hmem with rfl | hmem
        · exact Or.inl ⟨literal, hliteral, hvar⟩
        · exact Or.inr ⟨found, hmem, literal, hliteral, hvar⟩

end DNF

/-! ## De Morgan Negation Duality -/

/-- Negate a CNF formula by flipping all literal polarities, producing a DNF.
By De Morgan's laws, `¬(∧ᵢ ∨ⱼ lᵢⱼ) = ∨ᵢ ∧ⱼ ¬lᵢⱼ`. -/
def CNF.neg (φ : CNF N) : DNF N :=
  ⟨φ.clauses.map (fun clause => clause.map Literal.neg)⟩

/-- Negate a DNF formula by flipping all literal polarities, producing a CNF.
By De Morgan's laws, `¬(∨ᵢ ∧ⱼ lᵢⱼ) = ∧ᵢ ∨ⱼ ¬lᵢⱼ`. -/
def DNF.neg (φ : DNF N) : CNF N :=
  ⟨φ.terms.map (fun term => term.map Literal.neg)⟩

private theorem Literal.map_neg_neg
    (literals : List (Literal N)) :
    (literals.map Literal.neg).map Literal.neg = literals := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp only [List.map_cons, Literal.neg_neg, ih]

/-- De Morgan negation from CNF to DNF and back is an involution. -/
@[simp] theorem CNF.neg_neg (φ : CNF N) :
    φ.neg.neg = φ := by
  rcases φ with ⟨clauses⟩
  simp only [CNF.neg, DNF.neg]
  congr 1
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.map_cons, Literal.map_neg_neg, ih]

/-- De Morgan negation from DNF to CNF and back is an involution. -/
@[simp] theorem DNF.neg_neg (φ : DNF N) :
    φ.neg.neg = φ := by
  rcases φ with ⟨terms⟩
  simp only [DNF.neg, CNF.neg]
  congr 1
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      simp only [List.map_cons, Literal.map_neg_neg, ih]

/-- Negating a CNF formula negates its evaluation (De Morgan duality). -/
theorem CNF.eval_neg (φ : CNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [CNF.neg, DNF.eval, CNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a DNF formula negates its evaluation (De Morgan duality). -/
theorem DNF.eval_neg (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [DNF.neg, CNF.eval, DNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

private theorem Literal.vars_map_neg
    (literals : List (Literal N)) :
    Literal.vars (literals.map Literal.neg) =
      Literal.vars literals := by
  induction literals with
  | nil => rfl
  | cons literal literals ih =>
      simp only [List.map_cons, Literal.vars_cons]
      change insert literal.var
          (Literal.vars (literals.map Literal.neg)) =
        insert literal.var (Literal.vars literals)
      rw [ih]

/-- Negating a CNF preserves its variable support. -/
theorem CNF.vars_neg (φ : CNF N) :
    φ.neg.vars = φ.vars := by
  rcases φ with ⟨clauses⟩
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change Literal.vars (clause.map Literal.neg) ∪
          (⟨clauses⟩ : CNF N).neg.vars =
        Literal.vars clause ∪ (⟨clauses⟩ : CNF N).vars
      rw [Literal.vars_map_neg, ih]

/-- Negating a DNF preserves its variable support. -/
theorem DNF.vars_neg (φ : DNF N) :
    φ.neg.vars = φ.vars := by
  rcases φ with ⟨terms⟩
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      change Literal.vars (term.map Literal.neg) ∪
          (⟨terms⟩ : DNF N).neg.vars =
        Literal.vars term ∪ (⟨terms⟩ : DNF N).vars
      rw [Literal.vars_map_neg, ih]

/-- Negating a CNF preserves complexity. -/
theorem CNF.complexity_neg (φ : CNF N) : φ.neg.complexity = φ.complexity := by
  simp [CNF.neg, DNF.complexity, CNF.complexity, List.length_map]

/-- Negating a DNF preserves complexity. -/
theorem DNF.complexity_neg (φ : DNF N) :
    φ.neg.complexity = φ.complexity := by
  simp [DNF.neg, CNF.complexity, DNF.complexity, List.length_map]

/-- Negating a CNF preserves width. -/
theorem CNF.width_neg (φ : CNF N) : φ.neg.width = φ.width := by
  rcases φ with ⟨clauses⟩
  change (clauses.map (fun clause => clause.map Literal.neg)).foldr
      (fun term rest => max term.length rest) 0 =
    clauses.foldr (fun clause rest => max clause.length rest) 0
  induction clauses with
  | nil => rfl
  | cons clause clauses ih => simp [ih]

/-- Negating a DNF preserves width. -/
theorem DNF.width_neg (φ : DNF N) : φ.neg.width = φ.width := by
  rcases φ with ⟨terms⟩
  change (terms.map (fun term => term.map Literal.neg)).foldr
      (fun clause rest => max clause.length rest) 0 =
    terms.foldr (fun term rest => max term.length rest) 0
  induction terms with
  | nil => rfl
  | cons term terms ih => simp [ih]

end Complexity
