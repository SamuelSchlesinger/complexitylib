/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.FirstOrder.Substitution
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite connectives and quantifier blocks

Finite conjunctions and disjunctions express tag choices in an interpretation.
Quantifier blocks replace a quantifier over tuples by quantification over each
coordinate. `envBlock σ v` puts the coordinates of `v` first, followed by `σ`.
These constructions include empty blocks and empty families.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

variable {V : Vocabulary}

/-- Extend an environment by an entire tuple, placing its first coordinate at index zero. -/
def envBlock {card n : Nat} (σ : Env card n) : {k : Nat} → Env card k → Env card (n + k)
  | 0, _ => σ
  | _ + 1, v => envCons (v 0) (envBlock σ (Fin.tail v))

/-- The new variables evaluate to the corresponding tuple coordinates. -/
theorem envBlock_new {card n k : Nat} (σ : Env card n) (v : Env card k) (i : Fin k) :
    envBlock σ v ⟨i.val, by omega⟩ = v i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    induction i using Fin.cases with
    | zero => simp [envBlock, envCons]
    | succ i =>
      change envCons (v 0) (envBlock σ (Fin.tail v)) ⟨i.val + 1, _⟩ = v i.succ
      rw [envCons_succ (v 0) _ ⟨i.val, by omega⟩]
      exact ih (Fin.tail v) i

/-- Shift a term across a block of fresh variables. -/
def Term.shiftBy {n : Nat} (t : Term V n) : (k : Nat) → Term V (n + k)
  | 0 => t
  | k + 1 => (t.shiftBy k).shift

/-- Old terms retain their value when moved across a block of quantifiers. -/
theorem Term.shiftBy_eval {n k : Nat} (A : FinStruct V) (σ : Env A.card n)
    (v : Env A.card k) (t : Term V n) :
    (t.shiftBy k).eval A (envBlock σ v) = t.eval A σ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Term.shiftBy, envBlock, Term.shift_eval]
    exact ih (Fin.tail v)

/-- Existentially bind a block of the first `k` variables. -/
def Formula.existBlock {n : Nat} : (k : Nat) → Formula V (n + k) → Formula V n
  | 0, φ => φ
  | k + 1, φ => Formula.existBlock k (.exist φ)

/-- Universally bind a block of the first `k` variables. -/
def Formula.allBlock {n : Nat} : (k : Nat) → Formula V (n + k) → Formula V n
  | 0, φ => φ
  | k + 1, φ => Formula.allBlock k (.all φ)

/-- Existential block quantification is quantification over all coordinate tuples. -/
theorem Formula.existBlock_sat {n k : Nat} (A : FinStruct V) (σ : Env A.card n)
    (φ : Formula V (n + k)) :
    (φ.existBlock k).Sat A σ ↔ ∃ v : Env A.card k, φ.Sat A (envBlock σ v) := by
  induction k with
  | zero => simp [Formula.existBlock, envBlock]
  | succ k ih =>
    rw [Formula.existBlock, ih]
    change (∃ v : Env A.card k, ∃ a, φ.Sat A (envCons a (envBlock σ v))) ↔ _
    constructor
    · rintro ⟨v, a, h⟩; exact ⟨Fin.cons a v, by simpa [envBlock] using h⟩
    · rintro ⟨v, h⟩; exact ⟨Fin.tail v, v 0, h⟩

/-- Universal block quantification is quantification over all coordinate tuples. -/
theorem Formula.allBlock_sat {n k : Nat} (A : FinStruct V) (σ : Env A.card n)
    (φ : Formula V (n + k)) :
    (φ.allBlock k).Sat A σ ↔ ∀ v : Env A.card k, φ.Sat A (envBlock σ v) := by
  induction k with
  | zero => simp [Formula.allBlock, envBlock]
  | succ k ih =>
    rw [Formula.allBlock, ih]
    change (∀ v : Env A.card k, ∀ a, φ.Sat A (envCons a (envBlock σ v))) ↔ _
    constructor
    · intro h v; exact h (Fin.tail v) (v 0)
    · intro h v a; simpa [envBlock] using h (Fin.cons a v)

/-- A finite conjunction, with verum as the empty conjunction. -/
def Formula.conjList {n : Nat} (xs : List (Formula V n)) : Formula V n :=
  xs.foldr .conj .verum

/-- A finite disjunction, with falsum as the empty disjunction. -/
def Formula.disjList {n : Nat} (xs : List (Formula V n)) : Formula V n :=
  xs.foldr .disj .falsum

/-- A finite conjunction holds exactly when every member holds. -/
theorem Formula.conjList_sat {n : Nat} (A : FinStruct V) (σ : Env A.card n)
    (xs : List (Formula V n)) :
    (Formula.conjList xs).Sat A σ ↔ ∀ φ ∈ xs, φ.Sat A σ := by
  induction xs with
  | nil => simp [Formula.conjList, Formula.verum_sat]
  | cons φ xs ih => simp [Formula.conjList, Formula.Sat, ← ih]

/-- A finite disjunction holds exactly when some member holds. -/
theorem Formula.disjList_sat {n : Nat} (A : FinStruct V) (σ : Env A.card n)
    (xs : List (Formula V n)) :
    (Formula.disjList xs).Sat A σ ↔ ∃ φ ∈ xs, φ.Sat A σ := by
  induction xs with
  | nil => simp [Formula.disjList, Formula.falsum_sat]
  | cons φ xs ih => simp [Formula.disjList, Formula.Sat, ← ih]

/-- Conjunction over a finite index type. -/
def Formula.conjFin {n k : Nat} (φ : Fin k → Formula V n) : Formula V n :=
  Formula.conjList ((List.finRange k).map φ)

/-- Disjunction over a finite index type. -/
def Formula.disjFin {n k : Nat} (φ : Fin k → Formula V n) : Formula V n :=
  Formula.disjList ((List.finRange k).map φ)

/-- Finite conjunction is universal quantification over its indices. -/
theorem Formula.conjFin_sat {n k : Nat} (A : FinStruct V) (σ : Env A.card n)
    (φ : Fin k → Formula V n) :
    (Formula.conjFin φ).Sat A σ ↔ ∀ i, (φ i).Sat A σ := by
  simp [Formula.conjFin, Formula.conjList_sat]

/-- Finite disjunction is existential quantification over its indices. -/
theorem Formula.disjFin_sat {n k : Nat} (A : FinStruct V) (σ : Env A.card n)
    (φ : Fin k → Formula V n) :
    (Formula.disjFin φ).Sat A σ ↔ ∃ i, (φ i).Sat A σ := by
  simp [Formula.disjFin, Formula.disjList_sat]

end Complexity.DescriptiveComplexity
