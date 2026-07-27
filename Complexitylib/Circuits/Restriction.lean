/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Basic
public import Complexitylib.Circuits.Formula

/-!
# Restrictions

A **restriction** is a partial assignment that fixes some variables to constants
and leaves the rest free — the basic operation behind random-restriction and
switching-lemma arguments (roadmap track L4). This module defines restrictions,
their composition, and proves that evaluating a *restricted* Boolean formula
agrees with evaluating the original under the restriction applied to the
assignment (evaluation commutes with restriction).

## Main definitions and results

- `Restriction`, `Restriction.applyTo`, `Restriction.comp`
- `Restriction.On` — a finite-arity restriction suitable for finite counting
- `Restriction.applyTo_comp` — applying a composite restriction is applying the
  two in sequence
- `BoolFormula.restrict`, `BoolFormula.eval_restrict`,
  `BoolFormula.restrict_comp` — evaluation and composition laws
-/

@[expose] public section

namespace Complexity

/-- A restriction: a partial assignment fixing some variables (`some b`) and
    leaving the rest free (`none`). -/
abbrev Restriction := ℕ → Option Bool

namespace Restriction

/-- The restriction leaving every variable free. -/
def empty : Restriction := fun _ => none

/-- Apply a restriction on top of a total assignment: fixed variables take the
    restriction's value, free variables fall back to the assignment. -/
def applyTo (ρ : Restriction) (α : ℕ → Bool) : ℕ → Bool := fun i => (ρ i).getD (α i)

/-- Compose two restrictions: the first takes precedence, the second fills in the
    variables the first leaves free. -/
def comp (ρ₁ ρ₂ : Restriction) : Restriction := fun i => (ρ₁ i).or (ρ₂ i)

@[simp] theorem empty_apply (i : Nat) : empty i = none := rfl

@[simp] theorem applyTo_empty (α : Nat → Bool) : applyTo empty α = α := by
  funext i
  rfl

@[simp] theorem empty_comp (ρ : Restriction) : comp empty ρ = ρ := by
  funext i
  rfl

@[simp] theorem comp_empty (ρ : Restriction) : comp ρ empty = ρ := by
  funext i
  simp [comp, empty]

/-- Restriction composition is associative, with the leftmost fixed value
taking precedence. -/
theorem comp_assoc (ρ₁ ρ₂ ρ₃ : Restriction) :
    comp (comp ρ₁ ρ₂) ρ₃ = comp ρ₁ (comp ρ₂ ρ₃) := by
  funext i
  simp only [comp]
  cases ρ₁ i <;> rfl

/-- Applying a composite restriction is the same as applying the two restrictions
    in sequence. -/
theorem applyTo_comp (ρ₁ ρ₂ : Restriction) (α : ℕ → Bool) :
    applyTo (comp ρ₁ ρ₂) α = applyTo ρ₁ (applyTo ρ₂ α) := by
  funext i
  simp only [applyTo, comp]
  cases ρ₁ i <;> rfl

/-! ## Finite-arity restrictions -/

/-- A restriction on exactly `N` variables.

Unlike the ambient `Restriction = Nat → Option Bool`, this is a finite type and
can therefore be used directly as a finite probability space. -/
abbrev On (N : Nat) := Fin N → Option Bool

namespace On

/-- The finite restriction leaving every coordinate free. -/
def empty : Restriction.On N := fun _ => none

/-- Fix exactly one coordinate and leave every other coordinate free. -/
def single (index : Fin N) (value : Bool) : Restriction.On N :=
  fun other => if other = index then some value else none

/-- Left-biased composition of finite restrictions. -/
def comp (ρ₁ ρ₂ : Restriction.On N) : Restriction.On N :=
  fun index => (ρ₁ index).or (ρ₂ index)

/-- Apply a finite-arity restriction to a matching bit string. -/
def applyTo (ρ : Restriction.On N) (x : BitString N) : BitString N :=
  fun i => (ρ i).getD (x i)

/-- The finite set of coordinates left free by a finite-arity restriction. -/
def freeVariables (ρ : Restriction.On N) : Finset (Fin N) :=
  Finset.univ.filter fun index => ρ index = none

/-- Extend a finite-arity restriction by leaving every index outside its
declared arity free. -/
def toRestriction (ρ : Restriction.On N) : Restriction := fun i =>
  if h : i < N then ρ ⟨i, h⟩ else none

@[simp] theorem toRestriction_apply
    (ρ : Restriction.On N) (i : Fin N) :
    ρ.toRestriction i.val = ρ i := by
  simp only [toRestriction, i.isLt, dite_true]

@[simp] theorem empty_apply (index : Fin N) :
    empty index = none := rfl

@[simp] theorem single_apply_self (index : Fin N) (value : Bool) :
    single index value index = some value := by
  simp [single]

theorem single_apply_of_ne {index other : Fin N} (h : other ≠ index)
    (value : Bool) :
    single index value other = none := by
  simp [single, h]

@[simp] theorem applyTo_empty (x : BitString N) :
    applyTo empty x = x := by
  funext index
  rfl

@[simp] theorem mem_freeVariables (ρ : Restriction.On N)
    (index : Fin N) :
    index ∈ ρ.freeVariables ↔ ρ index = none := by
  simp [freeVariables]

/-- Applying a singleton restriction is function update at its fixed index. -/
theorem applyTo_single (index : Fin N) (value : Bool)
    (x : BitString N) :
    applyTo (single index value) x =
      Function.update x index value := by
  funext other
  by_cases h : other = index
  · subst other
    simp [applyTo, single]
  · simp [applyTo, single, Function.update, h]

@[simp] theorem empty_comp (ρ : Restriction.On N) :
    comp empty ρ = ρ := by
  funext index
  rfl

@[simp] theorem comp_empty (ρ : Restriction.On N) :
    comp ρ empty = ρ := by
  funext index
  simp [comp, empty]

theorem comp_assoc (ρ₁ ρ₂ ρ₃ : Restriction.On N) :
    comp (comp ρ₁ ρ₂) ρ₃ = comp ρ₁ (comp ρ₂ ρ₃) := by
  funext index
  simp only [comp]
  cases ρ₁ index <;> rfl

/-- Disjoint finite restrictions commute despite composition being
left-biased in general. -/
theorem comp_comm_of_disjoint
    (first second : Restriction.On N)
    (hdisjoint :
      ∀ index, first index = none ∨ second index = none) :
    comp first second = comp second first := by
  funext index
  specialize hdisjoint index
  cases hfirst : first index <;>
    cases hsecond : second index <;>
      simp_all [comp]

/-- Finite restriction application respects left-biased composition. -/
theorem applyTo_comp (ρ₁ ρ₂ : Restriction.On N)
    (x : BitString N) :
    applyTo (comp ρ₁ ρ₂) x =
      applyTo ρ₁ (applyTo ρ₂ x) := by
  funext index
  simp only [applyTo, comp]
  cases ρ₁ index <;> rfl

end On

end Restriction

namespace BoolFormula

/-- Apply a restriction to a formula, replacing each fixed variable by the
    corresponding constant and leaving free variables in place. -/
def restrict (ρ : Restriction) : BoolFormula → BoolFormula
  | var i => match ρ i with
    | some b => if b then tru else fls
    | none => var i
  | tru => tru
  | fls => fls
  | neg φ => neg (restrict ρ φ)
  | conj φ ψ => conj (restrict ρ φ) (restrict ρ ψ)
  | disj φ ψ => disj (restrict ρ φ) (restrict ρ ψ)

/-- The empty restriction is the identity on formulas. -/
@[simp] theorem restrict_empty (φ : BoolFormula) :
    restrict Restriction.empty φ = φ := by
  induction φ with
  | var i => rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp [restrict, ih]
  | conj φ ψ ihφ ihψ => simp [restrict, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [restrict, ihφ, ihψ]

/-- **Evaluation commutes with restriction.** Evaluating a restricted formula at
    `α` equals evaluating the original formula at the restriction applied to
    `α`. -/
theorem eval_restrict (ρ : Restriction) (α : ℕ → Bool) (φ : BoolFormula) :
    eval α (restrict ρ φ) = eval (Restriction.applyTo ρ α) φ := by
  induction φ with
  | var i =>
    cases h : ρ i with
    | none => simp [restrict, eval, Restriction.applyTo, h]
    | some b => cases b <;> simp [restrict, eval, Restriction.applyTo, h]
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, eval, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, eval, ihφ, ihψ]

/-- Applying `ρ₁` and then `ρ₂` to a formula is syntactically the same as
applying their left-biased composition. -/
theorem restrict_comp (ρ₁ ρ₂ : Restriction) (φ : BoolFormula) :
    restrict ρ₂ (restrict ρ₁ φ) =
      restrict (Restriction.comp ρ₁ ρ₂) φ := by
  induction φ with
  | var i =>
      cases h₁ : ρ₁ i with
      | none =>
          cases h₂ : ρ₂ i with
          | none =>
              simp [restrict, Restriction.comp, h₁, h₂]
          | some b =>
              cases b <;> simp [restrict, Restriction.comp, h₁, h₂]
      | some b =>
          cases b <;> simp [restrict, Restriction.comp, h₁]
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, ihφ, ihψ]

/-- Restriction preserves the tree size: fixing a variable replaces a leaf by a
    constant leaf, and connectives are untouched. So `(restrict ρ φ).size = φ.size`
    — restriction never grows a formula (a fact width/size arguments rely on). -/
theorem restrict_size (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).size = φ.size := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, size, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, size, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, size, ihφ, ihψ]

/-- Restriction also preserves the leaf count: `(restrict ρ φ).leaves = φ.leaves`. -/
theorem restrict_leaves (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).leaves = φ.leaves := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, leaves, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, leaves, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, leaves, ihφ, ihψ]

/-- Restriction preserves the formula depth exactly: it only relabels leaves,
    leaving the connective tree — and hence every root-to-leaf path length —
    untouched. So `(restrict ρ φ).depth = φ.depth`. -/
theorem restrict_depth (ρ : Restriction) (φ : BoolFormula) :
    (restrict ρ φ).depth = φ.depth := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => rfl
    | some b => cases b <;> rfl
  | tru => rfl
  | fls => rfl
  | neg φ ih => simp only [restrict, depth, ih]
  | conj φ ψ ihφ ihψ => simp only [restrict, depth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp only [restrict, depth, ihφ, ihψ]

/-- Restriction only ever removes variables: `vars (restrict ρ φ) ⊆ vars φ`. Fixing
    a variable turns its leaf into a constant (dropping it); free variables are
    untouched. This is the variable-tracking fact switching-lemma arguments use to
    bound the surviving support after a random restriction. -/
theorem vars_restrict_subset (ρ : Restriction) (φ : BoolFormula) :
    vars (restrict ρ φ) ⊆ vars φ := by
  induction φ with
  | var i =>
    simp only [restrict]
    cases ρ i with
    | none => simp [vars]
    | some b => cases b <;> simp [vars]
  | tru => simp [restrict, vars]
  | fls => simp [restrict, vars]
  | neg φ ih => simpa [restrict, vars] using ih
  | conj φ ψ ihφ ihψ =>
    simp only [restrict, vars]
    exact Finset.union_subset_union ihφ ihψ
  | disj φ ψ ihφ ihψ =>
    simp only [restrict, vars]
    exact Finset.union_subset_union ihφ ihψ

/-- Restriction removes exactly the fixed variables from a formula's support. -/
theorem vars_restrict_eq_filter (ρ : Restriction) (φ : BoolFormula) :
    vars (restrict ρ φ) =
      (vars φ).filter fun i => ρ i = none := by
  induction φ with
  | var i =>
      cases h : ρ i with
      | none =>
          simp only [restrict, h, vars]
          ext j
          by_cases hji : j = i
          · subst j
            simp [h]
          · simp [hji]
      | some b =>
          cases b
          · simp only [restrict, h, Bool.false_eq_true, ↓reduceIte, vars]
            ext j
            by_cases hji : j = i
            · subst j
              simp [h]
            · simp [hji]
          · simp only [restrict, h, ↓reduceIte, vars]
            ext j
            by_cases hji : j = i
            · subst j
              simp [h]
            · simp [hji]
  | tru => simp [restrict, vars]
  | fls => simp [restrict, vars]
  | neg φ ih => simpa [restrict, vars] using ih
  | conj φ ψ ihφ ihψ =>
      simp only [restrict, vars, ihφ, ihψ, Finset.filter_union]
  | disj φ ψ ihφ ihψ =>
      simp only [restrict, vars, ihφ, ihψ, Finset.filter_union]

end BoolFormula

end Complexity
