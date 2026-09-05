/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Finset.SDiff
public import Std.Tactic.BVDecide.Normalize.Bool

/-!
# Quantified Boolean formulas

Syntax and semantics of **quantified Boolean formulas (QBF)** — the canonical
PSPACE object, and the target of the TQBF PSPACE-completeness theorem and the
`IP = PSPACE` development (roadmap tracks N3, M4, L1).

A `QBF` is a Boolean formula over variables `x_i` (`i : ℕ`) closed under `¬`, `∧`,
`∨`, and the quantifiers `∃ x_i` and `∀ x_i`. Semantics are given by
`QBF.eval` relative to an assignment `α : ℕ → Bool`; a quantifier over `x_i`
ranges over the two Boolean values substituted for `x_i` via `Function.update`.

## Main definitions and results

- `QBF` — the formula syntax
- `QBF.eval` — evaluation under an assignment
- `QBF.eval_ex_iff`, `QBF.eval_all_iff` — the defining substitution semantics of
  the quantifiers, phrased as existence/universality over the substituted value
-/


@[expose] public section

namespace Complexity

/-- Quantified Boolean formulas over variables indexed by `ℕ`. -/
inductive QBF where
  /-- The variable `x_i`. -/
  | var (i : ℕ)
  /-- The constant `⊤`. -/
  | tru
  /-- The constant `⊥`. -/
  | fls
  /-- Negation `¬ φ`. -/
  | neg (φ : QBF)
  /-- Conjunction `φ ∧ ψ`. -/
  | conj (φ ψ : QBF)
  /-- Disjunction `φ ∨ ψ`. -/
  | disj (φ ψ : QBF)
  /-- Existential quantifier `∃ x_i, φ`. -/
  | ex (i : ℕ) (φ : QBF)
  /-- Universal quantifier `∀ x_i, φ`. -/
  | all (i : ℕ) (φ : QBF)
  deriving Repr, DecidableEq

namespace QBF

/-- Evaluate a QBF under an assignment `α : ℕ → Bool`. A quantifier over `x_i`
    substitutes both Boolean values for `x_i` (via `Function.update`) and combines
    the results disjunctively (`ex`) or conjunctively (`all`). -/
def eval (α : ℕ → Bool) : QBF → Bool
  | .var i => α i
  | .tru => true
  | .fls => false
  | .neg φ => !(eval α φ)
  | .conj φ ψ => eval α φ && eval α ψ
  | .disj φ ψ => eval α φ || eval α ψ
  | .ex i φ => eval (Function.update α i false) φ || eval (Function.update α i true) φ
  | .all i φ => eval (Function.update α i false) φ && eval (Function.update α i true) φ

@[simp] theorem eval_var (α : ℕ → Bool) (i : ℕ) : eval α (var i) = α i := rfl
@[simp] theorem eval_tru (α : ℕ → Bool) : eval α tru = true := rfl
@[simp] theorem eval_fls (α : ℕ → Bool) : eval α fls = false := rfl
@[simp] theorem eval_neg (α : ℕ → Bool) (φ : QBF) : eval α (neg φ) = !(eval α φ) := rfl
@[simp] theorem eval_conj (α : ℕ → Bool) (φ ψ : QBF) :
    eval α (conj φ ψ) = (eval α φ && eval α ψ) := rfl
@[simp] theorem eval_disj (α : ℕ → Bool) (φ ψ : QBF) :
    eval α (disj φ ψ) = (eval α φ || eval α ψ) := rfl

/-- **Existential substitution semantics.** `∃ x_i, φ` is true under `α` iff `φ`
    is true for *some* Boolean value substituted for `x_i`. -/
theorem eval_ex_iff (α : ℕ → Bool) (i : ℕ) (φ : QBF) :
    eval α (ex i φ) = true ↔ ∃ b, eval (Function.update α i b) φ = true := by
  simp only [eval, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inl hb
    · exact Or.inr hb

/-- **Universal substitution semantics.** `∀ x_i, φ` is true under `α` iff `φ` is
    true for *every* Boolean value substituted for `x_i`. -/
theorem eval_all_iff (α : ℕ → Bool) (i : ℕ) (φ : QBF) :
    eval α (all i φ) = true ↔ ∀ b, eval (Function.update α i b) φ = true := by
  simp only [eval, Bool.and_eq_true]
  constructor
  · rintro ⟨h₀, h₁⟩ b
    cases b
    · exact h₀
    · exact h₁
  · intro h
    exact ⟨h false, h true⟩

/-- The quantifier nesting depth of a QBF: the largest number of quantifiers on
    a root-to-leaf syntax path. This bounds, but does not count, quantifier
    alternations; consecutive quantifiers of the same kind each increase
    `quantDepth`. -/
def quantDepth : QBF → ℕ
  | .var _ => 0
  | .tru => 0
  | .fls => 0
  | .neg φ => quantDepth φ
  | .conj φ ψ => max (quantDepth φ) (quantDepth ψ)
  | .disj φ ψ => max (quantDepth φ) (quantDepth ψ)
  | .ex _ φ => quantDepth φ + 1
  | .all _ φ => quantDepth φ + 1

/-- A QBF is **quantifier-free** when it has no quantifiers (depth `0`). -/
def QuantifierFree (φ : QBF) : Prop := quantDepth φ = 0

/-- A conjunction is quantifier-free iff both conjuncts are. -/
theorem quantifierFree_conj {φ ψ : QBF} :
    QuantifierFree (conj φ ψ) ↔ QuantifierFree φ ∧ QuantifierFree ψ := by
  simp only [QuantifierFree, quantDepth, Nat.max_eq_zero_iff]

/-- The **free variables** of a QBF: variables not captured by an enclosing
    quantifier. A quantifier `∃ x_i` / `∀ x_i` removes `i` from the free set. -/
def freeVars : QBF → Finset ℕ
  | var i => {i}
  | tru => ∅
  | fls => ∅
  | neg φ => freeVars φ
  | conj φ ψ => freeVars φ ∪ freeVars ψ
  | disj φ ψ => freeVars φ ∪ freeVars ψ
  | ex i φ => freeVars φ \ {i}
  | all i φ => freeVars φ \ {i}

/-- **Semantic locality of QBF.** Evaluation depends only on the free variables:
    if two assignments agree on `freeVars φ`, they give `φ` the same value. In
    particular a closed formula (empty `freeVars`) has an assignment-independent
    truth value. The quantifier cases use that updating the bound variable makes
    the two assignments agree on the quantified subformula. -/
theorem eval_eq_of_agree : ∀ (φ : QBF) (α β : ℕ → Bool),
    (∀ i ∈ freeVars φ, α i = β i) → eval α φ = eval β φ := by
  intro φ
  induction φ with
  | var i => intro α β h; exact h i (Finset.mem_singleton_self i)
  | tru => intro _ _ _; rfl
  | fls => intro _ _ _; rfl
  | neg φ ih => intro α β h; simp only [eval]; rw [ih α β h]
  | conj φ ψ ihφ ihψ =>
    intro α β h
    simp only [eval]
    rw [ihφ α β (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ α β (fun i hi => h i (Finset.mem_union_right _ hi))]
  | disj φ ψ ihφ ihψ =>
    intro α β h
    simp only [eval]
    rw [ihφ α β (fun i hi => h i (Finset.mem_union_left _ hi)),
      ihψ α β (fun i hi => h i (Finset.mem_union_right _ hi))]
  | ex i φ ih =>
    intro α β h
    have hagree : ∀ b : Bool, ∀ j ∈ freeVars φ,
        Function.update α i b j = Function.update β i b j := by
      intro b j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact h j (Finset.mem_sdiff.mpr ⟨hj, by simpa using hji⟩)
    simp only [eval]
    rw [ih _ _ (hagree false), ih _ _ (hagree true)]
  | all i φ ih =>
    intro α β h
    have hagree : ∀ b : Bool, ∀ j ∈ freeVars φ,
        Function.update α i b j = Function.update β i b j := by
      intro b j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]
        exact h j (Finset.mem_sdiff.mpr ⟨hj, by simpa using hji⟩)
    simp only [eval]
    rw [ih _ _ (hagree false), ih _ _ (hagree true)]

/-- Updating a non-free variable does not change a formula's value. -/
theorem eval_update_not_mem (α : ℕ → Bool) (i : ℕ) (b : Bool) (φ : QBF)
    (hi : i ∉ freeVars φ) : eval (Function.update α i b) φ = eval α φ := by
  apply eval_eq_of_agree
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp only [Function.update_apply, ite_eq_right hji]

/-- **Vacuous existential quantification.** Quantifying `∃` over a variable that
    does not occur free is a no-op: `eval α (∃ x_i, φ) = eval α φ`. -/
theorem eval_ex_not_mem (α : ℕ → Bool) (i : ℕ) (φ : QBF) (hi : i ∉ freeVars φ) :
    eval α (ex i φ) = eval α φ := by
  have h : eval α (ex i φ)
      = (eval (Function.update α i false) φ || eval (Function.update α i true) φ) := rfl
  rw [h, eval_update_not_mem α i false φ hi, eval_update_not_mem α i true φ hi, Bool.or_self]

/-- **Vacuous universal quantification.** Quantifying `∀` over a variable that does
    not occur free is a no-op: `eval α (∀ x_i, φ) = eval α φ`. -/
theorem eval_all_not_mem (α : ℕ → Bool) (i : ℕ) (φ : QBF) (hi : i ∉ freeVars φ) :
    eval α (all i φ) = eval α φ := by
  have h : eval α (all i φ)
      = (eval (Function.update α i false) φ && eval (Function.update α i true) φ) := rfl
  rw [h, eval_update_not_mem α i false φ hi, eval_update_not_mem α i true φ hi, Bool.and_self]

/-- A QBF is **closed** when it has no free variables. -/
def Closed (φ : QBF) : Prop := freeVars φ = ∅

/-- A closed QBF evaluates to the same value under any assignment: the truth
    value of a fully-quantified formula is well defined. -/
theorem eval_closed_eq {φ : QBF} (hφ : Closed φ) (α β : ℕ → Bool) :
    eval α φ = eval β φ := by
  apply eval_eq_of_agree
  intro i hi
  have h0 : freeVars φ = ∅ := hφ
  rw [h0] at hi
  simp at hi

/-- A closed QBF is **true** when it evaluates to `true`. By `eval_closed_eq`
    the choice of assignment is immaterial; this uses the all-`false` one. The
    set of true closed QBFs is the canonical PSPACE-complete problem TQBF. -/
def IsTrue (φ : QBF) : Prop := eval (fun _ => false) φ = true

instance (φ : QBF) : Decidable (Closed φ) := by unfold Closed; infer_instance

instance (φ : QBF) : Decidable (IsTrue φ) := by unfold IsTrue; infer_instance

/-- `∀ x₀, x₀ ∨ ¬x₀` is a true closed QBF — an executable check of the
    semantics (law of excluded middle in the Boolean domain). -/
example : IsTrue (all 0 (disj (var 0) (neg (var 0)))) := by decide

/-- Universal implies existential: over the (nonempty) Boolean domain, if
    `∀ x_i, φ` is true then `∃ x_i, φ` is true. -/
theorem isTrue_ex_of_isTrue_all {i : ℕ} {φ : QBF} (h : IsTrue (all i φ)) :
    IsTrue (ex i φ) := by
  simp only [IsTrue, eval, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
  exact Or.inl h.1

/-- Truth of a negation: `¬φ` is true iff `φ` is not (the TQBF membership rule for
    negation). -/
theorem isTrue_neg_iff (φ : QBF) : IsTrue (neg φ) ↔ ¬ IsTrue φ := by
  simp only [IsTrue, eval]
  cases eval (fun _ => false) φ <;> simp

/-- Truth of a conjunction distributes: `φ ∧ ψ` is true iff both are. -/
theorem isTrue_conj_iff (φ ψ : QBF) : IsTrue (conj φ ψ) ↔ IsTrue φ ∧ IsTrue ψ := by
  simp only [IsTrue, eval, Bool.and_eq_true]

/-- Truth of a disjunction distributes: `φ ∨ ψ` is true iff at least one is. -/
theorem isTrue_disj_iff (φ ψ : QBF) : IsTrue (disj φ ψ) ↔ IsTrue φ ∨ IsTrue ψ := by
  simp only [IsTrue, eval, Bool.or_eq_true]

/-- **Quantifier De Morgan** (`¬∃ = ∀¬`): `¬(∃ x_i, φ)` is equivalent to
    `∀ x_i, ¬φ`. -/
theorem eval_neg_ex (α : ℕ → Bool) (i : ℕ) (φ : QBF) :
    eval α (neg (ex i φ)) = eval α (all i (neg φ)) := by
  simp only [eval, Bool.not_or]

/-- **Quantifier De Morgan** (`¬∀ = ∃¬`): `¬(∀ x_i, φ)` is equivalent to
    `∃ x_i, ¬φ`. -/
theorem eval_neg_all (α : ℕ → Bool) (i : ℕ) (φ : QBF) :
    eval α (neg (all i φ)) = eval α (ex i (neg φ)) := by
  simp only [eval, Bool.not_and]

end QBF

end Complexity
