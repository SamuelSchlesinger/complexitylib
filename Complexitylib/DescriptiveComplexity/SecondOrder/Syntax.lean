/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.DescriptiveComplexity.FirstOrder.Syntax

/-!
# Second-order logic: syntax

Second-order logic over a vocabulary `V` extends first-order logic with **relation
variables** — quantifiable variables standing for relations on the universe — and
**second-order quantifiers**. A formula is indexed by a de Bruijn context `rctx :
List ℕ` giving the arities of the relation variables in scope (innermost first) and
by the number `n` of first-order variables in scope, so `soExist k` pushes a fresh
arity-`k` relation variable onto `rctx`.

This is step 1 of the Fagin decomposition (roadmap L6): the `∃SO` fragment of this
syntax is the one Fagin's theorem characterizes as `NP`.

## Main definitions

- `DescriptiveComplexity.SOFormula`, `SOSentence` — second-order formulas and
  sentences.
- `SOFormula.ofFormula` — the embedding of first-order logic into second-order
  logic.
- `SOFormula.size` — the syntactic size.
-/

@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

/-- Second-order formulas over vocabulary `V`, with a de Bruijn context `rctx` of
    relation-variable arities and `n` first-order variables. Extends first-order
    logic with relation-variable application (`soRelApp`) and second-order
    quantifiers (`soExist`/`soAll`), which push a fresh arity onto `rctx`. -/
inductive SOFormula (V : Vocabulary) : List Nat → Nat → Type where
  /-- Apply a vocabulary relation symbol to terms. -/
  | relApp {rctx n} : (i : Fin V.numRels) → (Fin (V.relArity i) → Term V n) → SOFormula V rctx n
  /-- Apply a relation *variable* (de Bruijn index `r`, arity `rctx.get r`) to terms. -/
  | soRelApp {rctx n} : (r : Fin rctx.length) → (Fin (rctx.get r) → Term V n) → SOFormula V rctx n
  /-- Equality of terms. -/
  | eq {rctx n} : Term V n → Term V n → SOFormula V rctx n
  /-- Negation. -/
  | neg {rctx n} : SOFormula V rctx n → SOFormula V rctx n
  /-- Conjunction. -/
  | conj {rctx n} : SOFormula V rctx n → SOFormula V rctx n → SOFormula V rctx n
  /-- Disjunction. -/
  | disj {rctx n} : SOFormula V rctx n → SOFormula V rctx n → SOFormula V rctx n
  /-- First-order existential quantifier. -/
  | exist {rctx n} : SOFormula V rctx (n + 1) → SOFormula V rctx n
  /-- First-order universal quantifier. -/
  | all {rctx n} : SOFormula V rctx (n + 1) → SOFormula V rctx n
  /-- Second-order existential quantifier over a fresh arity-`k` relation. -/
  | soExist {rctx n} : (k : Nat) → SOFormula V (k :: rctx) n → SOFormula V rctx n
  /-- Second-order universal quantifier over a fresh arity-`k` relation. -/
  | soAll {rctx n} : (k : Nat) → SOFormula V (k :: rctx) n → SOFormula V rctx n

/-- A second-order sentence: no free relation or element variables. -/
abbrev SOSentence (V : Vocabulary) := SOFormula V [] 0

namespace SOFormula

/-- The first-order fragment embeds into second-order logic (over any relation
    context): every FO formula is an SO formula that never mentions relation
    variables. -/
def ofFormula {V : Vocabulary} {n : Nat} : Formula V n → (rctx : List Nat) → SOFormula V rctx n
  | .relApp i args, _ => .relApp i args
  | .eq a b, _ => .eq a b
  | .neg φ, rctx => .neg (ofFormula φ rctx)
  | .conj φ ψ, rctx => .conj (ofFormula φ rctx) (ofFormula ψ rctx)
  | .disj φ ψ, rctx => .disj (ofFormula φ rctx) (ofFormula ψ rctx)
  | .exist φ, rctx => .exist (ofFormula φ rctx)
  | .all φ, rctx => .all (ofFormula φ rctx)

/-- Syntactic size (number of nodes) of a second-order formula. -/
def size {V : Vocabulary} {rctx : List Nat} {n : Nat} : SOFormula V rctx n → Nat
  | .relApp _ _ => 1
  | .soRelApp _ _ => 1
  | .eq _ _ => 1
  | .neg φ => φ.size + 1
  | .conj φ ψ => φ.size + ψ.size + 1
  | .disj φ ψ => φ.size + ψ.size + 1
  | .exist φ => φ.size + 1
  | .all φ => φ.size + 1
  | .soExist _ φ => φ.size + 1
  | .soAll _ φ => φ.size + 1

/-- A formula has no second-order quantifiers — an FO matrix over the relation
    variables in scope. -/
def IsFOMatrix {V : Vocabulary} : {rctx : List Nat} → {n : Nat} → SOFormula V rctx n → Prop
  | _, _, .relApp _ _ => True
  | _, _, .soRelApp _ _ => True
  | _, _, .eq _ _ => True
  | _, _, .neg φ => IsFOMatrix φ
  | _, _, .conj φ ψ => IsFOMatrix φ ∧ IsFOMatrix ψ
  | _, _, .disj φ ψ => IsFOMatrix φ ∧ IsFOMatrix ψ
  | _, _, .exist φ => IsFOMatrix φ
  | _, _, .all φ => IsFOMatrix φ
  | _, _, .soExist _ _ => False
  | _, _, .soAll _ _ => False

/-- A formula is in **existential second-order** (`∃SO`) form: a block of
    second-order existential quantifiers over an FO matrix. This is the exact
    fragment Fagin's theorem characterizes as `NP`. -/
def IsExistSO {V : Vocabulary} : {rctx : List Nat} → {n : Nat} → SOFormula V rctx n → Prop
  | _, _, .soExist _ ψ => IsExistSO ψ
  | _, _, φ => φ.IsFOMatrix

/-- The first-order embedding of any formula is an FO matrix. -/
theorem ofFormula_isFOMatrix {V : Vocabulary} :
    ∀ {n : Nat} (φ : Formula V n) (rctx : List Nat), (SOFormula.ofFormula φ rctx).IsFOMatrix := by
  intro n φ
  induction φ with
  | relApp i args => intro rctx; exact True.intro
  | eq a b => intro rctx; exact True.intro
  | neg φ ih => intro rctx; exact ih rctx
  | conj φ ψ ihφ ihψ => intro rctx; exact ⟨ihφ rctx, ihψ rctx⟩
  | disj φ ψ ihφ ihψ => intro rctx; exact ⟨ihφ rctx, ihψ rctx⟩
  | exist φ ih => intro rctx; exact ih rctx
  | all φ ih => intro rctx; exact ih rctx

/-- The first-order fragment sits inside `∃SO`: an embedded FO formula is a
    (quantifier-free-in-second-order) `∃SO` formula. -/
theorem ofFormula_isExistSO {V : Vocabulary} {n : Nat} (φ : Formula V n) (rctx : List Nat) :
    (SOFormula.ofFormula φ rctx).IsExistSO := by
  cases φ <;> exact ofFormula_isFOMatrix _ _

end SOFormula

end DescriptiveComplexity

end Complexity
