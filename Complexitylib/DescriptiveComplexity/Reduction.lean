/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Query
public import Complexitylib.DescriptiveComplexity.FirstOrder.Substitution

/-!
# First-order reductions and projections

A **first-order reduction** between decision problems (Boolean queries over finite
structures) is a first-order *interpretation*: the target structure is defined from
the source by FO formulas, one per target relation symbol. This module gives the
dimension-1 (universe-preserving) case — each target relation is an FO-definable
relation on the same universe — the foundational special case of the general
dimension-`k` interpretation (whose target universe is a definable subset of `domᵏ`,
recorded as a roadmap L6 milestone).

First-order reductions are the reductions of descriptive complexity: weak enough to
sit inside `FO`/`AC⁰`, yet enough to define completeness for the standard classes.
Their quantifier-free restriction — **first-order projections** — is weaker still and
is the notion under which many natural problems are complete.

Each Boolean query induces a machine-model `Language` via `queryLanguage`; the
string-level FO-reduction (an FO map on encodings) is a further step on track L6.

## Main definitions and results

- `FOInterpretation` — a dimension-1 first-order interpretation `V → W`.
- `FOInterpretation.apply` — the induced structure map, with `apply_idInterp`.
- `FOReduces` — first-order reducibility between Boolean queries, with reflexivity
  and transitivity.
- `FOInterpretation.IsQuantifierFree`, `FOProjReduces` — first-order projections,
  with `FOInterpretation.IsQuantifierFree.comp`, `FOProjReduces.toFOReduces`, and
  reflexivity/transitivity.
-/


@[expose] public section

namespace Complexity

namespace DescriptiveComplexity

variable {V W : Vocabulary} {n : Nat}

/-- A **(dimension-1) first-order interpretation** from vocabulary `V` to `W`: each
    target relation symbol is defined by an FO formula over `V` with one free variable
    per argument, and each target constant symbol is a source constant. Applying it to
    a `V`-structure yields a `W`-structure on the *same* universe. -/
structure FOInterpretation (V W : Vocabulary) where
  /-- The FO formula (over `V`) defining each target relation of `W`. -/
  relFormula : (i : Fin W.numRels) → Formula V (W.relArity i)
  /-- Each target constant of `W` is interpreted as a source constant of `V`. -/
  constMap : Fin W.numConsts → Fin V.numConsts

/-- Apply an interpretation to a source structure, producing a target structure on the
    same universe: each target relation holds exactly when its defining formula does. -/
def FOInterpretation.apply (I : FOInterpretation V W) (A : FinStruct V) : FinStruct W where
  card := A.card
  hcard := A.hcard
  rel := fun i args => Formula.Sat A args (I.relFormula i)
  const := fun c => A.const (I.constMap c)

/-- The **identity interpretation**: each relation is defined by its own atom
    `R(x₀, …, x_{a-1})` and each constant maps to itself. -/
def FOInterpretation.idInterp (V : Vocabulary) : FOInterpretation V V where
  relFormula := fun i => Formula.relApp i (fun j => Term.var j)
  constMap := fun c => c

/-- The identity interpretation acts as the identity on structures. -/
theorem FOInterpretation.apply_idInterp (A : FinStruct V) :
    (FOInterpretation.idInterp V).apply A = A := by
  cases A with
  | mk card hcard rel const =>
    simp only [FOInterpretation.apply, FOInterpretation.idInterp, Formula.Sat, Term.eval]

/-- Translate a `W`-term to a `V`-term along the interpretation: a variable stays
    put, and a target constant becomes its designated source constant. -/
def FOInterpretation.translateTerm (I : FOInterpretation V W) : Term W n → Term V n
  | .var j => Term.var j
  | .const c => Term.const (I.constMap c)

/-- **Term-level transport.** Evaluating a translated term in the source structure
    agrees with evaluating the original term in the interpreted structure. This is the
    base case of the full (formula-level) transport theorem. -/
theorem FOInterpretation.translateTerm_eval (I : FOInterpretation V W) (A : FinStruct V)
    (σ : Env A.card n) (t : Term W n) :
    Term.eval A σ (I.translateTerm t) = Term.eval (I.apply A) σ t := by
  cases t with
  | var j => rfl
  | const c => rfl

/-- The interpreted structure's relation is (definitionally) satisfaction of the
    defining formula. -/
theorem FOInterpretation.apply_rel (I : FOInterpretation V W) (A : FinStruct V)
    (i : Fin W.numRels) (args : Fin (W.relArity i) → Fin A.card) :
    (I.apply A).rel i args = Formula.Sat A args (I.relFormula i) := rfl

/-- Translate a `W`-formula to a `V`-formula along the interpretation: a target
    relation atom is replaced by its defining formula with the (translated) argument
    terms substituted in; other connectives and quantifiers are traversed. -/
def FOInterpretation.translate (I : FOInterpretation V W) :
    {n : Nat} → Formula W n → Formula V n
  | _, .relApp i ts => (I.relFormula i).subst (fun k => I.translateTerm (ts k))
  | _, .eq t₁ t₂ => .eq (I.translateTerm t₁) (I.translateTerm t₂)
  | _, .neg φ => .neg (I.translate φ)
  | _, .conj φ ψ => .conj (I.translate φ) (I.translate ψ)
  | _, .disj φ ψ => .disj (I.translate φ) (I.translate ψ)
  | _, .exist φ => .exist (I.translate φ)
  | _, .all φ => .all (I.translate φ)

/-- **The transport theorem (fundamental theorem of interpretations).** Satisfaction of
    a formula in the interpreted structure `I.apply A` equals satisfaction of its
    translation in the source structure `A`. This is what makes FO-reductions compose.
    -/
theorem FOInterpretation.translate_sat (I : FOInterpretation V W) (A : FinStruct V) :
    ∀ {n : Nat} (σ : Env A.card n) (φ : Formula W n),
      Formula.Sat (I.apply A) σ φ ↔ Formula.Sat A σ (I.translate φ) := by
  intro n σ φ
  induction φ with
  | relApp i ts =>
    simp only [FOInterpretation.translate]
    rw [Formula.subst_sat]
    have henv : (fun j => Term.eval (I.apply A) σ (ts j))
        = (fun k => Term.eval A σ (I.translateTerm (ts k))) := by
      funext k; rw [I.translateTerm_eval]
    exact Iff.of_eq (congrArg (fun e => Formula.Sat A e (I.relFormula i)) henv)
  | eq t₁ t₂ =>
    simp only [FOInterpretation.translate, Formula.Sat]
    constructor
    · intro h; rw [I.translateTerm_eval, I.translateTerm_eval]; exact h
    · intro h; rw [I.translateTerm_eval, I.translateTerm_eval] at h; exact h
  | neg φ ih => exact not_congr (ih σ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ σ) (ihψ σ)
  | disj φ ψ ihφ ihψ => exact or_congr (ihφ σ) (ihψ σ)
  | exist φ ih => exact exists_congr fun a => ih (envCons a σ)
  | all φ ih => exact forall_congr' fun a => ih (envCons a σ)

/-- Compose two interpretations by translating the outer defining formulas through
    the inner interpretation (`I₂ ∘ I₁`, source `U → V → W`). -/
def FOInterpretation.comp (I₂ : FOInterpretation V W) (I₁ : FOInterpretation U V) :
    FOInterpretation U W where
  relFormula := fun i => I₁.translate (I₂.relFormula i)
  constMap := fun c => I₁.constMap (I₂.constMap c)

/-- **Composition applies as composition of structure maps**: `(I₂ ∘ I₁).apply A =
    I₂.apply (I₁.apply A)`. The relation fields agree by the transport theorem. -/
theorem FOInterpretation.apply_comp (I₂ : FOInterpretation V W) (I₁ : FOInterpretation U V)
    (A : FinStruct U) : (I₂.comp I₁).apply A = I₂.apply (I₁.apply A) := by
  have hrel : ((I₂.comp I₁).apply A).rel = (I₂.apply (I₁.apply A)).rel := by
    funext i args
    exact propext (I₁.translate_sat A args (I₂.relFormula i)).symm
  rw [show (I₂.comp I₁).apply A
      = { I₂.apply (I₁.apply A) with rel := ((I₂.comp I₁).apply A).rel } from rfl, hrel]

/-- **First-order reduction** between Boolean queries: an FO-interpretation carrying
    `Q₁`-membership to `Q₂`-membership on the interpreted structure. -/
def FOReduces (Q₁ : BooleanQuery V) (Q₂ : BooleanQuery W) : Prop :=
  ∃ I : FOInterpretation V W, ∀ A : FinStruct V, Q₁ A ↔ Q₂ (I.apply A)

/-- FO-reducibility is reflexive, via the identity interpretation. -/
theorem FOReduces.refl (Q : BooleanQuery V) : FOReduces Q Q :=
  ⟨FOInterpretation.idInterp V, fun A => by rw [FOInterpretation.apply_idInterp]⟩

/-- **First-order reductions respect complementation**: the same interpretation
    witnesses `Q₁ᶜ ≤ Q₂ᶜ`, since the carrying biconditional negates. -/
theorem FOReduces.complement {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOReduces Q₁ Q₂) : FOReduces Q₁.complement Q₂.complement := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, fun A => by simp only [BooleanQuery.complement, hI A]⟩

/-- **FO-reducibility is transitive**, via composition of interpretations (the
    transport theorem is exactly what makes the composite carry membership). Together
    with `FOReduces.refl`, FO-reducibility is a preorder on Boolean queries. -/
theorem FOReduces.trans {U : Vocabulary} {Q₁ : BooleanQuery U} {Q₂ : BooleanQuery V}
    {Q₃ : BooleanQuery W} (h₁ : FOReduces Q₁ Q₂) (h₂ : FOReduces Q₂ Q₃) :
    FOReduces Q₁ Q₃ := by
  obtain ⟨I₁, hI₁⟩ := h₁
  obtain ⟨I₂, hI₂⟩ := h₂
  refine ⟨I₂.comp I₁, fun A => ?_⟩
  rw [hI₁ A, hI₂ (I₁.apply A), FOInterpretation.apply_comp]

/-- An interpretation is **quantifier-free** when every defining formula has quantifier
    rank `0` — the coarse form of a first-order projection. -/
def FOInterpretation.IsQuantifierFree (I : FOInterpretation V W) : Prop :=
  ∀ i, (I.relFormula i).quantifierRank = 0

/-- Translating through a quantifier-free interpretation preserves quantifier rank.
    Relation atoms are replaced by quantifier-free defining formulas, while all
    logical connectives and quantifiers retain their original structure. -/
theorem FOInterpretation.IsQuantifierFree.quantifierRank_translate
    {I : FOInterpretation V W} (hI : I.IsQuantifierFree) {n : Nat}
    (φ : Formula W n) :
    (I.translate φ).quantifierRank = φ.quantifierRank := by
  induction φ with
  | relApp i ts =>
    simpa [FOInterpretation.translate, Formula.quantifierRank_subst,
      Formula.quantifierRank] using hI i
  | eq t₁ t₂ => rfl
  | neg φ ih =>
    simpa [FOInterpretation.translate, Formula.quantifierRank] using ih
  | conj φ ψ ihφ ihψ =>
    simp only [FOInterpretation.translate, Formula.quantifierRank, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
    simp only [FOInterpretation.translate, Formula.quantifierRank, ihφ, ihψ]
  | exist φ ih =>
    simp only [FOInterpretation.translate, Formula.quantifierRank, ih]
  | all φ ih =>
    simp only [FOInterpretation.translate, Formula.quantifierRank, ih]

/-- The identity interpretation is quantifier-free (each relation is a bare atom). -/
theorem FOInterpretation.idInterp_isQuantifierFree :
    (FOInterpretation.idInterp V).IsQuantifierFree :=
  fun _ => rfl

/-- Composing quantifier-free interpretations remains quantifier-free. -/
theorem FOInterpretation.IsQuantifierFree.comp {U : Vocabulary}
    {I₂ : FOInterpretation V W} {I₁ : FOInterpretation U V}
    (hI₂ : I₂.IsQuantifierFree) (hI₁ : I₁.IsQuantifierFree) :
    (I₂.comp I₁).IsQuantifierFree := by
  intro i
  rw [show (I₂.comp I₁).relFormula i = I₁.translate (I₂.relFormula i) from rfl,
    hI₁.quantifierRank_translate, hI₂ i]

/-- A **first-order projection** reduction: an FO-reduction witnessed by a
    quantifier-free interpretation. -/
def FOProjReduces (Q₁ : BooleanQuery V) (Q₂ : BooleanQuery W) : Prop :=
  ∃ I : FOInterpretation V W, I.IsQuantifierFree ∧ ∀ A : FinStruct V, Q₁ A ↔ Q₂ (I.apply A)

/-- Every first-order projection is in particular a first-order reduction. -/
theorem FOProjReduces.toFOReduces {Q₁ : BooleanQuery V} {Q₂ : BooleanQuery W}
    (h : FOProjReduces Q₁ Q₂) : FOReduces Q₁ Q₂ :=
  let ⟨I, _, hI⟩ := h; ⟨I, hI⟩

/-- FO-projection reducibility is reflexive, via the (quantifier-free) identity. -/
theorem FOProjReduces.refl (Q : BooleanQuery V) : FOProjReduces Q Q :=
  ⟨FOInterpretation.idInterp V, FOInterpretation.idInterp_isQuantifierFree,
    fun A => by rw [FOInterpretation.apply_idInterp]⟩

/-- **FO-projection reducibility is transitive.** Composition preserves both the
    query-membership equivalence and quantifier-freeness of the interpretation. -/
theorem FOProjReduces.trans {U : Vocabulary} {Q₁ : BooleanQuery U}
    {Q₂ : BooleanQuery V} {Q₃ : BooleanQuery W} (h₁ : FOProjReduces Q₁ Q₂)
    (h₂ : FOProjReduces Q₂ Q₃) : FOProjReduces Q₁ Q₃ := by
  obtain ⟨I₁, hqf₁, hI₁⟩ := h₁
  obtain ⟨I₂, hqf₂, hI₂⟩ := h₂
  refine ⟨I₂.comp I₁, hqf₂.comp hqf₁, fun A => ?_⟩
  rw [hI₁ A, hI₂ (I₁.apply A), FOInterpretation.apply_comp]

end DescriptiveComplexity

end Complexity
