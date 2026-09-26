/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Interpretation.Defs
public import Complexitylib.DescriptiveComplexity.FirstOrder.Blocks

/-!
# Formula pullback for tagged tuple interpretations

The dual of an interpretation replaces variables by tuples, relation atoms by
their defining formulas, equality by equality of tags and coordinates, and each
quantifier by a finite tag choice followed by a block of coordinate quantifiers.
This is Immerman's Definition 3.3 and Proposition 3.5, using the tagged full
universe of Senellart--Gnatenko (2026), Sections 3.2--3.3. Constants are tuples
of source constants, the special case in the footnote to Definition 3.3.

`pullbackWith` accepts arbitrary source terms for the coordinates of free target
variables. This stronger interface makes substitution and interpretation
composition possible without special cases for closed formulas.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.TaggedFOInterpretation

variable {V W : Vocabulary} {tags dim n m : Nat}

/-- The tag of a target term under a tag assignment. -/
def termTag (I : TaggedFOInterpretation V W tags dim) (τ : Fin n → Fin tags) :
    Term W n → Fin tags
  | .var i => τ i
  | .const c => I.constTag c

/-- Source terms describing the coordinates of a target term. -/
def termCoords (I : TaggedFOInterpretation V W tags dim)
    (κ : Fin n → Fin dim → Term V m) : Term W n → Fin dim → Term V m
  | .var i => κ i
  | .const c => fun j => .const (I.constCoord c j)

/-- Under a tuple binder, new coordinates are variables and old coordinates are shifted. -/
def liftCoords (κ : Fin n → Fin dim → Term V m) :
    Fin (n + 1) → Fin dim → Term V (m + dim) :=
  Fin.cons (fun j => .var ⟨j.val, by omega⟩) (fun i j => (κ i j).shiftBy dim)

/-- Interpret a target variable assignment from source terms for its coordinates. -/
def coordEnv (A : FinStruct V) (τ : Fin n → Fin tags)
    (κ : Fin n → Fin dim → Term V m) (σ : Env A.card m) :
    Env (tags * A.card ^ dim) n := fun i =>
  (elementEquiv A.card tags dim).symm (τ i, fun j => (κ i j).eval A σ)

/-- Pull back a formula using a tag and a tuple of source terms for every free variable. -/
def pullbackWith (I : TaggedFOInterpretation V W tags dim) :
    {n m : Nat} → Formula W n → (Fin n → Fin tags) →
      (Fin n → Fin dim → Term V m) → Formula V m
  | _, _, .relApp i ts, τ, κ =>
    (I.relFormula i (fun j => I.termTag τ (ts j))).subst
      (fun k => I.termCoords κ (ts (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2)
  | _, _, .eq t₁ t₂, τ, κ =>
    if I.termTag τ t₁ = I.termTag τ t₂ then
      .conjFin (fun j => .eq (I.termCoords κ t₁ j) (I.termCoords κ t₂ j))
    else .falsum
  | _, _, .neg φ, τ, κ => .neg (I.pullbackWith φ τ κ)
  | _, _, .conj φ ψ, τ, κ => .conj (I.pullbackWith φ τ κ) (I.pullbackWith ψ τ κ)
  | _, _, .disj φ ψ, τ, κ => .disj (I.pullbackWith φ τ κ) (I.pullbackWith ψ τ κ)
  | _, _, .exist φ, τ, κ => .disjFin (fun tag =>
    .existBlock dim (I.pullbackWith φ (Fin.cons tag τ) (liftCoords κ)))
  | _, _, .all φ, τ, κ => .conjFin (fun tag =>
    .allBlock dim (I.pullbackWith φ (Fin.cons tag τ) (liftCoords κ)))

/-- Pull back an open formula with one block of source variables per target variable. -/
def translate (I : TaggedFOInterpretation V W tags dim) (φ : Formula W n)
    (τ : Fin n → Fin tags) : Formula V (n * dim) :=
  I.pullbackWith φ τ (fun i j => .var (finProdFinEquiv (i, j)))

/-- Pull back a sentence; there are no free tags or coordinates to supply. -/
def translateSentence (I : TaggedFOInterpretation V W tags dim) (φ : Sentence W) : Sentence V :=
  I.pullbackWith φ Fin.elim0 (fun i => i.elim0)

end Complexity.DescriptiveComplexity.TaggedFOInterpretation
