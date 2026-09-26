/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AC0.NormalForm.Connectives
public import Complexitylib.DescriptiveComplexity.Encoding
public import Complexitylib.DescriptiveComplexity.ModelChecking
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Expanding first-order formulas into unbounded Boolean formulas

For a fixed universe size, the input consists of relation truth tables and
one-hot constant blocks. `StructureInput` assigns wires to those bits. The
compiler supports arbitrary arities, constants, and open formulas. A quantifier
becomes one unbounded gate over all possible values; atomic formulas select
their arguments through the constant blocks.

This is the finite quantifier expansion underlying Immerman's Theorem 5.22,
Section 5.4: <https://people.cs.umass.edu/~immerman/book/ch5.pdf>. The target is
the existing `AC0Formula` tree representation. The surface module combines it
with circuit realization. `Circuit.Validity` supplies encoding validation, and
`DescriptiveComplexity.AC0` packages the complete circuit family.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- Positions of relation bits and one-hot constant bits in an input vector. -/
structure StructureInput (V : Vocabulary) (card N : Nat) where
  /-- The bit for each relation symbol and tuple. -/
  rel : (i : Fin V.numRels) → (Fin (V.relArity i) → Fin card) → Fin N
  /-- The bit asserting that a constant has a specified value. -/
  const : Fin V.numConsts → Fin card → Fin N

namespace StructureInput

variable {V : Vocabulary} {card N n : Nat}

/-- The assigned wires carry the relation tables and exact constant values of a structure. -/
def Represents (A : DecFinStruct V) (L : StructureInput V A.card N)
    (input : BitString N) : Prop :=
  (∀ i args, input (L.rel i args) = A.rel i args) ∧
    ∀ c a, input (L.const c a) = decide (A.const c = a)

/-- Test whether a term has a given value using a constant leaf or one input literal. -/
def termTest (L : StructureInput V card N) (σ : Env card n) :
    Term V n → Fin card → AC0Formula N
  | .var i, a => .const (decide (σ i = a))
  | .const c, a => .lit ⟨L.const c a, true⟩

/-- Select a relation-table entry by testing all its argument values. -/
def relationTest (L : StructureInput V card N) (σ : Env card n)
    (i : Fin V.numRels) (ts : Fin (V.relArity i) → Term V n) : AC0Formula N :=
  .orList ((allTuples card (V.relArity i)).map fun args =>
    .andList (.lit ⟨L.rel i args, true⟩ ::
      (List.finRange (V.relArity i)).map (fun j => L.termTest σ (ts j) (args j))))

/-- Equality holds when the two term selectors agree on some value. -/
def equalityTest (L : StructureInput V card N) (σ : Env card n)
    (t₁ t₂ : Term V n) : AC0Formula N :=
  .orList ((List.finRange card).map fun a =>
    .andList [L.termTest σ t₁ a, L.termTest σ t₂ a])

/-- Expand a formula into an unbounded Boolean formula over the structure input. -/
def compile (L : StructureInput V card N) : {n : Nat} → Formula V n → Env card n → AC0Formula N
  | _, .relApp i ts, σ => L.relationTest σ i ts
  | _, .eq t₁ t₂, σ => L.equalityTest σ t₁ t₂
  | _, .neg φ, σ => (L.compile φ σ).neg
  | _, .conj φ ψ, σ => .andList [L.compile φ σ, L.compile ψ σ]
  | _, .disj φ ψ, σ => .orList [L.compile φ σ, L.compile ψ σ]
  | _, .exist φ, σ => .orList ((List.finRange card).map fun a => L.compile φ (envCons a σ))
  | _, .all φ, σ => .andList ((List.finRange card).map fun a => L.compile φ (envCons a σ))

end StructureInput

/-- The exact syntax-tree size of the quantifier expansion, as a polynomial in universe size. -/
noncomputable def Formula.expansionPolynomial {V : Vocabulary} :
    {n : Nat} → Formula V n → Polynomial Nat
  | _, .relApp i _ => 1 + Polynomial.X ^ (V.relArity i) * Polynomial.C (V.relArity i + 2)
  | _, .eq _ _ => 1 + Polynomial.X * Polynomial.C 3
  | _, .neg φ => φ.expansionPolynomial
  | _, .conj φ ψ => 1 + φ.expansionPolynomial + ψ.expansionPolynomial
  | _, .disj φ ψ => 1 + φ.expansionPolynomial + ψ.expansionPolynomial
  | _, .exist φ => 1 + Polynomial.X * φ.expansionPolynomial
  | _, .all φ => 1 + Polynomial.X * φ.expansionPolynomial

end Complexity.DescriptiveComplexity
