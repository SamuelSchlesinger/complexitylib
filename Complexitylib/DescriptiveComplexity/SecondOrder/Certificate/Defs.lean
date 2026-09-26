/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Encoding
public import Complexitylib.DescriptiveComplexity.SecondOrder.ModelChecking
public import Complexitylib.DescriptiveComplexity.Language

/-!
# Binary witness checking for existential second-order formulas

A certificate lists the truth tables of the leading existential relation
quantifiers, in outermost-first order. Each quantifier reads exactly its table;
the remaining FO matrix is checked only after all certificate bits are consumed.
Both missing bits and trailing data are rejected. Free element values and free
Boolean relation tables are also supported.

This implements the witness-checking algorithm of Immerman, Section 7.1,
Proposition 7.6. Correctness and polynomial certificate length are proved in
the surface module. `SecondOrder.PolynomialTime` supplies the polynomial-time
machine bound by proving agreement with an arithmetic verifier.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

namespace SOFormula

/-- Arities of the leading existential relation quantifiers, outermost first. -/
def witnessArities {V : Vocabulary} : {rctx : List Nat} → {n : Nat} →
    SOFormula V rctx n → List Nat
  | _, _, .soExist k φ => k :: φ.witnessArities
  | _, _, _ => []

/-- The exact certificate length as a polynomial in the universe cardinality. -/
noncomputable def witnessPolynomial {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) : Polynomial Nat :=
  DecREnv.encodingPolynomial φ.witnessArities

/-- Check supplied truth tables for the existential prefix, then evaluate its matrix. -/
def checkCertificate {V : Vocabulary} (A : DecFinStruct V) :
    {rctx : List Nat} → {n : Nat} → (φ : SOFormula V rctx n) →
      φ.IsExistSO → Env A.card n → DecREnv A.card rctx → List Bool → Bool
  | _, _, .soExist k φ, h, σ, ρ, bits =>
    match DecREnv.decode A.card [k] (bits.take (A.card ^ k)) with
    | none => false
    | some τ => φ.checkCertificate A h σ (ρ.cons (τ 0)) (bits.drop (A.card ^ k))
  | _, _, φ@(.relApp _ _), h, σ, ρ, bits
  | _, _, φ@(.soRelApp _ _), h, σ, ρ, bits
  | _, _, φ@(.eq _ _), h, σ, ρ, bits
  | _, _, φ@(.neg _), h, σ, ρ, bits
  | _, _, φ@(.conj _ _), h, σ, ρ, bits
  | _, _, φ@(.disj _ _), h, σ, ρ, bits
  | _, _, φ@(.exist _), h, σ, ρ, bits
  | _, _, φ@(.all _), h, σ, ρ, bits =>
    bits.isEmpty && φ.evalMatrixB A (by subst_vars; exact h) σ ρ
  | _, _, .soAll _ _, h, _, _, _ => h.elim

end SOFormula

/-- Check an existential-SO sentence's binary certificate on an encoded structure. -/
def SOSentence.checkEncoded {V : Vocabulary} (φ : SOSentence V) (h : φ.IsExistSO)
    (input certificate : List Bool) : Bool :=
  match decodeStruct V input with
  | none => false
  | some A => φ.checkCertificate A h (emptyEnv A.card) (DecREnv.empty A.card) certificate

end Complexity.DescriptiveComplexity
