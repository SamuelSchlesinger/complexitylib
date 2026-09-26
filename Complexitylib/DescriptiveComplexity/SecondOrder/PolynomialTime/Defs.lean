/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.Syntax

/-!+# Arithmetic checking of second-order certificates

Represent each free relation by its truth-table string. Matrix evaluation reads
these strings at arithmetic tuple indices. Each existential relation quantifier
consumes the next table from the certificate and prepends it to the environment;
short tables and trailing certificate bits are rejected.

These total functions implement the verifier in Immerman's *Descriptive
Complexity*, Section 7.1, Proposition 7.6. The surface module proves agreement
with the existing checker and polynomial time against the machine definitions.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity.SOFormula

/-- Evaluate an FO matrix directly on structure bits and supplied relation-table strings. -/
def evalMatrixCode {V : Vocabulary} (card : Nat) (input : List Bool) :
    {rctx : List Nat} → {n : Nat} → (φ : SOFormula V rctx n) → φ.IsFOMatrix →
      (Fin n → Nat) → (Fin rctx.length → List Bool) → Bool
  | _, _, .relApp r args, _, σ, _ =>
    input[relationAddress V card r (fun i => (args i).evalCode card input σ)]?.getD false
  | _, _, .soRelApp r args, _, σ, tables =>
    (tables r)[tupleIndex card (fun i => (args i).evalCode card input σ)]?.getD false
  | _, _, .eq a b, _, σ, _ => decide (a.evalCode card input σ = b.evalCode card input σ)
  | _, _, .neg φ, h, σ, tables => !(φ.evalMatrixCode card input h σ tables)
  | _, _, .conj φ ψ, h, σ, tables =>
    φ.evalMatrixCode card input h.1 σ tables && ψ.evalMatrixCode card input h.2 σ tables
  | _, _, .disj φ ψ, h, σ, tables =>
    φ.evalMatrixCode card input h.1 σ tables || ψ.evalMatrixCode card input h.2 σ tables
  | _, _, .exist φ, h, σ, tables =>
    (List.range card).any fun a => φ.evalMatrixCode card input h (Fin.cons a σ) tables
  | _, _, .all φ, h, σ, tables =>
    (List.range card).all fun a => φ.evalMatrixCode card input h (Fin.cons a σ) tables
  | _, _, .soExist _ _, h, _, _ => h.elim
  | _, _, .soAll _ _, h, _, _ => h.elim

/-- Consume the existential prefix's truth tables, then run arithmetic matrix evaluation. -/
def checkCertificateCode {V : Vocabulary} (card : Nat) (input : List Bool) :
    {rctx : List Nat} → {n : Nat} → (φ : SOFormula V rctx n) → φ.IsExistSO →
      (Fin n → Nat) → (Fin rctx.length → List Bool) → List Bool → Bool
  | _, _, .soExist k φ, h, σ, tables, certificate =>
    decide (card ^ k ≤ certificate.length) &&
      φ.checkCertificateCode card input h σ
        (Fin.cons (certificate.take (card ^ k)) tables) (certificate.drop (card ^ k))
  | _, _, φ@(.relApp _ _), h, σ, tables, certificate
  | _, _, φ@(.soRelApp _ _), h, σ, tables, certificate
  | _, _, φ@(.eq _ _), h, σ, tables, certificate
  | _, _, φ@(.neg _), h, σ, tables, certificate
  | _, _, φ@(.conj _ _), h, σ, tables, certificate
  | _, _, φ@(.disj _ _), h, σ, tables, certificate
  | _, _, φ@(.exist _), h, σ, tables, certificate
  | _, _, φ@(.all _), h, σ, tables, certificate =>
    certificate.isEmpty && φ.evalMatrixCode card input (by subst_vars; exact h) σ tables
  | _, _, .soAll _ _, h, _, _, _ => h.elim

end Complexity.DescriptiveComplexity.SOFormula
