/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.Definable
public import Complexitylib.Classes.P.StringAccess
public import Complexitylib.Classes.NP
import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime.Internal
import Complexitylib.Classes.P.Pairing

/-!+# Existential second-order queries belong to NP

For each fixed existential-SO sentence, the existing binary certificate checker
has a polynomial-time one-bit verdict. Arithmetic table reads, bounded
first-order quantifiers, and polynomial-time certificate slicing establish the
machine bound. Validation rejects malformed structures; the existing checker
also rejects missing or trailing certificate bits.

Combining this verifier with its proved polynomial witness bound and the
library's guess-and-verify NTM proves `ExistSODefinable.queryLanguage_mem_NP`.
This is the upper direction of Fagin's theorem, following Immerman's
*Descriptive Complexity*, Section 7.1, Proposition 7.6. The converse tableau
construction is not asserted. Formulas and vocabularies are fixed parameters.
-/

public section

namespace Complexity.DescriptiveComplexity

/-- Arithmetic matrix evaluation agrees with semantics on canonical structure and relation bits. -/
theorem SOFormula.evalMatrixCode_encodeStruct {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) (h : φ.IsFOMatrix)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    φ.evalMatrixCode A.card (encodeStruct A) h (fun i => (σ i).val)
      (fun r => encodeRelC (ρ r)) = true ↔ φ.Sat A.toFinStruct σ ρ.toREnv :=
  matrix_evalCode_sat_internal A φ h σ ρ

/-- Arithmetic matrix evaluation gives exactly the existing Boolean matrix evaluator's verdict. -/
theorem SOFormula.evalMatrixCode_eq_evalMatrixB {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) (h : φ.IsFOMatrix)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    φ.evalMatrixCode A.card (encodeStruct A) h (fun i => (σ i).val)
      (fun r => encodeRelC (ρ r)) = φ.evalMatrixB A h σ ρ := matrix_evalCode_eq_internal A φ h σ ρ

/-- A fixed matrix is polynomial-time on polynomial-time structure bits, values, and tables. -/
theorem SOFormula.evalMatrixCode_fpPred {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (h : φ.IsFOMatrix)
    {input : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} {tables : List Bool → Fin rctx.length → List Bool}
    (hinput : input ∈ FP) (hcard : UnaryFn card) (hσ : ∀ i, UnaryFn fun z => σ z i)
    (ht : ∀ r, (fun z => tables z r) ∈ FP) :
    FPPred fun z => φ.evalMatrixCode (card z) (input z) h (σ z) (tables z) = true :=
  matrix_evalCode_fpPred_internal φ h input card σ tables hinput hcard hσ ht

/-- Arithmetic certificate consumption agrees with the existing checker on encoded structures. -/
theorem SOFormula.checkCertificateCode_encodeStruct {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) (h : φ.IsExistSO)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) (certificate : List Bool) :
    φ.checkCertificateCode A.card (encodeStruct A) h (fun i => (σ i).val)
      (fun r => encodeRelC (ρ r)) certificate = φ.checkCertificate A h σ ρ certificate :=
  certificate_evalCode_eq_internal A φ h σ ρ certificate

/-- Checking a fixed existential prefix is polynomial-time on polynomial-time supplied data. -/
theorem SOFormula.checkCertificateCode_fpPred {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) (h : φ.IsExistSO)
    {input certificate : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} {tables : List Bool → Fin rctx.length → List Bool}
    (hinput : input ∈ FP) (hcard : UnaryFn card) (hσ : ∀ i, UnaryFn fun z => σ z i)
    (ht : ∀ r, (fun z => tables z r) ∈ FP) (hc : certificate ∈ FP) :
    FPPred fun z =>
      φ.checkCertificateCode (card z) (input z) h (σ z) (tables z) (certificate z) = true :=
  certificate_evalCode_fpPred_internal φ h input card σ tables certificate hinput hcard hσ ht hc

/-- The existing encoded certificate checker is a polynomial-time predicate. -/
theorem SOSentence.checkEncoded_fpPred {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) {input certificate : List Bool → List Bool}
    (hinput : input ∈ FP) (hc : certificate ∈ FP) :
    FPPred fun z => φ.checkEncoded h (input z) (certificate z) = true :=
  sentence_checkEncoded_fpPred_internal φ h hinput hc

/-- A polynomial-time machine computes the existing encoded checker's one-bit verdict. -/
theorem SOSentence.checkEncoded_mem_FP {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) :
    (fun z => [φ.checkEncoded h (pairFst z) (pairSnd z)]) ∈ FP := by
  simpa using (φ.checkEncoded_fpPred h pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP

/-- Fagin's upper direction: every fixed existential-SO sentence induces a language in NP. -/
theorem SOSentence.queryLanguage_mem_NP {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) : queryLanguage (fun A => SOSentence.Models A φ) ∈ NP :=
  sentence_queryLanguage_mem_NP_internal φ h

/-- An existential-SO witness places the induced binary query language in machine NP. -/
theorem ExistSODefinable.queryLanguage_mem_NP {V : Vocabulary} {Q : BooleanQuery V}
    (hQ : ExistSODefinable Q) : queryLanguage Q ∈ NP := by
  obtain ⟨φ, h, hφ⟩ := hQ
  have heq : queryLanguage Q = queryLanguage (fun A => SOSentence.Models A φ) := by
    ext input
    simp only [mem_queryLanguage_iff_decodeStruct, hφ]
  rw [heq]
  exact φ.queryLanguage_mem_NP h

end Complexity.DescriptiveComplexity
