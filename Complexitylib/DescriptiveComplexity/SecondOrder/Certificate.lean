/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate.Defs
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate.Internal

/-!
# Verified binary certificates for existential second-order logic

An existential-SO formula is true exactly when its certificate checker accepts
some bit string. Every accepted certificate has exactly the sum of the truth
table sizes of the prefix relations. For sentences, the encoded checker gives
the same characterization of the existing query language, rejects malformed
structure encodings, and bounds certificate length by a fixed polynomial in
input length. `SecondOrder.PolynomialTime` proves that a polynomial-time machine
computes the checker's verdict, giving the upper direction of Fagin's theorem.
-/

public section

namespace Complexity.DescriptiveComplexity

namespace SOFormula

variable {V : Vocabulary} {rctx : List Nat} {n : Nat}

/-- An FO matrix has no relation-witness prefix. -/
theorem witnessArities_of_isFOMatrix (φ : SOFormula V rctx n) (h : φ.IsFOMatrix) :
    φ.witnessArities = [] := by
  cases φ <;> first | rfl | exact h.elim

/-- The witness polynomial evaluates to the exact sum of relation-table sizes. -/
@[simp] theorem witnessPolynomial_eval (φ : SOFormula V rctx n) (card : Nat) :
    φ.witnessPolynomial.eval card = DecREnv.encodingLength card φ.witnessArities :=
  DecREnv.encodingPolynomial_eval card φ.witnessArities

/-- A matrix consumes no witness bits and uses the existing matrix evaluator. -/
theorem checkCertificate_matrix (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (hm : φ.IsFOMatrix) (σ : Env A.card n)
    (ρ : DecREnv A.card rctx) (bits : List Bool) :
    φ.checkCertificate A h σ ρ bits = (bits.isEmpty && φ.evalMatrixB A hm σ ρ) := by
  cases φ <;> first | rfl | exact hm.elim

/-- An embedded FO formula needs the empty certificate and runs the FO evaluator. -/
theorem checkCertificate_ofFormula (A : DecFinStruct V) (φ : Formula V n)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool) :
    (ofFormula φ rctx).checkCertificate A (ofFormula_isExistSO φ rctx) σ ρ bits =
      (bits.isEmpty && Formula.evalB A σ φ) := by
  rw [checkCertificate_matrix A _ _ (ofFormula_isFOMatrix φ rctx), evalMatrixB_ofFormula]

/-- An encoded prefix table is consumed exactly, leaving the next relation environment. -/
theorem checkCertificate_soExist_append (A : DecFinStruct V) {k : Nat}
    (φ : SOFormula V (k :: rctx) n) (h : φ.IsExistSO) (σ : Env A.card n)
    (ρ : DecREnv A.card rctx) (τ : DecREnv A.card [k]) (bits : List Bool) :
    (soExist k φ).checkCertificate A h σ ρ (τ.encode ++ bits) =
      φ.checkCertificate A h σ (ρ.cons (τ 0)) bits := by
  have hlen : τ.encode.length = A.card ^ k := by simp
  simp only [checkCertificate, List.take_left' hlen, List.drop_left' hlen,
    DecREnv.decode_encode]

/-- An accepted certificate proves satisfaction of the existential-SO formula. -/
theorem checkCertificate_sound (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool)
    (haccept : φ.checkCertificate A h σ ρ bits = true) :
    φ.Sat A.toFinStruct σ ρ.toREnv :=
  (checkCertificate_sound_internal A φ h σ ρ bits haccept).2

/-- Every accepted certificate has exactly the prescribed truth-table length. -/
theorem checkCertificate_length (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (bits : List Bool)
    (haccept : φ.checkCertificate A h σ ρ bits = true) :
    bits.length = DecREnv.encodingLength A.card φ.witnessArities :=
  (checkCertificate_sound_internal A φ h σ ρ bits haccept).1

/-- Binary certificates are sound and complete for existential-SO satisfaction. -/
theorem exists_checkCertificate_iff (A : DecFinStruct V) (φ : SOFormula V rctx n)
    (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    (∃ bits, φ.checkCertificate A h σ ρ bits = true) ↔
      φ.Sat A.toFinStruct σ ρ.toREnv :=
  ⟨fun ⟨bits, hb⟩ => checkCertificate_sound A φ h σ ρ bits hb,
    checkCertificate_complete_internal A φ h σ ρ⟩

end SOFormula

namespace SOSentence

variable {V : Vocabulary}

/-- Checking on a valid structure encoding agrees with structure-level certificate checking. -/
@[simp] theorem checkEncoded_encodeStruct (φ : SOSentence V) (h : φ.IsExistSO)
    (A : DecFinStruct V) (certificate : List Bool) :
    φ.checkEncoded h (encodeStruct A) certificate =
      φ.checkCertificate A h (emptyEnv A.card) (DecREnv.empty A.card) certificate := by
  simp only [checkEncoded, decodeStruct_encodeStruct]

/-- A malformed structure encoding is rejected with every certificate. -/
theorem checkEncoded_of_decode_eq_none (φ : SOSentence V) (h : φ.IsExistSO)
    (input certificate : List Bool) (hinput : decodeStruct V input = none) :
    φ.checkEncoded h input certificate = false := by
  simp only [checkEncoded, hinput]

/-- The encoded checker has a witness exactly on the sentence's induced language. -/
theorem exists_checkEncoded_iff (φ : SOSentence V) (h : φ.IsExistSO) (input : List Bool) :
    (∃ certificate, φ.checkEncoded h input certificate = true) ↔
      input ∈ queryLanguage (fun A => Models A φ) := by
  rw [mem_queryLanguage_iff_decodeStruct]
  cases hd : decodeStruct V input with
  | none => simp [checkEncoded, hd]
  | some A =>
    simp only [checkEncoded, hd, Option.some.injEq, exists_eq_left',
      SOFormula.exists_checkCertificate_iff, DecREnv.toREnv_empty, Models]
    rfl

/-- An accepted certificate has exactly the table size determined by the input cardinality. -/
theorem checkEncoded_certificate_length (φ : SOSentence V) (h : φ.IsExistSO)
    (input certificate : List Bool) (haccept : φ.checkEncoded h input certificate = true) :
    certificate.length =
      DecREnv.encodingLength (input.takeWhile id).length φ.witnessArities := by
  cases hd : decodeStruct V input with
  | none => simp [checkEncoded, hd] at haccept
  | some A =>
    obtain rfl := (decodeStruct_eq_some_iff input A).mp hd
    rw [checkEncoded_encodeStruct] at haccept
    rw [encodeStruct_card]
    exact φ.checkCertificate_length A h _ _ certificate haccept

/-- Accepted certificates are polynomially bounded in the encoded input length. -/
theorem checkEncoded_length_le (φ : SOSentence V) (h : φ.IsExistSO)
    (input certificate : List Bool) (haccept : φ.checkEncoded h input certificate = true) :
    certificate.length ≤ φ.witnessPolynomial.eval input.length := by
  rw [checkEncoded_certificate_length φ h input certificate haccept,
    SOFormula.witnessPolynomial_eval]
  exact DecREnv.encodingLength_mono φ.witnessArities (List.takeWhile_sublist id).length_le

/-- Adding the polynomial certificate bound preserves the exact language characterization. -/
theorem exists_checkEncoded_bounded_iff (φ : SOSentence V) (h : φ.IsExistSO)
    (input : List Bool) :
    (∃ certificate, certificate.length ≤ φ.witnessPolynomial.eval input.length ∧
      φ.checkEncoded h input certificate = true) ↔
        input ∈ queryLanguage (fun A => Models A φ) := by
  rw [← exists_checkEncoded_iff φ h input]
  exact ⟨fun ⟨certificate, _, hc⟩ => ⟨certificate, hc⟩,
    fun ⟨certificate, hc⟩ => ⟨certificate, checkEncoded_length_le φ h input certificate hc, hc⟩⟩

end SOSentence

end Complexity.DescriptiveComplexity
