/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
public import Complexitylib.DescriptiveComplexity.SecondOrder.Certificate
public import Complexitylib.Classes.NP
import Complexitylib.Classes.P
import Complexitylib.Classes.P.DecisionFn
import Complexitylib.Classes.NP.Verifier

/-!+# Correctness and polynomial time of second-order verification

Arithmetic matrix evaluation agrees with semantic satisfaction when supplied
canonical relation tables. Certificate consumption agrees with the existing
decoder-based checker. Bounded bit access, quantification, and string slicing
then give the polynomial-time verifier required by the NP witness construction.
-/

public section

namespace Complexity.DescriptiveComplexity

private theorem envCons_val {card n : Nat} (a : Fin card) (σ : Env card n) :
    (fun i => (envCons a σ i).val) = Fin.cons a.val (fun i => (σ i).val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [envCons]

theorem matrix_evalCode_sat_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) :
    ∀ (h : φ.IsFOMatrix) (σ : Env A.card n) (ρ : DecREnv A.card rctx),
      φ.evalMatrixCode A.card (encodeStruct A) h (fun i => (σ i).val)
        (fun r => encodeRelC (ρ r)) = true ↔ φ.Sat A.toFinStruct σ ρ.toREnv := by
  induction φ with
  | relApp r args =>
    intro h σ ρ
    change (encodeStruct A)[relationAddress V A.card r
      (fun i => (args i).evalCode A.card (encodeStruct A) (fun j => (σ j).val))]?.getD false =
        true ↔ A.rel r (fun i => (args i).eval A.toFinStruct σ) = true
    simp only [Term.evalCode_encodeStruct]
    rw [getElem?_encodeStruct_relation A r (fun i => (args i).eval A.toFinStruct σ)]
    rfl
  | soRelApp r args =>
    intro h σ ρ
    change (encodeRelC (ρ r))[tupleIndex A.card
      (fun i => (args i).evalCode A.card (encodeStruct A) (fun j => (σ j).val))]?.getD false =
        true ↔ ρ r (fun i => (args i).eval A.toFinStruct σ) = true
    simp only [Term.evalCode_encodeStruct]
    rw [getElem?_encodeRelC_index (ρ r) (fun i => (args i).eval A.toFinStruct σ)]
    rfl
  | eq a b =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixCode, Term.evalCode_encodeStruct, decide_eq_true_eq,
      SOFormula.Sat, Fin.ext_iff]
  | neg φ ih =>
    intro h σ ρ
    simpa only [SOFormula.evalMatrixCode, Bool.not_eq_true', Bool.eq_false_iff, SOFormula.Sat]
      using not_congr (ih h σ ρ)
  | conj φ ψ ihφ ihψ =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixCode, Bool.and_eq_true, SOFormula.Sat]
    exact and_congr (ihφ h.1 σ ρ) (ihψ h.2 σ ρ)
  | disj φ ψ ihφ ihψ =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixCode, Bool.or_eq_true, SOFormula.Sat]
    exact or_congr (ihφ h.1 σ ρ) (ihψ h.2 σ ρ)
  | exist φ ih =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixCode, List.any_eq_true, List.mem_range, SOFormula.Sat]
    change _ ↔ ∃ a : Fin A.card, φ.Sat A.toFinStruct (envCons a σ) ρ.toREnv
    constructor
    · rintro ⟨a, ha, hsat⟩
      refine ⟨⟨a, ha⟩, (ih h (envCons ⟨a, ha⟩ σ) ρ).mp ?_⟩
      rw [envCons_val]
      exact hsat
    · rintro ⟨a, hsat⟩
      refine ⟨a.val, a.isLt, ?_⟩
      have he := (ih h (envCons a σ) ρ).mpr hsat
      rw [envCons_val a σ] at he
      exact he
  | all φ ih =>
    intro h σ ρ
    simp only [SOFormula.evalMatrixCode, List.all_eq_true, List.mem_range, SOFormula.Sat]
    change _ ↔ ∀ a : Fin A.card, φ.Sat A.toFinStruct (envCons a σ) ρ.toREnv
    constructor
    · intro hsat a
      apply (ih h (envCons a σ) ρ).mp
      rw [envCons_val a σ]
      exact hsat a.val a.isLt
    · intro hsat a ha
      have he := (ih h (envCons ⟨a, ha⟩ σ) ρ).mpr (hsat ⟨a, ha⟩)
      rw [envCons_val] at he
      exact he
  | soExist k φ ih | soAll k φ ih => intro h; exact h.elim

theorem matrix_evalCode_eq_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) (h : φ.IsFOMatrix)
    (σ : Env A.card n) (ρ : DecREnv A.card rctx) :
    φ.evalMatrixCode A.card (encodeStruct A) h (fun i => (σ i).val)
      (fun r => encodeRelC (ρ r)) = φ.evalMatrixB A h σ ρ := by
  apply Bool.eq_iff_iff.mpr
  exact (matrix_evalCode_sat_internal A φ h σ ρ).trans (φ.evalMatrixB_eq_sat A h σ ρ).symm

private theorem loop_env_unary {n : Nat} {σ : List Bool → Fin n → Nat}
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    ∀ i : Fin (n + 1),
      UnaryFn fun z => (Fin.cons (pairSnd z).length (σ (pairFst z)) : Fin (n + 1) → Nat) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact UnaryFn.index
  · exact (hσ j).lift

theorem matrix_evalCode_fpPred_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) : ∀ (h : φ.IsFOMatrix)
      (input : List Bool → List Bool) (card : List Bool → Nat)
      (σ : List Bool → Fin n → Nat) (tables : List Bool → Fin rctx.length → List Bool),
      input ∈ FP → UnaryFn card → (∀ i, UnaryFn fun z => σ z i) →
      (∀ r, (fun z => tables z r) ∈ FP) →
        FPPred fun z => φ.evalMatrixCode (card z) (input z) h (σ z) (tables z) = true := by
  induction φ with
  | relApp r args =>
    intro h input card σ tables hinput hcard hσ ht
    exact relationBit_fpPred V r hinput hcard
      (fun i => (args i).evalCode_unary hinput hcard hσ)
  | soRelApp r args =>
    intro h input card σ tables hinput hcard hσ ht
    exact FPPred.getBit (ht r)
      (tupleIndex_unary hcard (fun i => (args i).evalCode_unary hinput hcard hσ))
  | eq a b =>
    intro h input card σ tables hinput hcard hσ ht
    exact (FPPred.eq (a.evalCode_unary hinput hcard hσ)
      (b.evalCode_unary hinput hcard hσ)).of_iff fun z => by
        simp only [SOFormula.evalMatrixCode, decide_eq_true_eq]
  | neg φ ih =>
    intro h input card σ tables hinput hcard hσ ht
    exact (ih h input card σ tables hinput hcard hσ ht).not.of_iff fun z => by
      simp only [SOFormula.evalMatrixCode, Bool.not_eq_true', Bool.eq_false_iff]
  | conj φ ψ ihφ ihψ =>
    intro h input card σ tables hinput hcard hσ ht
    exact ((ihφ h.1 input card σ tables hinput hcard hσ ht).and
      (ihψ h.2 input card σ tables hinput hcard hσ ht)).of_iff fun z => by
        simp only [SOFormula.evalMatrixCode, Bool.and_eq_true]
  | disj φ ψ ihφ ihψ =>
    intro h input card σ tables hinput hcard hσ ht
    exact ((ihφ h.1 input card σ tables hinput hcard hσ ht).or
      (ihψ h.2 input card σ tables hinput hcard hσ ht)).of_iff fun z => by
        simp only [SOFormula.evalMatrixCode, Bool.or_eq_true]
  | exist φ ih =>
    intro h input card σ tables hinput hcard hσ ht
    have hbody := ih h (fun z => input (pairFst z)) (fun z => card (pairFst z))
      (fun z => Fin.cons (pairSnd z).length (σ (pairFst z))) (fun z => tables (pairFst z))
      (mem_FP_comp pairFst_mem_FP hinput) hcard.lift (loop_env_unary hσ)
      (fun r => mem_FP_comp pairFst_mem_FP (ht r))
    exact (FPPred.exists_lt hcard hbody).of_iff fun z => by
      simp [SOFormula.evalMatrixCode, List.any_eq_true]
  | all φ ih =>
    intro h input card σ tables hinput hcard hσ ht
    have hbody := ih h (fun z => input (pairFst z)) (fun z => card (pairFst z))
      (fun z => Fin.cons (pairSnd z).length (σ (pairFst z))) (fun z => tables (pairFst z))
      (mem_FP_comp pairFst_mem_FP hinput) hcard.lift (loop_env_unary hσ)
      (fun r => mem_FP_comp pairFst_mem_FP (ht r))
    exact (FPPred.forall_lt hcard hbody).of_iff fun z => by
      simp [SOFormula.evalMatrixCode, List.all_eq_true]
  | soExist k φ ih | soAll k φ ih => intro h; exact h.elim

private theorem encode_tables_cons {card k : Nat} {rctx : List Nat}
    (ρ : DecREnv card rctx) (S : (Fin k → Fin card) → Bool) :
    (fun r => encodeRelC ((ρ.cons S) r)) =
      Fin.cons (encodeRelC S) (fun r => encodeRelC (ρ r)) := by
  funext r
  refine Fin.cases ?_ (fun i => ?_) r <;> rfl

private theorem encode_singleton {card k : Nat} (ρ : DecREnv card [k]) :
    ρ.encode = encodeRelC (ρ 0) := by
  simp [DecREnv.encode_eq_flatMap, List.finRange_succ]

theorem certificate_evalCode_eq_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (A : DecFinStruct V) (φ : SOFormula V rctx n) :
    ∀ (h : φ.IsExistSO) (σ : Env A.card n) (ρ : DecREnv A.card rctx) (certificate : List Bool),
      φ.checkCertificateCode A.card (encodeStruct A) h (fun i => (σ i).val)
        (fun r => encodeRelC (ρ r)) certificate = φ.checkCertificate A h σ ρ certificate := by
  induction φ with
  | soExist k φ ih =>
    intro h σ ρ certificate
    simp only [SOFormula.checkCertificateCode, SOFormula.checkCertificate]
    cases hd : DecREnv.decode A.card [k] (certificate.take (A.card ^ k)) with
    | none =>
      have hlen := (DecREnv.decode_eq_none_iff _ _ _).mp hd
      simp only [List.length_take, DecREnv.encodingLength_cons,
        DecREnv.encodingLength_nil, Nat.add_zero] at hlen
      have hshort : ¬ A.card ^ k ≤ certificate.length := by omega
      simp [hshort]
    | some τ =>
      have he := (DecREnv.decode_eq_some_iff _ τ).mp hd
      have hlen := congrArg List.length he
      simp only [DecREnv.encode_length, DecREnv.encodingLength_cons,
        DecREnv.encodingLength_nil, Nat.add_zero, List.length_take] at hlen
      have hbound : A.card ^ k ≤ certificate.length := by omega
      have htable : encodeRelC (τ 0) = certificate.take (A.card ^ k) :=
        (encode_singleton τ).symm.trans he
      simp only [hbound, decide_true, Bool.true_and]
      rw [← htable, ← encode_tables_cons]
      exact ih h σ (ρ.cons (τ 0)) (certificate.drop (A.card ^ k))
  | soAll k φ ih => intro h; exact h.elim
  | relApp r args | soRelApp r args | eq a b | neg φ ih | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ | exist φ ih | all φ ih =>
    intro h σ ρ certificate
    simp only [SOFormula.checkCertificateCode, SOFormula.checkCertificate,
      matrix_evalCode_eq_internal]

private theorem tables_cons_mem_FP {m : Nat}
    {tables : List Bool → Fin m → List Bool} {bits : List Bool → List Bool}
    (ht : ∀ r, (fun z => tables z r) ∈ FP) (hb : bits ∈ FP) :
    ∀ r : Fin (m + 1),
      (fun z => (Fin.cons (bits z) (tables z) : Fin (m + 1) → List Bool) r) ∈ FP := by
  intro r
  refine Fin.cases ?_ (fun i => ?_) r
  · exact hb
  · exact ht i

theorem certificate_evalCode_fpPred_internal {V : Vocabulary} {rctx : List Nat} {n : Nat}
    (φ : SOFormula V rctx n) : ∀ (h : φ.IsExistSO)
      (input : List Bool → List Bool) (card : List Bool → Nat)
      (σ : List Bool → Fin n → Nat) (tables : List Bool → Fin rctx.length → List Bool)
      (certificate : List Bool → List Bool),
      input ∈ FP → UnaryFn card → (∀ i, UnaryFn fun z => σ z i) →
      (∀ r, (fun z => tables z r) ∈ FP) → certificate ∈ FP →
        FPPred fun z =>
          φ.checkCertificateCode (card z) (input z) h (σ z) (tables z) (certificate z) = true := by
  induction φ with
  | soExist k φ ih =>
    intro h input card σ tables certificate hinput hcard hσ ht hc
    have hsize := hcard.pow_const k
    have htake := take_mem_FP hc hsize
    have hdrop := drop_mem_FP hc hsize
    have htables := tables_cons_mem_FP ht htake
    have hbody := ih h input card σ
      (fun z => Fin.cons ((certificate z).take (card z ^ k)) (tables z))
      (fun z => (certificate z).drop (card z ^ k)) hinput hcard hσ htables hdrop
    exact ((FPPred.le hsize (UnaryFn.length hc)).and hbody).of_iff fun z => by
      simp only [SOFormula.checkCertificateCode, Bool.and_eq_true, decide_eq_true_eq]
  | soAll k φ ih => intro h; exact h.elim
  | relApp r args | soRelApp r args | eq a b | neg φ ih | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ | exist φ ih | all φ ih =>
    intro h input card σ tables certificate hinput hcard hσ ht hc
    have hempty := FPPred.eq (UnaryFn.length hc) (UnaryFn.const 0)
    have hmatrix := matrix_evalCode_fpPred_internal _ h input card σ tables hinput hcard hσ ht
    exact (hempty.and hmatrix).of_iff fun z => by
      simp only [SOFormula.checkCertificateCode, Bool.and_eq_true, List.isEmpty_iff,
        List.length_eq_zero_iff]

private theorem emptyEnv_val (card : Nat) :
    (fun i => (emptyEnv card i).val) = (Fin.elim0 : Fin 0 → Nat) := by
  funext i
  exact i.elim0

private theorem empty_tables (card : Nat) :
    (fun r => encodeRelC (DecREnv.empty card r)) = (Fin.elim0 : Fin 0 → List Bool) := by
  funext r
  exact r.elim0

theorem sentence_checkEncoded_code_iff_internal {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) (input certificate : List Bool) :
    φ.checkEncoded h input certificate = true ↔
      (∃ A : DecFinStruct V, encodeStruct A = input) ∧
        φ.checkCertificateCode (input.takeWhile id).length input h Fin.elim0 Fin.elim0
          certificate = true := by
  cases hd : decodeStruct V input with
  | none =>
    have hn := (decodeStruct_eq_none_iff input).mp hd
    simp [SOSentence.checkEncoded, hd, hn]
  | some A =>
    obtain rfl := (decodeStruct_eq_some_iff input A).mp hd
    have he := certificate_evalCode_eq_internal A φ h (emptyEnv A.card)
      (DecREnv.empty A.card) certificate
    rw [emptyEnv_val, empty_tables] at he
    simp only [SOSentence.checkEncoded_encodeStruct, encodeStruct_card, he]
    exact ⟨fun hc => ⟨⟨A, rfl⟩, hc⟩, And.right⟩

theorem sentence_checkEncoded_fpPred_internal {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) {input certificate : List Bool → List Bool}
    (hinput : input ∈ FP) (hc : certificate ∈ FP) :
    FPPred fun z => φ.checkEncoded h (input z) (certificate z) = true := by
  have hraw := certificate_evalCode_fpPred_internal φ h input
    (fun z => ((input z).takeWhile id).length) (fun _ => Fin.elim0) (fun _ => Fin.elim0)
    certificate hinput (UnaryFn.leadingTrueLength hinput) (fun i => Fin.elim0 i)
    (fun r => Fin.elim0 r) hc
  exact (((encodable_fpPred V).comp hinput).and hraw).of_iff fun z =>
    (sentence_checkEncoded_code_iff_internal φ h (input z) (certificate z)).symm

theorem sentence_queryLanguage_mem_NP_internal {V : Vocabulary} (φ : SOSentence V)
    (h : φ.IsExistSO) : queryLanguage (fun A => SOSentence.Models A φ) ∈ NP := by
  let verifier : Language := {z | φ.checkEncoded h (pairFst z) (pairSnd z) = true}
  have hv : verifier ∈ P :=
    (sentence_checkEncoded_fpPred_internal φ h pairFst_mem_FP pairSnd_mem_FP).mem_P
  apply mem_NP_of_poly_witness φ.witnessPolynomial hv
  · intro input certificate haccept
    change φ.checkEncoded h (pairFst (pair input certificate))
      (pairSnd (pair input certificate)) = true at haccept
    simp only [pairFst_pair, pairSnd_pair] at haccept
    exact φ.checkEncoded_length_le h input certificate haccept
  · intro input
    simp only [verifier, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
    exact (φ.exists_checkEncoded_iff h input).symm

end Complexity.DescriptiveComplexity
