/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
public import Complexitylib.DescriptiveComplexity.Language
public import Complexitylib.DescriptiveComplexity.ModelChecking
import Complexitylib.Classes.P

/-!
# Correctness and polynomial time of arithmetic first-order evaluation

Constant lookup recovers the unique marked entry. Arithmetic reads and bounded
quantifiers then support structural induction on the formula, both for semantic
correctness and for the machine-level polynomial-time proof.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem term_evalCode_encodeStruct_internal {V : Vocabulary} {n : Nat}
    (A : DecFinStruct V) (t : Term V n) (σ : Env A.card n) :
    t.evalCode A.card (encodeStruct A) (fun i => (σ i).val) =
      (t.eval A.toFinStruct σ).val := by
  cases t with
  | var i => rfl
  | const c =>
    change (List.range A.card).findIdx _ = (A.const c).val
    apply (List.findIdx_eq (by simp)).mpr
    constructor
    · simp only [List.getElem_range]
      rw [getElem?_encodeStruct_constant A c (A.const c)]
      simp
    · intro i hi
      have hbound : i < A.card := hi.trans (A.const c).isLt
      simp only [List.getElem_range]
      rw [getElem?_encodeStruct_constant A c ⟨i, hbound⟩]
      simp only [Option.getD_some, Fin.ext_iff]
      exact decide_eq_false (by omega)

theorem term_evalCode_unary_internal {V : Vocabulary} {n : Nat} (t : Term V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    {σ : List Bool → Fin n → Nat} (hbits : bits ∈ FP) (hcard : UnaryFn card)
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    UnaryFn fun z => t.evalCode (card z) (bits z) (σ z) := by
  cases t with
  | var i => exact hσ i
  | const c =>
    have htest := constantBit_fpPred V c (mem_FP_comp pairFst_mem_FP hbits)
      hcard.lift UnaryFn.index
    exact (hcard.find htest).of_eq fun z => by
      simp [Term.evalCode]

private theorem envCons_val {card n : Nat} (a : Fin card) (σ : Env card n) :
    (fun i => (envCons a σ i).val) = Fin.cons a.val (fun i => (σ i).val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [envCons]

theorem formula_evalCode_encodeStruct_internal {V : Vocabulary} {n : Nat}
    (A : DecFinStruct V) (φ : Formula V n) : ∀ σ : Env A.card n,
      φ.evalCode A.card (encodeStruct A) (fun i => (σ i).val) = true ↔
        φ.Sat A.toFinStruct σ := by
  induction φ with
  | relApp r args =>
    intro σ
    change (encodeStruct A)[relationAddress V A.card r
      (fun i => (args i).evalCode A.card (encodeStruct A) (fun j => (σ j).val))]?.getD false =
        true ↔ A.rel r (fun i => (args i).eval A.toFinStruct σ) = true
    simp only [term_evalCode_encodeStruct_internal]
    rw [getElem?_encodeStruct_relation A r (fun i => (args i).eval A.toFinStruct σ)]
    rfl
  | eq a b =>
    intro σ
    simp only [Formula.evalCode, term_evalCode_encodeStruct_internal, decide_eq_true_eq,
      Formula.Sat, Fin.ext_iff]
  | neg φ ih =>
    intro σ
    simpa only [Formula.evalCode, Bool.not_eq_true', Bool.eq_false_iff, Formula.Sat] using
      not_congr (ih σ)
  | conj φ ψ ihφ ihψ =>
    intro σ
    simp only [Formula.evalCode, Bool.and_eq_true, Formula.Sat]
    exact and_congr (ihφ σ) (ihψ σ)
  | disj φ ψ ihφ ihψ =>
    intro σ
    simp only [Formula.evalCode, Bool.or_eq_true, Formula.Sat]
    exact or_congr (ihφ σ) (ihψ σ)
  | exist φ ih =>
    intro σ
    simp only [Formula.evalCode, List.any_eq_true, List.mem_range, Formula.Sat]
    change _ ↔ ∃ a : Fin A.card, φ.Sat A.toFinStruct (envCons a σ)
    constructor
    · rintro ⟨a, ha, h⟩
      refine ⟨⟨a, ha⟩, (ih (envCons ⟨a, ha⟩ σ)).mp ?_⟩
      rw [envCons_val]
      exact h
    · rintro ⟨a, h⟩
      refine ⟨a.val, a.isLt, ?_⟩
      have he := (ih (envCons a σ)).mpr h
      rw [envCons_val a σ] at he
      exact he
  | all φ ih =>
    intro σ
    simp only [Formula.evalCode, List.all_eq_true, List.mem_range, Formula.Sat]
    change _ ↔ ∀ a : Fin A.card, φ.Sat A.toFinStruct (envCons a σ)
    constructor
    · intro h a
      apply (ih (envCons a σ)).mp
      rw [envCons_val a σ]
      exact h a.val a.isLt
    · intro h a ha
      have he := (ih (envCons ⟨a, ha⟩ σ)).mpr (h ⟨a, ha⟩)
      rw [envCons_val] at he
      exact he

private theorem loop_env_unary {n : Nat} {σ : List Bool → Fin n → Nat}
    (hσ : ∀ i, UnaryFn fun z => σ z i) :
    ∀ i : Fin (n + 1),
      UnaryFn fun z => (Fin.cons (pairSnd z).length (σ (pairFst z)) : Fin (n + 1) → Nat) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact UnaryFn.index
  · exact (hσ j).lift

theorem formula_evalCode_fpPred_internal {V : Vocabulary} {n : Nat} (φ : Formula V n) :
    ∀ (bits : List Bool → List Bool) (card : List Bool → Nat) (σ : List Bool → Fin n → Nat),
      bits ∈ FP → UnaryFn card → (∀ i, UnaryFn fun z => σ z i) →
        FPPred fun z => φ.evalCode (card z) (bits z) (σ z) = true := by
  induction φ with
  | relApp r args =>
    intro bits card σ hbits hcard hσ
    exact relationBit_fpPred V r hbits hcard
      (fun i => term_evalCode_unary_internal (args i) hbits hcard hσ)
  | eq a b =>
    intro bits card σ hbits hcard hσ
    exact (FPPred.eq (term_evalCode_unary_internal a hbits hcard hσ)
      (term_evalCode_unary_internal b hbits hcard hσ)).of_iff fun z => by
        simp only [Formula.evalCode, decide_eq_true_eq]
  | neg φ ih =>
    intro bits card σ hbits hcard hσ
    exact (ih bits card σ hbits hcard hσ).not.of_iff fun z => by
      simp only [Formula.evalCode, Bool.not_eq_true', Bool.eq_false_iff]
  | conj φ ψ ihφ ihψ =>
    intro bits card σ hbits hcard hσ
    exact ((ihφ bits card σ hbits hcard hσ).and
      (ihψ bits card σ hbits hcard hσ)).of_iff fun z => by
        simp only [Formula.evalCode, Bool.and_eq_true]
  | disj φ ψ ihφ ihψ =>
    intro bits card σ hbits hcard hσ
    exact ((ihφ bits card σ hbits hcard hσ).or
      (ihψ bits card σ hbits hcard hσ)).of_iff fun z => by
        simp only [Formula.evalCode, Bool.or_eq_true]
  | exist φ ih =>
    intro bits card σ hbits hcard hσ
    have hbody := ih (fun z => bits (pairFst z)) (fun z => card (pairFst z))
      (fun z => Fin.cons (pairSnd z).length (σ (pairFst z)))
      (mem_FP_comp pairFst_mem_FP hbits) hcard.lift (loop_env_unary hσ)
    exact (FPPred.exists_lt hcard hbody).of_iff fun z => by
      simp [Formula.evalCode, List.any_eq_true]
  | all φ ih =>
    intro bits card σ hbits hcard hσ
    have hbody := ih (fun z => bits (pairFst z)) (fun z => card (pairFst z))
      (fun z => Fin.cons (pairSnd z).length (σ (pairFst z)))
      (mem_FP_comp pairFst_mem_FP hbits) hcard.lift (loop_env_unary hσ)
    exact (FPPred.forall_lt hcard hbody).of_iff fun z => by
      simp [Formula.evalCode, List.all_eq_true]

private theorem emptyEnv_val (card : Nat) :
    (fun i => (emptyEnv card i).val) = (Fin.elim0 : Fin 0 → Nat) := by
  funext i
  exact i.elim0

theorem sentence_evalCode_encodeStruct_internal {V : Vocabulary} (A : DecFinStruct V)
    (φ : Sentence V) :
    φ.evalCode A.card (encodeStruct A) Fin.elim0 = true ↔ Sentence.Models A.toFinStruct φ := by
  have h := formula_evalCode_encodeStruct_internal A φ (emptyEnv A.card)
  rw [emptyEnv_val] at h
  exact h

theorem sentence_validatedCode_internal {V : Vocabulary} (φ : Sentence V) (input : List Bool) :
    ((∃ A : DecFinStruct V, encodeStruct A = input) ∧
      φ.evalCode (input.takeWhile id).length input Fin.elim0 = true) ↔
        input ∈ queryLanguage (fun A => Sentence.Models A φ) := by
  constructor
  · rintro ⟨⟨A, rfl⟩, h⟩
    rw [encodeStruct_card] at h
    exact mem_queryLanguage _ A ((sentence_evalCode_encodeStruct_internal A φ).mp h)
  · intro h
    obtain ⟨A, hdecode, hA⟩ := (mem_queryLanguage_iff_decodeStruct _ input).mp h
    obtain rfl := (decodeStruct_eq_some_iff input A).mp hdecode
    refine ⟨⟨A, rfl⟩, ?_⟩
    rw [encodeStruct_card]
    exact (sentence_evalCode_encodeStruct_internal A φ).mpr hA

theorem sentence_queryLanguage_fpPred_internal {V : Vocabulary} (φ : Sentence V) :
    FPPred fun input => input ∈ queryLanguage (fun A => Sentence.Models A φ) := by
  have heval := formula_evalCode_fpPred_internal φ id
    (fun input => (input.takeWhile id).length) (fun _ => Fin.elim0)
    id_mem_FP encodedCard_unary (fun i => Fin.elim0 i)
  exact ((encodable_fpPred V).and heval).of_iff (sentence_validatedCode_internal φ)

theorem formula_tableCode_encodeStruct_internal {V : Vocabulary} {n : Nat}
    (A : DecFinStruct V) (φ : Formula V n) :
    φ.tableCode A.card (encodeStruct A) = encodeRelC (fun σ => Formula.evalB A σ φ) := by
  have hcard : 0 < A.card := by have := A.hcard; omega
  rw [Formula.tableCode, ← map_allTuples_eq_range hcard]
  unfold encodeRelC
  apply List.map_congr_left
  intro σ _
  apply Bool.eq_iff_iff.mpr
  exact (formula_evalCode_encodeStruct_internal A φ σ).trans (Formula.evalB_eq_sat A φ σ).symm

theorem formula_tableCode_mem_FP_internal {V : Vocabulary} {n : Nat} (φ : Formula V n)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    (fun z => φ.tableCode (card z) (bits z)) ∈ FP := by
  have hbit := formula_evalCode_fpPred_internal φ (fun z => bits (pairFst z))
    (fun z => card (pairFst z))
    (fun z => tupleDigits (card (pairFst z)) n (pairSnd z).length)
    (mem_FP_comp pairFst_mem_FP hbits) hcard.lift
    (fun i => tupleDigits_unary hcard.lift UnaryFn.index n i)
  apply bitwise_mem_FP (hcard.pow_const n).mem_FP hbit.flag_mem_FP
  intro z i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Bool.decide_eq_true]

end Complexity.DescriptiveComplexity
