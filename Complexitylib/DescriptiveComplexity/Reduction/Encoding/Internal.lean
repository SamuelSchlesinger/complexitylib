/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Reduction.Encoding.Defs
public import Complexitylib.DescriptiveComplexity.ModelChecking.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Validity
import Complexitylib.Classes.P
import Complexitylib.Classes.P.Bridge
import Complexitylib.Classes.P.Cobham.Internal

/-!
# Correctness and polynomial time of encoded interpretations

Generate each defining formula's truth table in the canonical tuple order and
copy each designated constant's one-hot block. The resulting string is exactly
the encoding of the interpreted structure. Polynomial-time validation guards
this table generator and maps every malformed input to the empty string.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem applyDec_toFinStruct_internal {V W : Vocabulary} (I : FOInterpretation V W)
    (A : DecFinStruct V) : (I.applyDec A).toFinStruct = I.apply A.toFinStruct := by
  have hrel : (I.applyDec A).toFinStruct.rel = (I.apply A.toFinStruct).rel := by
    funext r args
    exact propext (Formula.evalB_eq_sat A (I.relFormula r) args)
  rw [show (I.applyDec A).toFinStruct =
    { I.apply A.toFinStruct with rel := (I.applyDec A).toFinStruct.rel } from rfl, hrel]

private theorem constant_block_eq {V : Vocabulary} (A : DecFinStruct V)
    (c : Fin V.numConsts) :
    (List.range A.card).map (fun a =>
      (encodeStruct A)[constantAddress V A.card c a]?.getD false) = encodeConstC (A.const c) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hi' : i < A.card := by simpa using hi
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem?_encodeStruct_constant A c ⟨i, hi'⟩]
  simp [encodeConstC, beq_eq_decide, Fin.ext_iff, eq_comm]

theorem rawEncoding_encodeStruct_internal {V W : Vocabulary} (I : FOInterpretation V W)
    (A : DecFinStruct V) : I.rawEncoding A.card (encodeStruct A) = encodeStruct (I.applyDec A) := by
  simp only [FOInterpretation.rawEncoding, Formula.tableCode_encodeStruct, constant_block_eq]
  rfl

theorem rawEncoding_length_internal {V W : Vocabulary} (I : FOInterpretation V W)
    (card : Nat) (input : List Bool) :
    (I.rawEncoding card input).length = encodingLength W card := by
  simp [FOInterpretation.rawEncoding, encodingLength, List.length_flatMap, Nat.add_assoc]
  omega

private theorem flatMap_fixed_mem_FP {α : Type} (indices : List α)
    (f : α → List Bool → List Bool) (hf : ∀ i, f i ∈ FP) :
    (fun z => indices.flatMap (fun i => f i z)) ∈ FP := by
  induction indices with
  | nil => exact constFn_mem_FP []
  | cons i indices ih => exact Cobham.appendFn_mem_FP (hf i) ih

theorem rawEncoding_mem_FP_internal {V W : Vocabulary} (I : FOInterpretation V W)
    {input : List Bool → List Bool} {card : List Bool → Nat}
    (hinput : input ∈ FP) (hcard : UnaryFn card) :
    (fun z => I.rawEncoding (card z) (input z)) ∈ FP := by
  have hrels := flatMap_fixed_mem_FP (List.finRange W.numRels)
    (fun r z => (I.relFormula r).tableCode (card z) (input z))
    (fun r => (I.relFormula r).tableCode_mem_FP hinput hcard)
  have hconst : ∀ c : Fin W.numConsts,
      (fun z => (List.range (card z)).map fun a =>
        (input z)[constantAddress V (card z) (I.constMap c) a]?.getD false) ∈ FP := by
    intro c
    have hbit := constantBit_fpPred V (I.constMap c)
      (mem_FP_comp pairFst_mem_FP hinput) hcard.lift UnaryFn.index
    apply bitwise_mem_FP hcard.mem_FP hbit.flag_mem_FP
    intro z i
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
      Bool.decide_eq_true]
  have hconsts := flatMap_fixed_mem_FP (List.finRange W.numConsts) _ hconst
  exact Cobham.appendFn_mem_FP hcard.mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) (Cobham.appendFn_mem_FP hrels hconsts))

theorem mapEncoding_mem_FP_internal {V W : Vocabulary} (I : FOInterpretation V W) :
    I.mapEncoding ∈ FP := by
  classical
  have hraw := rawEncoding_mem_FP_internal I id_mem_FP encodedCard_unary
  have hif := (encodable_fpPred V).ite_mem_FP hraw (constFn_mem_FP [])
  refine mem_FP_of_eq hif fun input => ?_
  cases hd : decodeStruct V input with
  | none =>
    have hn := (decodeStruct_eq_none_iff input).mp hd
    simp [FOInterpretation.mapEncoding, hd, hn]
  | some A =>
    have henc := (decodeStruct_eq_some_iff input A).mp hd
    have hvalid : ∃ B : DecFinStruct V, encodeStruct B = input := ⟨A, henc⟩
    simp only [hvalid, ite_true, FOInterpretation.mapEncoding, hd]
    rw [← henc, encodeStruct_card]
    exact rawEncoding_encodeStruct_internal I A

theorem mapEncoding_mem_queryLanguage_iff_internal {V W : Vocabulary}
    (I : FOInterpretation V W) (Q : BooleanQuery W) (input : List Bool) :
    I.mapEncoding input ∈ queryLanguage Q ↔
      input ∈ queryLanguage (fun A => Q (I.apply A)) := by
  cases hd : decodeStruct V input with
  | none => simp [FOInterpretation.mapEncoding, hd, mem_queryLanguage_iff_decodeStruct]
  | some A =>
    simp only [FOInterpretation.mapEncoding, mem_queryLanguage_iff_decodeStruct,
      hd, decodeStruct_encodeStruct, Option.some.injEq, exists_eq_left',
      applyDec_toFinStruct_internal]

end Complexity.DescriptiveComplexity
