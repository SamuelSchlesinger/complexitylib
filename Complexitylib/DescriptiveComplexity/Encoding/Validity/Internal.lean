/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.Encoding.Validity.Defs
public import Complexitylib.DescriptiveComplexity.Encoding.PolynomialTime
public import Complexitylib.DescriptiveComplexity.Encoding.Decoding
import Complexitylib.Classes.P

/-!
# Correctness and polynomial time of encoding validation

Construct a structure from unrestricted relation bits and one-hot constant
blocks. The arithmetic-access theorems recover the original string. Bounded
quantifiers over polynomial-time bit reads implement every validation condition.
-/

public section

namespace Complexity.DescriptiveComplexity

theorem isValidEncoding_encodeStruct_internal {V : Vocabulary} (A : DecFinStruct V) :
    IsValidEncoding V A.card (encodeStruct A) := by
  refine ⟨A.hcard, encodeStruct_length_eq A, ?_, ?_⟩
  · intro i hi
    rw [getElem?_encodeStruct_header A ⟨i, hi⟩]
    rfl
  · intro c
    refine ⟨(A.const c).val, (A.const c).isLt, fun b hb => ?_⟩
    rw [getElem?_encodeStruct_constant A c ⟨b, hb⟩]
    simp only [Option.getD_some, Fin.ext_iff]

theorem isValidEncoding_iff_internal (V : Vocabulary) (card : Nat) (bits : List Bool) :
    IsValidEncoding V card bits ↔
      ∃ A : DecFinStruct V, A.card = card ∧ encodeStruct A = bits := by
  classical
  constructor
  · rintro ⟨hcard, hlen, hheader, hconst⟩
    choose values hvalues hblocks using hconst
    let A : DecFinStruct V :=
      ⟨card, hcard,
        (fun r args => bits[relationAddress V card r (fun i => (args i).val)]?.getD false),
        fun c => ⟨values c, hvalues c⟩⟩
    have hget (i : Nat) (hi : i < bits.length) :
        bits[i]? = some (bits[i]?.getD false) := by
      rw [List.getElem?_eq_getElem hi]
      rfl
    refine ⟨A, rfl, encodeStruct_eq_of_values A bits hlen ?_ ?_⟩
    · intro i
      have hi : i.val < bits.length := by
        rw [hlen]
        exact lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt (card_lt_encodingLength V card))
      exact (hget i.val hi).trans (congrArg some (hheader i.val i.isLt))
    · rintro (⟨r, args⟩ | ⟨c, a⟩)
      · rw [hget _ (hlen ▸ encodingPosition_lt V card (.inl ⟨r, args⟩)),
          encodingPosition_relation]
        rfl
      · rw [hget _ (hlen ▸ encodingPosition_lt V card (.inr (c, a))),
          encodingPosition_constant, hblocks c a.val a.isLt]
        simp only [inputSiteValue, A, Fin.ext_iff]
  · rintro ⟨A, rfl, rfl⟩
    exact isValidEncoding_encodeStruct_internal A

private theorem fpPred_iff {p q : List Bool → Prop} (hp : FPPred p) (hq : FPPred q) :
    FPPred fun z => p z ↔ q z :=
  ((hp.not.or hq).and (hq.not.or hp)).of_iff fun _ => by tauto

private theorem fpPred_forall_fin {m : Nat} {p : Fin m → List Bool → Prop}
    (hp : ∀ i, FPPred (p i)) : FPPred fun z => ∀ i, p i z := by
  induction m with
  | zero => exact (FPPred.const True).of_iff fun _ => by simp
  | succ m ih =>
    exact ((hp 0).and (ih fun i => hp i.succ)).of_iff fun z =>
      (Fin.forall_fin_succ (P := fun i => p i z)).symm

private theorem header_fpPred {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    FPPred fun z => ∀ i < card z + 1, (bits z)[i]?.getD false = decide (i < card z) := by
  have hbit := FPPred.getBit (mem_FP_comp pairFst_mem_FP hbits) UnaryFn.index
  have htest := fpPred_iff hbit (FPPred.lt UnaryFn.index hcard.lift)
  refine (FPPred.forall_lt (hcard.add (UnaryFn.const 1)) htest).of_iff fun z => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  exact forall_congr' fun i => forall_congr' fun _ =>
    (Bool.eq_iff_iff.trans (by simp)).symm

private theorem constantBlock_fpPred (V : Vocabulary) (c : Fin V.numConsts)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    FPPred fun z => ∃ a < card z, ∀ b < card z,
      (bits z)[constantAddress V (card z) c b]?.getD false = decide (a = b) := by
  have hbits2 := mem_FP_comp pairFst_mem_FP
    (mem_FP_comp pairFst_mem_FP hbits)
  have hbit := constantBit_fpPred V c hbits2 hcard.lift.lift UnaryFn.index
  have heq := FPPred.eq UnaryFn.index.lift UnaryFn.index
  have htest := fpPred_iff hbit heq
  have hall := FPPred.forall_lt hcard.lift htest
  refine (FPPred.exists_lt hcard hall).of_iff fun z => ?_
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  exact exists_congr fun a => and_congr Iff.rfl (forall_congr' fun b =>
    forall_congr' fun _ => (Bool.eq_iff_iff.trans (by simp)).symm)

theorem isValidEncoding_fpPred_internal (V : Vocabulary)
    {bits : List Bool → List Bool} {card : List Bool → Nat}
    (hbits : bits ∈ FP) (hcard : UnaryFn card) :
    FPPred fun z => IsValidEncoding V (card z) (bits z) :=
  (FPPred.le (UnaryFn.const 2) hcard).and
    ((FPPred.eq (UnaryFn.length hbits) (encodingLength_unary V hcard)).and
      ((header_fpPred hbits hcard).and
        (fpPred_forall_fin fun c => constantBlock_fpPred V c hbits hcard)))

end Complexity.DescriptiveComplexity
