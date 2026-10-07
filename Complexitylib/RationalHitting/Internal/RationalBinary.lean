/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.SignedBinary

/-!
# Rational hitting lists: rational binary

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/RationalBinary.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

lemma eval_copy9 (s : Store (Fin 12)) (a b : Fin 12)
    (hab : a≠b) (ha : a≠9) (hb : b≠9) (h9 : s 9=[]) :
    Eval (copy a b 9) s (update s b (s a)) (7*(s a).length+2*(s b).length+7) := by
  have hh := eval_copy hab ha hb s
  have he : update (update s b (s a)) 9 []=update s b (s a) := by
    funext k; by_cases hk : k=9 <;> simp_all [Ne.symm hb]
  rw [he] at hh
  simpa [h9] using hh

/-- Euclid followed by two binary divisions, destructively producing the
coprime numerator and positive denominator magnitudes. -/
def fractionReduce : Program (Fin 12) :=
  .seq (copy 0 10 9) (.seq (copy 5 11 9) (.seq (gcdLoop.rename fractionArith)
    (.seq (copy 0 5 9) (.seq (copy 10 0 9) (.seq (quotient.rename fractionArith)
    (.seq (copy 0 10 9) (.seq (copy 11 0 9) (.seq (quotient.rename fractionArith)
    (.seq (copy 0 5 9) (.seq (copy 10 0 9) (.seq (clear 10) (clear 11))))))))))))

lemma eval_fractionReduce (s : Store (Fin 12)) (hs : FractionScratch s)
    (h10 : s 10=[]) (h11 : s 11=[])
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 3000*(B+1)^3,
      Eval fractionReduce s
        (update (update s 0 (wordValue (s 0)/Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits)
          5 (wordValue (s 5)/Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) t := by
  let A := wordValue (s 0)
  let D := wordValue (s 5)
  let g := Nat.gcd A D
  have hg : 0<g := Nat.gcd_pos_of_pos_right A hb
  have h9 : s 9=[] := hs 9 (by decide) (by decide)
  have hgl : g.bits.length≤B := by
    apply le_trans _ h5
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.le_of_dvd hb (Nat.gcd_dvd_right A D)).trans_lt (wordValue_lt _)
  have hAl : (A/g).bits.length≤B := by
    apply le_trans _ h0; rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hDl : (D/g).bits.length≤B := by
    apply le_trans _ h5; rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  let u1 := update s 10 (s 0)
  let u2 := update u1 11 (s 5)
  let u3 := update (update u2 0 g.bits) 5 []
  let u4 := update u3 5 g.bits
  let u5 := update u4 0 (s 0)
  let u6 := update u5 0 (A/g).bits
  let u7 := update u6 10 (A/g).bits
  let u8 := update u7 0 (s 5)
  let u9 := update u8 0 (D/g).bits
  let u10 := update u9 5 (D/g).bits
  let u11 := update u10 0 (A/g).bits
  let u12 := update u11 10 []
  have e1 : Eval (copy 0 10 9) s u1 (7*(s 0).length+7) := by
    simpa [u1,h10] using eval_copy9 s 0 10 (by decide) (by decide) (by decide) h9
  have e2 : Eval (copy 5 11 9) u1 u2 (7*(s 5).length+7) := by
    simpa [u2,u1,h11] using eval_copy9 u1 5 11 (by decide) (by decide) (by decide) (by simp [u1,h9])
  have hs2 : FractionScratch u2 :=
    fractionScratch_update _ (fractionScratch_update _ hs 10 (by simp) _) 11 (by simp) _
  obtain ⟨t3,ht3,e3⟩ := eval_fractionGcd u2 hs2 (by simpa [u2,u1] using hcan0)
    (by simpa [u2,u1] using hcan5) B (by simpa [u2,u1] using h0) (by simpa [u2,u1] using h5)
  change Eval (gcdLoop.rename fractionArith) u2 u3 t3 at e3
  have e4 : Eval (copy 0 5 9) u3 u4 (7*g.bits.length+7) := by
    simpa [u4,u3,u2,u1] using eval_copy9 u3 0 5 (by decide) (by decide) (by decide) (by simp
      [u3,u2,u1,h9])
  have e5 : Eval (copy 10 0 9) u4 u5 (7*(s 0).length+2*g.bits.length+7) := by
    simpa [u5,u4,u3,u2,u1] using eval_copy9 u4 10 0 (by decide) (by decide) (by decide)
      (by simp [u4,u3,u2,u1,h9])
  have hs5 : FractionScratch u5 := by
    apply fractionScratch_update _ (fractionScratch_update _
      (fractionScratch_update _ (fractionScratch_update _ hs2 0 (by simp) _) 5 (by simp) _)
      5 (by simp) _) 0 (by simp)
  obtain ⟨t6,ht6,e6⟩ := eval_fractionQuotient u5 hs5 (by simpa [u5,u4] using hg) B
    (by simpa [u5] using h0) (by simpa [u5,u4] using hgl)
  have ev6 : Eval (quotient.rename fractionArith) u5 u6 t6 := by
    simpa [u6,u5,u4,A] using e6
  have e7 : Eval (copy 0 10 9) u6 u7 (7*(A/g).bits.length+2*(s 0).length+7) := by
    simpa [u7,u6,u5,u4,u3,u2,u1] using eval_copy9 u6 0 10 (by decide) (by decide) (by decide)
      (by simp [u6,u5,u4,u3,u2,u1,h9])
  have e8 : Eval (copy 11 0 9) u7 u8 (7*(s 5).length+2*(A/g).bits.length+7) := by
    simpa [u8,u7,u6,u5,u4,u3,u2,u1] using eval_copy9 u7 11 0 (by decide) (by decide) (by decide)
      (by simp [u7,u6,u5,u4,u3,u2,u1,h9])
  have hs8 : FractionScratch u8 :=
    fractionScratch_update _ (fractionScratch_update _ (fractionScratch_update _ hs5
      0 (by simp) _) 10 (by simp) _) 0 (by simp) _
  obtain ⟨t9,ht9,e9⟩ := eval_fractionQuotient u8 hs8 (by simpa [u8,u7,u6,u5,u4] using hg) B
    (by simpa [u8] using h5) (by simpa [u8,u7,u6,u5,u4] using hgl)
  have ev9 : Eval (quotient.rename fractionArith) u8 u9 t9 := by
    simpa [u9,u8,u7,u6,u5,u4,D] using e9
  have e10 : Eval (copy 0 5 9) u9 u10 (7*(D/g).bits.length+2*g.bits.length+7) := by
    simpa [u10,u9,u8,u7,u6,u5,u4] using eval_copy9 u9 0 5 (by decide) (by decide) (by decide)
      (by simp [u9,u8,u7,u6,u5,u4,u3,u2,u1,h9])
  have e11 : Eval (copy 10 0 9) u10 u11 (7*(A/g).bits.length+2*(D/g).bits.length+7) := by
    simpa [u11,u10,u9,u8,u7] using eval_copy9 u10 10 0 (by decide) (by decide) (by decide)
      (by simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,h9])
  have e12 : Eval (clear 10) u11 u12 (2*(A/g).bits.length+1) := by
    simpa [u12,u11,u10,u9,u8,u7] using eval_clear (10 : Fin 12) u11
  have e13 := eval_clear (11 : Fin 12) u12
  have heq : update u12 11 [] = update (update s 0 (A/g).bits) 5 (D/g).bits := by
    funext k; fin_cases k <;> simp [u12,u11,u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,h10,h11]
  rw [heq] at e13
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq ev6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq ev9 (Eval.seq e10 (Eval.seq e11 (Eval.seq e12 e13)))))))))))
  refine ⟨_,?_,hh⟩
  simp only [show u12 11=s 5 by simp [u12,u11,u10,u9,u8,u7,u6,u5,u4,u3,u2,u1]]
  nlinarith [Nat.zero_le (B^3)]

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Consume a word, emitting its unary length, independently of its bits. -/
def unaryLength (a b : K) : Program K := .loop a (.seq (.drop a) (.push b true))

lemma eval_unaryLength {a b : K} (hab : a≠b) (s : Store K) :
    Eval (unaryLength a b) s
      (update (update s a []) b (List.replicate (s a).length true ++ s b))
      (4*(s a).length+1) := by
  generalize he : s a=w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b)=s := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all
    simpa [unaryLength,he,hh] using (Eval.whileNil (p:=Program.seq (.drop a) (.push b true)) he)
  | cons x w ih =>
    let u := update s a w
    let v := update u b (true::s b)
    have e1 : Eval (Program.drop a) s u 1 := by simpa [u,he] using Eval.drop a s
    have e2 : Eval (Program.push b true) u v 1 := by
      simpa [v,u,Ne.symm hab] using Eval.push b
        true u
    have e3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) (Eval.seq e1 e2) e3
    have heq : update (update v a []) b (List.replicate w.length true ++ v b) =
        update (update s a []) b (List.replicate (x::w).length true ++ s b) := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;>
        simp_all [v,u,List.replicate_add,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [unaryLength] ; omega

/-- Canonical output's self-delimiting natural-number encoding, applied to
an already canonical little-endian binary word. -/
def encodedWord (w : List Bool) : List Bool :=
  List.replicate w.length true ++ [false] ++ w

/-- Write a self-delimiting binary word with its unary length prefix. -/
def encodeWord : Program (Fin 4) :=
  .seq (duplicateReverse 0 2 3) (.seq (reverse 2 1)
    (.seq (.push 1 false) (unaryLength 3 1)))

lemma eval_encodeWord (s : Store (Fin 4)) (h2 : s 2=[]) (h3 : s 3=[]) :
    Eval encodeWord s (update (update s 0 []) 1 (encodedWord (s 0)++s 1))
      (11*(s 0).length+7) := by
  let u := update (update (update s 0 []) 2 (s 0).reverse) 3 (s 0).reverse
  let v := update (update u 2 []) 1 (s 0++s 1)
  let z := update v 1 (false::s 0++s 1)
  have e1 : Eval (duplicateReverse 0 2 3) s u (5*(s 0).length+1) := by
    simpa [u,h2,h3] using eval_duplicateReverse (a:=0) (b:=2) (c:=3)
      (by decide) (by decide) (by decide) s
  have e2 : Eval (reverse 2 1) u v (2*(s 0).length+1) := by
    simpa [v,u] using eval_reverse (a:=2) (b:=1) (by decide) u
  have e3 : Eval (Program.push 1 false) v z 1 := by
    simpa [z,v,u] using Eval.push (1 : Fin 4) false v
  have e4 := eval_unaryLength (a:=3) (b:=1) (by decide) z
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  have heq : update (update z 3 []) 1 (List.replicate (z 3).length true ++ z 1) =
      update (update s 0 []) 1 (encodedWord (s 0)++s 1) := by
    funext k; fin_cases k <;> simp [z,v,u,h2,h3,encodedWord,List.append_assoc]
  rw [heq] at hh
  convert hh using 1 <;> simp [encodeWord,z,v,u] ; omega

lemma digits_bool_bits (a : ℕ) :
    (Nat.digits 2 a).map (fun b => b != 0)=a.bits := by
  rw [Nat.digits_two_eq_bits,List.map_map]
  convert List.map_id a.bits using 1
  congr 1
  funext b; cases b <;> rfl

end RationalHitting.StackLanguage

namespace RationalHitting.RationalCanonical

lemma divInt_num_abs (a b : ℤ) (hb : b≠0) :
    (Rat.divInt a b).num.natAbs = a.natAbs/Nat.gcd a.natAbs b.natAbs := by
  rw [Rat.num_divInt,Int.natAbs_ediv_of_dvd (dvd_mul_of_dvd_right (Int.gcd_dvd_right b a) b.sign),
    Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hb,Int.natAbs_natCast,one_mul]
  simp only [Int.gcd, Nat.gcd_comm]

lemma divInt_den (a b : ℤ) (hb : b≠0) :
    (Rat.divInt a b).den = b.natAbs/Nat.gcd a.natAbs b.natAbs := by
  simp [Rat.den_divInt,hb,Int.gcd,Nat.gcd_comm]

/-- The sign used by the canonical binary rational encoder. -/
lemma divInt_sign (a b : ℤ) (hb : b≠0) :
    decide ((Rat.divInt a b).num<0) =
      if a=0 then false else (decide (a<0) ^^ decide (b<0)) := by
  have hs : (Rat.divInt a b).num<0 ↔ (a:ℚ)/(b:ℚ)<0 := by
    rw [←Rat.num_neg, Rat.divInt_eq_div]
  simp only [hs]
  by_cases ha : a=0
  · simp [ha]
  · rw [ite_eq_right ha]
    rcases lt_or_gt_of_ne ha with hna|hpa <;> rcases lt_or_gt_of_ne hb with hnb|hpb
    · have hp : (0:ℚ)<(a:ℚ)/(b:ℚ) := div_pos_of_neg_of_neg (by exact_mod_cast hna) (by
      exact_mod_cast hnb)
      simp [hna,hnb,not_lt_of_ge hp.le]
    · have hn : (a:ℚ)/(b:ℚ)<0 := div_neg_of_neg_of_pos (by exact_mod_cast hna) (by
      exact_mod_cast hpb)
      simp [hna,not_lt_of_gt hpb,hn]
    · have hn : (a:ℚ)/(b:ℚ)<0 := div_neg_of_pos_of_neg (by exact_mod_cast hpa) (by
      exact_mod_cast hnb)
      simp [not_lt_of_gt hpa,hnb,hn]
    · have hp : (0:ℚ)<(a:ℚ)/(b:ℚ) := div_pos (by exact_mod_cast hpa) (by exact_mod_cast hpb)
      simp [not_lt_of_gt hpa,not_lt_of_gt hpb,not_lt_of_ge hp.le]

end RationalHitting.RationalCanonical

namespace RationalHitting
namespace StackLanguage
open Function

lemma encodedWord_bits (a : ℕ) : encodedWord a.bits=encodeNat a := by
  simp [encodeNat,digits_bool_bits,encodedWord]

lemma eval_encodeWord_rename {K : Type} [DecidableEq K] (f : Fin 4 → K)
    (hf : Injective f) (s : Store K) (h2 : s (f 2)=[]) (h3 : s (f 3)=[]) :
    Eval (encodeWord.rename f) s
      (update (update s (f 0) []) (f 1) (encodedWord (s (f 0))++s (f 1)))
      (11*(s (f 0)).length+7) := by
  have h := eval_rename_from f hf s (eval_encodeWord (fun k => s (f k)) h2 h3)
  simpa only [extend_update_store f hf,extend_pull_store f hf] using h

lemma eval_fractionReduce_rename {K : Type} [DecidableEq K] (f : Fin 12 → K)
    (hf : Injective f) (s : Store K) (hs : FractionScratch (fun k => s (f k)))
    (h10 : s (f 10)=[]) (h11 : s (f 11)=[]) (A D B : ℕ)
    (h0 : s (f 0)=A.bits) (h5 : s (f 5)=D.bits) (hD : 0<D)
    (ha : A.bits.length≤B) (hd : D.bits.length≤B) :
    ∃ t ≤ 3000*(B+1)^3, Eval (fractionReduce.rename f) s
      (update (update s (f 0) (A/Nat.gcd A D).bits) (f 5) (D/Nat.gcd A D).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_fractionReduce (fun k => s (f k)) hs h10 h11
    (by simp [h0]) (by simp [h5]) (by simpa [h5] using hD) B
    (by simpa [h0] using ha) (by simpa [h5] using hd)
  refine ⟨t,ht,?_⟩
  have h := eval_rename_from f hf s he
  simpa only [extend_update_store f hf,extend_pull_store f hf,h0,h5,wordValue_bits] using h

/-- Registers 12 and 13 hold signed-magnitude signs; 15 stores the canonical
result's sign and remains disjoint from the twelve arithmetic registers. -/
def fractionSign : Program (Fin 16) :=
  .branch 0 (.push 15 false)
    (readBit 12 (fun a => readBit 13 (fun b => .push 15 (a ^^ b))))
    (readBit 12 (fun a => readBit 13 (fun b => .push 15 (a ^^ b))))

lemma eval_fractionSign (s : Store (Fin 16)) (a b : Bool) (h12 : s 12=[a]) (h13 : s 13=[b]) :
    ∃ t ≤ 4, Eval fractionSign s
      (update s 15 ((if s 0=[] then false else a ^^ b)::s 15)) t := by
  cases h0 : s 0 with
  | nil =>
    refine ⟨2,by omega,?_⟩
    simpa [fractionSign,h0] using (Eval.branchNone h0 (Eval.push (15 : Fin 16) false s))
  | cons c w =>
    have hr : Eval (readBit 12 (fun a => readBit 13 (fun b => Program.push 15 (a ^^ b)))) s
        (update s 15 ((a ^^ b)::s 15)) 3 := by
      apply eval_readBit 12 _ s _ 2
      simp only [h12,List.headD_cons]
      apply eval_readBit 13 _ s _ 1
      simpa [h13] using Eval.push (15 : Fin 16) (a ^^ b) s
    cases c with
    | false => exact ⟨4,by omega,by simpa [fractionSign,h0] using Eval.branchFalse h0 hr⟩
    | true => exact ⟨4,by omega,by simpa [fractionSign,h0] using Eval.branchTrue h0 hr⟩

/-- Embed fraction-reduction registers into the rational-encoding program. -/
def reduceReg (i : Fin 12) : Fin 16 := ⟨i.val,by omega⟩
lemma reduceReg_inj : Injective reduceReg := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 16 => x.val) h

/-- Registers used when emitting the canonical denominator. -/
def denominatorReg : Fin 4 → Fin 16 := ![5,14,1,2]
/-- Registers used when emitting the canonical numerator magnitude. -/
def numeratorReg : Fin 4 → Fin 16 := ![0,14,1,2]
lemma denominatorReg_inj : Injective denominatorReg := by decide
lemma numeratorReg_inj : Injective numeratorReg := by decide

/-- Full signed canonical rational output. No gcd, comparison or sign oracle
occurs in this fixed finite binary-stack program. -/
def rationalEncode : Program (Fin 16) :=
  .seq fractionSign (.seq (fractionReduce.rename reduceReg)
    (.seq (encodeWord.rename denominatorReg)
      (.seq (encodeWord.rename numeratorReg) (.transfer 15 14))))

end StackLanguage
end RationalHitting

namespace RationalHitting.StackLanguage
open Function

/-- Exact final canonical binary fraction, with a cubic bit-time stack implementation.
This supplies the output-format obligation of the uniform list generator. -/
theorem eval_rationalEncode (s : Store (Fin 16)) (a b : ℤ) (hb : b≠0)
    (h0 : s 0=a.natAbs.bits) (h5 : s 5=b.natAbs.bits)
    (h12 : s 12=[decide (a<0)]) (h13 : s 13=[decide (b<0)]) (h15 : s 15=[])
    (hs : ∀ i : Fin 16, i.val<12 → i≠0 → i≠5 → s i=[])
    (B : ℕ) (ha : a.natAbs.bits.length≤B) (hd : b.natAbs.bits.length≤B) :
    ∃ t ≤ 3100*(B+1)^3, Eval rationalEncode s
      (update (update (update s 0 []) 5 []) 14 (encodeRat (Rat.divInt a b)++s 14)) t := by
  let g := Nat.gcd a.natAbs b.natAbs
  let A := a.natAbs/g
  let D := b.natAbs/g
  let sign := decide ((Rat.divInt a b).num<0)
  have hsg : (if s 0=[] then false else decide (a<0) ^^ decide (b<0))=sign := by
    have hz : a.natAbs.bits=[] ↔ a=0 := by
      constructor
      · intro he
        have hy := congrArg wordValue he
        simpa using hy
      · intro he; simp [he]
    simp only [h0,hz]
    exact (RationalCanonical.divInt_sign a b hb).symm
  have hA : A.bits.length≤B := by
    apply le_trans _ ha
    rw [Nat.size_eq_bits_len,Nat.size_le]
    have he := wordValue_lt a.natAbs.bits
    simp only [wordValue_bits] at he
    exact (Nat.div_le_self _ _).trans_lt he
  have hD : D.bits.length≤B := by
    apply le_trans _ hd
    rw [Nat.size_eq_bits_len,Nat.size_le]
    have he := wordValue_lt b.natAbs.bits
    simp only [wordValue_bits] at he
    exact (Nat.div_le_self _ _).trans_lt he
  let u1 := update s 15 [sign]
  let u2 := update (update u1 0 A.bits) 5 D.bits
  let u3 := update (update u2 5 []) 14 (encodedWord D.bits++s 14)
  let u4 := update (update u3 0 []) 14 (encodedWord A.bits++encodedWord D.bits++s 14)
  obtain ⟨t1,ht1,e1⟩ := eval_fractionSign s (decide (a<0)) (decide (b<0)) h12 h13
  have ev1 : Eval fractionSign s u1 t1 := by simpa [u1,hsg,h15] using e1
  have hs1 : FractionScratch (fun k => u1 (reduceReg k)) := by
    intro k hk0 hk5
    have hv : (reduceReg (fractionArith k)).val<12 := by
      dsimp [reduceReg, fractionArith]
      lia
    have hn : reduceReg (fractionArith k) ≠ (15 : Fin 16) := by
      intro hh; have hh' := congrArg (fun x : Fin 16 => x.val) hh; change k.val=15 at hh'; omega
    have hn0 : reduceReg (fractionArith k) ≠ (0 : Fin 16) := by
      intro hh; apply hk0; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) hh
    have hn5 : reduceReg (fractionArith k) ≠ (5 : Fin 16) := by
      intro hh; apply hk5; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) hh
    simpa [u1,hn] using hs _ hv hn0 hn5
  obtain ⟨t2,ht2,e2⟩ := eval_fractionReduce_rename reduceReg reduceReg_inj u1 hs1
    (by simpa [u1,reduceReg] using hs 10 (by decide) (by decide) (by decide))
    (by simpa [u1,reduceReg] using hs 11 (by decide) (by decide) (by decide))
    a.natAbs b.natAbs B (by simpa [u1,reduceReg] using h0)
    (by simpa [u1,reduceReg] using h5) (Int.natAbs_pos.mpr hb) ha hd
  have ev2 : Eval (fractionReduce.rename reduceReg) u1 u2 t2 := e2
  have h1 : s 1=[] := hs 1 (by decide) (by decide) (by decide)
  have h2 : s 2=[] := hs 2 (by decide) (by decide) (by decide)
  have ev3 : Eval (encodeWord.rename denominatorReg) u2 u3 (11*D.bits.length+7) := by
    simpa [denominatorReg,u3,u2,u1] using
      eval_encodeWord_rename denominatorReg denominatorReg_inj u2
        (by simp [denominatorReg,u2,u1,h1]) (by simp [denominatorReg,u2,u1,h2])
  have ev4 : Eval (encodeWord.rename numeratorReg) u3 u4 (11*A.bits.length+7) := by
    simpa [numeratorReg,u4,u3,u2,u1,List.append_assoc] using
      eval_encodeWord_rename numeratorReg numeratorReg_inj u3
        (by simp [numeratorReg,u3,u2,u1,h1]) (by simp [numeratorReg,u3,u2,u1,h2])
  have ev5 := Eval.transfer (15 : Fin 16) 14 u4
  have hh := Eval.seq ev1 (Eval.seq ev2 (Eval.seq ev3 (Eval.seq ev4 ev5)))
  have heq : transfer 15 14 u4 =
      update (update (update s 0 []) 5 []) 14 (encodeRat (Rat.divInt a b)++s 14) := by
    rw [transfer_cons (by decide) u4 sign [] (by simp [u4,u3,u2,u1])]
    funext k
    by_cases hk0 : k=0 <;> by_cases hk5 : k=5 <;> by_cases hk14 : k=14 <;> by_cases hk15 : k=15 <;>
      simp_all [u4,u3,u2,u1,encodeRat,encodedWord_bits,
        RationalCanonical.divInt_num_abs a b hb,RationalCanonical.divInt_den a b hb,A,D,g,sign,
        List.append_assoc]
  refine ⟨1+t1+(1+t2+(1+(11*D.bits.length+7)+(1+(11*A.bits.length+7)+1))),?_,?_⟩
  · nlinarith only [ht1,ht2,hA,hD,Nat.zero_le (B^2),Nat.zero_le (B^3)]
  · simpa only [rationalEncode,heq] using hh

end RationalHitting.StackLanguage

end Complexity
