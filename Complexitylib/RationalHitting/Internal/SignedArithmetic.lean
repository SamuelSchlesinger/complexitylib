/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.ListProcedures

/-!
# Rational hitting lists: signed arithmetic

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/SignedArithmetic.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Encode an integer by its sign bit and binary magnitude. -/
def intCode (z : ℤ) : List Bool := pairCode boolCode Nat.bits (decide (z<0),z.natAbs)
instance : Coding ℤ := ⟨intCode⟩
@[simp] lemma intCode_length (z : ℤ) : (intCode z).length=z.natAbs.bits.length+3 := by
  simp [intCode];omega

lemma nat_bits_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length :=
  by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

lemma difference_bits_length (a b : ℕ) :
    ((a:ℤ)-(b:ℤ)).natAbs.bits.length≤a.bits.length+b.bits.length := by
  have h := Int.natAbs_sub_le (a:ℤ) (b:ℤ)
  simp only [Int.natAbs_natCast] at h
  exact (nat_bits_mono h).trans (add_bits_length a b)

/-- Compute the magnitude of the signed difference of two binary natural inputs. -/
def differenceAbs : Program (Fin 5) := .seq signedDifference (clear 3)
/-- Compute the sign of the difference of two binary natural inputs. -/
def differenceSign : Program (Fin 5) := .seq signedDifference (clear 0)

lemma eval_difference_base (a b : ℕ) : ∃ t≤100*(a.bits.length+b.bits.length+1),
    Eval signedDifference (both (0 : Fin 5) 1 a.bits b.bits)
      (both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)]) t := by
  obtain ⟨t,ht,he⟩ := eval_signedDifference (both (0 : Fin 5) 1 a.bits b.bits)
    (by simp [both,single]) (by simp [both,single]) (by simp [both,single])
  have hx : update (update (update (both (0 : Fin 5) 1 a.bits b.bits)
       0 (((a:ℤ)-(b:ℤ)).natAbs).bits) 1 []) 3 [decide (a<b)]=
       both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)] := by
    funext k; fin_cases k <;> simp [both,single]
  simp only [both_first (by decide : (0 : Fin 5)≠1),both_second,wordValue_bits,hx] at ht he
  exact ⟨t,ht,he⟩

lemma eval_differenceAbs (a b : ℕ) : ∃ t≤200*(a.bits.length+b.bits.length+1),
    Eval differenceAbs (both (0 : Fin 5) 1 a.bits b.bits)
      (single 0 (((a:ℤ)-(b:ℤ)).natAbs).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_difference_base a b
  have hc : Eval (clear (3 : Fin 5))
      (both 0 3 (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)])
      (single 0 (((a:ℤ)-(b:ℤ)).natAbs).bits) 3 := by
    rw [both_comm (by decide : (0 : Fin 5)≠3)]
    exact eval_clear_both (by decide) _ _
  exact ⟨1+t+3,by omega,Eval.seq he hc⟩

lemma eval_differenceSign (a b : ℕ) : ∃ t≤200*(a.bits.length+b.bits.length+1),
    Eval differenceSign (both (0 : Fin 5) 1 a.bits b.bits)
      (single 3 [decide (a<b)]) t := by
  obtain ⟨t,ht,he⟩ := eval_difference_base a b
  have hc := eval_clear_both (by decide : (0 : Fin 5)≠3)
    (((a:ℤ)-(b:ℤ)).natAbs).bits [decide (a<b)]
  have hl := difference_bits_length a b
  exact ⟨1+t+(2*(((a:ℤ)-(b:ℤ)).natAbs).bits.length+1),by omega,Eval.seq he hc⟩

namespace Procedure

/-- Compute the magnitude of the signed difference of two binary natural inputs. -/
def differenceAbs : Procedure (pairCode Nat.bits Nat.bits) Nat.bits
    (fun a => ((a.1:ℤ)-(a.2:ℤ)).natAbs) :=
  fromBinary StackLanguage.differenceAbs 0 1 0 (by decide) (200*TimeBound.variable)
    (by intro a b; simpa using eval_differenceAbs a b)
    (by intro a b; have h := difference_bits_length a b; simp;omega)

/-- Compute the sign of the difference of two binary natural inputs. -/
def differenceSign : Procedure (pairCode Nat.bits Nat.bits) boolCode
    (fun a => decide (a.1<a.2)) :=
  fromBinary StackLanguage.differenceSign 0 1 3 (by decide) (200*TimeBound.variable)
    (by intro a b; simpa [boolCode] using eval_differenceSign a b) (by intro a b;simp;omega)

end Procedure
namespace Poly

@[fun_prop] theorem natDifferenceAbs : Poly (fun a : ℕ×ℕ => ((a.1:ℤ)-(a.2:ℤ)).natAbs) :=
  ⟨Procedure.differenceAbs⟩
@[fun_prop] theorem natLt : Poly (fun a : ℕ×ℕ => decide (a.1<a.2)) := ⟨Procedure.differenceSign⟩

@[fun_prop] theorem natDifference : Poly (fun a : ℕ×ℕ => (a.1:ℤ)-(a.2:ℤ)) := by
  have h := Feasible.pair natLt natDifferenceAbs
  refine h.recode _ _ _ (fun x => x) (by intro a;rfl) ?_
  intro a
  change pairCode boolCode Nat.bits (decide (a.1<a.2),_) = intCode _
  have hsign : decide (a.1<a.2)=decide ((a.1:ℤ)-(a.2:ℤ)<0) := by
    simp only [sub_neg, Int.ofNat_lt]
  simp only [intCode,hsign]

@[fun_prop] theorem intSign : Poly (fun a : ℤ => decide (a<0)) :=
  (Feasible.fst boolCode Nat.bits).recode _ _ _ (fun a : ℤ => (decide (a<0),a.natAbs))
    (by intro a;rfl) (by intro a;rfl)
@[fun_prop] theorem intAbs : Poly (Int.natAbs : ℤ → ℕ) :=
  (Feasible.snd boolCode Nat.bits).recode _ _ _ (fun a : ℤ => (decide (a<0),a.natAbs))
    (by intro a;rfl) (by intro a;rfl)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

/-- The nonnegative part of an integer, represented as a natural number. -/
def positivePart (z : ℤ) : ℕ := if decide (z<0) then 0 else z.natAbs
/-- The magnitude of the negative part of an integer. -/
def negativePart (z : ℤ) : ℕ := if decide (z<0) then z.natAbs else 0

lemma int_decompose (z : ℤ) : (positivePart z : ℤ)-(negativePart z : ℤ)=z := by
  by_cases h : z<0
  · simp [positivePart,negativePart,h,abs_of_neg h]
  · simp [positivePart,negativePart,h,abs_of_nonneg (by omega : 0≤z)]

namespace Poly

@[fun_prop] theorem positivePart_poly : Poly StackLanguage.positivePart := by
  unfold StackLanguage.positivePart
  fun_prop
@[fun_prop] theorem negativePart_poly : Poly StackLanguage.negativePart := by
  unfold StackLanguage.negativePart
  fun_prop

@[fun_prop] theorem natCastInt : Poly (fun a : ℕ => (a : ℤ)) := by
  have h := natDifference.comp (show Poly (fun a : ℕ => (a,0)) by fun_prop)
  exact h.of_eq (by intro a;simp)
@[fun_prop] theorem intNeg : Poly (fun a : ℤ => -a) := by
  have h := natDifference.comp (show Poly (fun a : ℤ => (negativePart a,positivePart a)) by
    fun_prop)
  exact h.of_eq (by intro a; have hh := int_decompose a;omega)
@[fun_prop] theorem intAdd : Poly (fun a : ℤ×ℤ => a.1+a.2) := by
  have h := natDifference.comp (show Poly (fun a : ℤ×ℤ =>
      (positivePart a.1+positivePart a.2,negativePart a.1+negativePart a.2)) by fun_prop)
  refine h.of_eq ?_
  intro a
  push_cast
  have h1 := int_decompose a.1
  have h2 := int_decompose a.2
  omega
@[fun_prop] theorem intMul : Poly (fun a : ℤ×ℤ => a.1*a.2) := by
  have h := natDifference.comp (show Poly (fun a : ℤ×ℤ =>
      (positivePart a.1*positivePart a.2+negativePart a.1*negativePart a.2,
      positivePart a.1*negativePart a.2+negativePart a.1*positivePart a.2)) by fun_prop)
  refine h.of_eq ?_
  intro a
  push_cast
  conv_rhs => rw [← int_decompose a.1,← int_decompose a.2]
  ring

@[fun_prop] theorem natZero : Poly (fun a : ℕ => decide (a=0)) := by
  refine (show Feasible (fun x => x) boolCode _ from ⟨Procedure.wordEmpty⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) ?_
  intro a
  change boolCode a.bits.isEmpty = boolCode (decide (a=0))
  by_cases h : a=0
  · simp [h]
  · have hh : a.bits≠[] := by
      intro e
      have he := congrArg wordValue e
      simp only [wordValue_bits,wordValue] at he
      exact h he
    cases he : a.bits with
    | nil => exact (hh he).elim
    | cons b w => simp [show a≠0 from h]

@[fun_prop] theorem intZero : Poly (fun a : ℤ => decide (a=0)) := by
  have h := natZero.comp intAbs
  exact h.of_eq (by intro a;simp)

@[fun_prop] theorem boolNot : Poly Bool.not := by
  have h : Poly (fun a : Bool => if a then false else true) := by fun_prop
  exact h.of_eq (by intro a;cases a <;> rfl)
@[fun_prop] theorem boolAnd : Poly (fun a : Bool×Bool => a.1 && a.2) := by
  have h : Poly (fun a : Bool×Bool => if a.1 then a.2 else false) := by fun_prop
  exact h.of_eq (by intro a;cases a.1 <;> rfl)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

@[simp] lemma unary_code_length (n : Unary) : (code n).length=n.val := by
  change (unaryCode n.val).length=n.val
  simp
@[simp] lemma nat_code_length (n : ℕ) : (code n).length=n.bits.length := rfl
@[simp] lemma prod_code_length {A B : Type} [Coding A] [Coding B] (a : A×B) :
    (code a).length=2*(code a.1).length+1+(code a.2).length := pairCode_length ..

lemma succ_iterate (a n : ℕ) : Nat.succ^[n] a=a+n := by
  induction n with
  | zero => simp
  | succ n ih => simp [iterate_succ_apply',ih,Nat.add_assoc]

lemma bits_length_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))

namespace Procedure

/-- A clean procedure computing unary predecessor. -/
def unaryPred : Procedure unaryCode unaryCode Nat.pred where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .drop ()
  bound := TimeBound.variable+1
  correct a := by
    refine ⟨1,by simp,?_⟩
    have h := Eval.drop () (single () (unaryCode a))
    convert h using 1
    · funext k
      cases k
      simp [single,unaryCode,List.tail_replicate]
  size a := by simp; omega

end Procedure

namespace Poly
@[fun_prop] theorem unaryToNat : Poly (Unary.val : Unary → ℕ) := by
  have hs : Poly Nat.succ := by
    exact (natAdd.comp (show Poly (fun a : ℕ => (a,1)) by fun_prop)).of_eq (by intro a;rfl)
  have hh := hs.iterate (2*TimeBound.variable) (by
    intro n a i hi
    simp only [succ_iterate,nat_code_length,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_variable,pairCode_length,unaryCode_length]
    have h := add_bits_length a i
    have h' := bits_length_le i
    omega)
  have ht := hh.comp (show Poly (fun a : Unary => (a,(0:ℕ))) by fun_prop)
  exact ht.of_eq (by intro a;simp [succ_iterate])

@[fun_prop] theorem unaryPred : Poly (fun a : Unary => Unary.mk (a.val-1)) :=
  (show Feasible unaryCode unaryCode Nat.pred from ⟨Procedure.unaryPred⟩).recode
    _ _ _ Unary.val (by intro a;rfl) (by intro a;rfl)

@[fun_prop] theorem unaryZero : Poly (fun a : Unary => decide (a.val=0)) := by
  exact natZero.comp unaryToNat

@[fun_prop] theorem unaryLt : Poly (fun a : Unary×Unary => decide (a.1.val<a.2.val)) := by
  exact natLt.comp (show Poly (fun a : Unary×Unary => (a.1.val,a.2.val)) by fun_prop)

@[fun_prop] theorem unaryLe : Poly (fun a : Unary×Unary => decide (a.1.val≤a.2.val)) := by
  have hh := boolNot.comp (unaryLt.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop))
  exact hh.of_eq (by
    intro a
    by_cases h : a.1.val≤a.2.val
    · simp [h,show ¬a.2.val<a.1.val by omega]
    · simp [h,show a.2.val<a.1.val by omega])

@[fun_prop] theorem unaryEq : Poly (fun a : Unary×Unary => decide (a.1.val=a.2.val)) := by
  have hh := boolAnd.comp (unaryLe.pair
    (unaryLe.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)))
  exact hh.of_eq (by intro a;by_cases h : a.1.val=a.2.val <;> simp_all;omega)

lemma unaryPred_iterate (a : Unary) (n : ℕ) :
    (fun a : Unary => Unary.mk (a.val-1))^[n] a=Unary.mk (a.val-n) := by
  induction n with
  | zero => cases a;rfl
  | succ n ih => simp [iterate_succ_apply',ih,Nat.sub_sub ]

@[fun_prop] theorem unarySub : Poly (fun a : Unary×Unary => Unary.mk (a.1.val-a.2.val)) := by
  have hh := unaryPred.iterate TimeBound.variable (by
    intro n a i hi
    simp only [unaryPred_iterate,unary_code_length,TimeBound.eval_variable,pairCode_length,
      unaryCode_length]
    omega)
  have ht := hh.comp (show Poly (fun a : Unary×Unary => (a.2,a.1)) by fun_prop)
  exact ht.of_eq (by intro a;exact unaryPred_iterate _ _)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma int_add_bits_le (a b : ℤ) :
    (a+b).natAbs.bits.length≤a.natAbs.bits.length+b.natAbs.bits.length :=
  (nat_bits_mono (Int.natAbs_add_le a b)).trans (add_bits_length a.natAbs b.natAbs)

lemma int_mul_bits_le (a b : ℤ) :
    (a*b).natAbs.bits.length≤a.natAbs.bits.length+b.natAbs.bits.length := by
  simpa only [Int.natAbs_mul, wordValue_bits] using product_bits_length a.natAbs.bits b.natAbs.bits

@[simp] lemma int_code_length (a : ℤ) : (code a).length=a.natAbs.bits.length+3 := intCode_length a

lemma powerStep_iterate (a : ℤ×ℤ) (n : ℕ) :
    (fun a : ℤ×ℤ => (a.1,a.2*a.1))^[n] a=(a.1,a.2*a.1^n) := by
  induction n with
  | zero => simp
  | succ n ih => simp [iterate_succ_apply',ih,pow_succ,mul_assoc]

lemma int_pow_bits_le (a : ℤ) (n : ℕ) : (a^n).natAbs.bits.length≤1+n*a.natAbs.bits.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hh := int_mul_bits_le (a^n) a
    nlinarith only [ih,hh]

namespace Poly

@[fun_prop] theorem intPow : Poly (fun a : ℤ×Unary => a.1^a.2.val) := by
  have hs : Poly (fun a : ℤ×ℤ => (a.1,a.2*a.1)) := by fun_prop
  have ht := hs.iterate (10*(TimeBound.variable+1)^2) (by
    intro n a i hi
    simp only [powerStep_iterate,prod_code_length,int_code_length,TimeBound.eval_mul,
      TimeBound.eval_numeral,TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,
      pairCode_length,unaryCode_length]
    have hh := int_mul_bits_le a.2 (a.1^i)
    have hp := int_pow_bits_le a.1 i
    have hin := Nat.mul_le_mul_right a.1.natAbs.bits.length hi
    nlinarith only [hh,hp,hin,Nat.zero_le (a.1.natAbs.bits.length^2),
      Nat.zero_le (a.2.natAbs.bits.length^2),Nat.zero_le (n^2)])
  have hm := (show Poly (Prod.snd : ℤ×ℤ → ℤ) from snd).comp
    (ht.comp (show Poly (fun a : ℤ×Unary => (a.2,(a.1,(1:ℤ)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [powerStep_iterate])

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- Consume the head of an integer list and add it to the accumulator. -/
def sumStep (a : List ℤ×ℤ) : List ℤ×ℤ := (a.1.tail,a.2+a.1.headD 0)

lemma sumStep_code_le (a : List ℤ×ℤ) : (code (sumStep a)).length≤(code a).length := by
  rcases a with ⟨l,z⟩
  cases l with
  | nil => simp [sumStep]
  | cons x l =>
    have hh := int_add_bits_le z x
    simp only [sumStep,List.tail_cons,List.headD_cons,prod_code_length,int_code_length]
    change 2*(listCode code l).length+1+(z+x).natAbs.bits.length+3≤
      2*(listCode code (x::l)).length+1+z.natAbs.bits.length+3
    simp only [listCode_cons,List.length_append,codeWord_length,int_code_length]
    omega

lemma sumStep_code_iterate_le (a : List ℤ×ℤ) (n : ℕ) :
    (code (sumStep^[n] a)).length≤(code a).length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply']; exact (sumStep_code_le _).trans ih

lemma sumStep_iterate_length (l : List ℤ) (z : ℤ) :
    sumStep^[l.length] (l,z)=([],z+l.sum) := by
  induction l generalizing z with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp only [sumStep,List.tail_cons,List.headD_cons,ih,List.sum_cons]
    simp [add_assoc]

namespace Poly
@[fun_prop] theorem listSum : Poly (List.sum : List ℤ → ℤ) := by
  have hs : Poly sumStep := by unfold sumStep; fun_prop
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := sumStep_code_iterate_le a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have hm := (show Poly (Prod.snd : List ℤ×ℤ → ℤ) from snd).comp
    (ht.comp (show Poly (fun a : List ℤ => (Unary.mk a.length,(a,(0:ℤ)))) by fun_prop))
  exact hm.of_eq (by intro a;simp [sumStep_iterate_length])

end Poly
end RationalHitting.StackLanguage

end Complexity
