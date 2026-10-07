/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.DenseRecords
public import Mathlib.Data.Int.NatAbs

/-!
# Rational hitting lists: signed binary

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/SignedBinary.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Replace the front variable-width record, consuming the replacement in 5. -/
def replaceRecord : Program (Fin 8) :=
  .seq (unpackRecord.rename peekUnpack) (.seq (clear 2)
    (.seq (reverse 5 2) (packRecord.rename peekPack)))

lemma eval_replaceRecord (old new tail : List Bool) (s : Store (Fin 8))
    (h0 : s 0 = codeWord old++tail) (h2 : s 2 = []) (h3 : s 3 = [])
    (h5 : s 5 = new) :
    Eval replaceRecord s (update (update s 0 (codeWord new++tail)) 5 [])
      (7*old.length+6*new.length+16) := by
  let u := update (update (update s 0 tail) 2 old.reverse) 3 []
  let v := update u 2 []
  let z := update (update v 5 []) 2 new.reverse
  have h1 := eval_rename_from peekUnpack peekUnpack.injective s
    (eval_unpackRecord old tail (fun k => s (peekUnpack k)) h0 h3)
  have hu : Eval (unpackRecord.rename peekUnpack) s u (5*old.length+8) := by
    simp only [extend_update_store peekUnpack peekUnpack.injective,
      extend_pull_store peekUnpack peekUnpack.injective] at h1
    simpa [peekUnpack,u,h2] using h1
  have hv : Eval (clear 2) u v (2*old.length+1) := by
    simpa [u,v] using eval_clear (2 : Fin 8) u
  have hz : Eval (reverse 5 2) v z (2*new.length+1) := by
    simpa [v,u,z,h5] using eval_reverse (a := (5 : Fin 8)) (b := 2) (by decide) v
  have h4 := eval_rename_from peekPack peekPack.injective z
    (eval_packRecord (fun k => z (peekPack k)))
  simp only [extend_update_store peekPack peekPack.injective,
    extend_pull_store peekPack peekPack.injective] at h4
  have heq : update (update z (peekPack 0) []) (peekPack 1)
      (codeWord (z (peekPack 0)).reverse++z (peekPack 1)) =
      update (update s 0 (codeWord new++tail)) 5 [] := by
    funext k; fin_cases k <;> simp [z,v,u,peekPack,h2,h3]
  rw [heq] at h4
  have hh := Eval.seq hu (Eval.seq hv (Eval.seq hz h4))
  convert hh using 1 <;> simp [replaceRecord,z,v,u,peekPack] ; omega

/-- Indexed overwrite with no fixed cell width or numerical oracle. -/
def arrayWrite : Program (Fin 8) := .seq scan (.seq replaceRecord restore)

theorem eval_arrayWrite (pre post : List (List Bool)) (old new : List Bool) (s : Store (Fin 8))
    (h0 : s 0 = codeArray (pre++old::post)) (h1 : s 1 = [])
    (h2 : s 2 = []) (h3 : s 3 = []) (h4 : s 4 = List.replicate pre.length true)
    (h5 : s 5 = new) :
    ∃ t ≤ 40*(s 0).length+6*new.length+30,
      Eval arrayWrite s (update (update (update s 0 (codeArray (pre++new::post))) 4 []) 5 []) t
        := by
  let tail := codeArray (old::post)
  let u := update (update (update s 0 tail) 1 (codeArray pre.reverse)) 4 []
  let v := update (update u 0 (codeWord new++codeArray post)) 5 []
  have hu : Eval scan s u (scanCost pre) := by
    simpa [u,h1] using eval_scan pre tail s (by simpa [tail] using h0) h4 h2 h3
  have hv : Eval replaceRecord u v (7*old.length+6*new.length+16) := by
    apply eval_replaceRecord old new (codeArray post) u <;> simp [u,tail,h2,h3,h5]
  have hz := eval_restore pre.reverse v (by simp [v,u]) (by simp [v,u,h2]) (by simp [v,u,h3])
  have hfinal : update (update v 1 []) 0 (codeArray pre.reverse.reverse++v 0) =
      update (update (update s 0 (codeArray (pre++new::post))) 4 []) 5 [] := by
    funext k; fin_cases k <;> simp [v,u,h1]
  rw [hfinal] at hz
  have hh := Eval.seq hu (Eval.seq hv hz)
  refine ⟨_,?_,hh⟩
  have hs := scanCost_bound pre
  have hr := restoreCost_bound pre.reverse
  simp only [codeArray_reverse_length] at hr
  rw [h0]
  simp only [codeArray_append,codeArray_cons,List.length_append,codeWord_length]
  omega

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- Repeated multiplication, preserving the binary base in register 8 and
consuming a unary exponent in register 9. Used in the Taylor input matrices. -/
def powerBody : Program (Fin 10) :=
  .seq (copy 8 1 7) (.seq (multiplyClean.rename factorMul) (.drop 9))

/-- Repeat multiplication over a unary exponent counter. -/
def powerLoop : Program (Fin 10) := .loop 9 powerBody

lemma eval_powerBody (s : Store (Fin 10)) (hf : FactorialScratch s)
    (B : ℕ) (h0 : (s 0).length≤B) (h8 : (s 8).length≤B) :
    ∃ t≤250*(B+1)^4, Eval powerBody s
      (update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits) 9 (s 9).tail) t := by
  let u := update s 1 (s 8)
  let v := update s 0 (wordValue (s 0)*wordValue (s 8)).bits
  have h1 : Eval (copy 8 1 7) s u (7*(s 8).length+7) := by
    have hh := eval_copy (a:=(8 : Fin 10)) (b:=1) (tmp:=7) (by decide) (by decide) (by decide) s
    have he : update (update s 1 (s 8)) 7 []=u := by
      funext k; fin_cases k <;> simp [u,hf 7 (by decide) (by decide)]
    rw [he] at hh
    simpa [hf 1 (by decide) (by decide),hf 7 (by decide) (by decide)] using hh
  obtain ⟨t,ht,hh⟩ := eval_factorMul u (by
    intro k hk hk'; have h := hf k (by omega) hk'; simp [u,show k≠1 by omega,h])
    B (by simpa [u] using h0) (by simpa [u] using h8)
  have he : update (update u 0 (wordValue (u 0)*wordValue (u 1)).bits) 1 []=v := by
    funext k; fin_cases k <;> simp [v,u,hf 1 (by decide) (by decide)]
  rw [he] at hh
  have hd : Eval (Program.drop 9) v (update v 9 (s 9).tail) 1 := by
    simpa [v] using Eval.drop (9 : Fin 10) v
  refine ⟨_,?_,Eval.seq h1 (Eval.seq hh hd)⟩
  nlinarith only [ht,h8,Nat.zero_le (B^2),Nat.zero_le (B^3)]

lemma eval_powerLoop (n B : ℕ) (s : Store (Fin 10))
    (hf : FactorialScratch s) (hcan : (wordValue (s 0)).bits=s 0)
    (hn : (s 9).length=n) (hp : (s 0).length+n*(s 8).length≤B)
    (hb : (s 8).length≤B) :
    ∃ t≤n*(250*(B+1)^4+1)+1, Eval powerLoop s
      (update (update s 0 (wordValue (s 0)*wordValue (s 8)^n).bits) 9 []) t := by
  induction n generalizing s with
  | zero =>
    have hz : s 9=[] := List.length_eq_zero_iff.mp hn
    have hh : update (update s 0 (wordValue (s 0)*wordValue (s 8)^0).bits) 9 []=s := by
      simp [hcan,←hz]
    rw [hh]
    exact ⟨1,by simp,Eval.whileNil hz⟩
  | succ n ih =>
    let u := update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits) 9 (s 9).tail
    obtain ⟨t,ht,he⟩ := eval_powerBody s hf B (by omega) hb
    have hu : FactorialScratch u := by
      intro k hk hk'; simpa [u,show k≠0 by omega,show k≠9 by omega] using hf k hk hk'
    have hc : (wordValue (u 0)).bits=u 0 := by simp [u]
    have hn' : (u 9).length=n := by simp [u,List.length_tail,hn]
    have hlen : (u 0).length≤(s 0).length+(s 8).length := by
      simpa [u] using product_bits_length
        (s 0) (s 8)
    have hp' : (u 0).length+n*(u 8).length≤B := by
      have h8eq : u 8=s 8 := by simp [u]
      rw [h8eq]
      nlinarith only [hlen,hp]
    obtain ⟨w,hw,he'⟩ := ih u hu hc hn' hp' (by simpa [u] using hb)
    have hx : update (update u 0 (wordValue (u 0)*wordValue (u 8)^n).bits) 9 []=
        update (update s 0 (wordValue (s 0)*wordValue (s 8)^(n+1)).bits) 9 [] := by
      funext k; by_cases hk0 : k=0 <;> by_cases hk9 : k=9 <;>
        simp_all [u,pow_succ,Nat.mul_assoc,Nat.mul_comm]
    rw [hx] at he'
    have hne : s 9≠[] := by intro h; simp [h] at hn
    exact ⟨1+t+w,by nlinarith,Eval.whileCons hne he he'⟩

/-- Initialize the multiplicative identity and execute exponentiation. -/
def powerCore : Program (Fin 10) := .seq (.push 0 true) powerLoop

/-- A fixed finite power subroutine. Its exponent is unary and its output is
canonical binary. No exponentiation instruction is supplied by the machine. -/
theorem eval_powerCore (s : Store (Fin 10)) (hf : FactorialScratch s) (h0 : s 0=[])
    (n : ℕ) (hn : (s 9).length=n) :
    ∃ t≤n*(250*(2+(n+1)*(s 8).length)^4+1)+3,
      Eval powerCore s (update (update s 0 (wordValue (s 8)^n).bits) 9 []) t := by
  let u := update s 0 [true]
  have hu : FactorialScratch u := by
    intro k hk hk'; simpa [u,show k≠0 by omega] using hf k hk hk'
  obtain ⟨t,ht,he⟩ := eval_powerLoop n (1+(n+1)*(s 8).length) u hu
    (by simp [u,wordValue]) (by simpa [u] using hn)
    (by simp [u];nlinarith) (by simp [u];nlinarith)
  have hh : Eval (Program.push 0 true) s u 1 := by simpa [u,h0] using Eval.push (0 : Fin 10) true s
  have hx : update (update u 0 (wordValue (u 0)*wordValue (u 8)^n).bits) 9 []=
      update (update s 0 (wordValue (s 8)^n).bits) 9 [] := by simp [u,wordValue]
  rw [hx] at he
  refine ⟨1+1+t,?_,Eval.seq hh he⟩
  have heq : 1+(n+1)*(s 8).length+1=2+(n+1)*(s 8).length := by omega
  rw [heq] at ht
  omega

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_complement (w : List Bool) :
    wordValue (w.map Bool.not)+wordValue w+1=2^w.length := by
  induction w with
  | nil => simp [wordValue]
  | cons b w ih => cases b <;> simp [wordValue,pow_succ] at * <;> omega

/-- Move a word to another stack while complementing each bit. -/
def flipReverse (a b : K) : Program K :=
  .loop a (readBit a (fun x => .seq (.drop a) (.push b (!x))))

lemma eval_flipReverse {a b : K} (hab : a≠b) (s : Store K) :
    Eval (flipReverse a b) s
      (update (update s a []) b (((s a).map Bool.not).reverse ++ s b))
      (5*(s a).length+1) := by
  generalize he : s a=w
  induction w generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b)=s := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all
    simpa [flipReverse,he,hh] using (Eval.whileNil (p:=readBit a (fun x => .seq (.drop a) (.push
      b (!x)))) he)
  | cons x w ih =>
    let u := update s a w
    let v := update u b ((!x)::s b)
    have h1 : Eval (Program.drop a) s u 1 := by simpa [u,he] using Eval.drop a s
    have h2 : Eval (Program.push b (!x)) u v 1 := by
      simpa [v,u,Ne.symm hab] using Eval.push b
        (!x) u
    have hr : Eval (readBit a (fun y => Program.seq (.drop a) (.push b (!y)))) s v 4 := by
      apply eval_readBit a _ s v 3
      simpa [he] using Eval.seq h1 h2
    have h3 := ih v (by simp [v,u,hab])
    have hh := Eval.whileCons (by simp [he]) hr h3
    have heq : update (update v a []) b ((w.map Bool.not).reverse++v b)=
        update (update s a []) b (((x::w).map Bool.not).reverse++s b) := by
      funext k; by_cases ha : k=a <;> by_cases hb : k=b <;>
        simp_all [v,u,List.reverse_cons,List.append_assoc]
    rw [heq] at hh
    convert hh using 1 <;> simp [flipReverse] ; omega

/-- Complement every bit and restore the original word order. -/
def flipWord (a b : K) : Program K := .seq (flipReverse a b) (reverse b a)

lemma eval_flipWord {a b : K} (hab : a≠b) (s : Store K) (hb : s b=[]) :
    Eval (flipWord a b) s (update s a ((s a).map Bool.not)) (7*(s a).length+3) := by
  let u := update (update s a []) b ((s a).map Bool.not).reverse
  have e1 : Eval (flipReverse a b) s u (5*(s a).length+1) := by
    simpa [u,hb] using eval_flipReverse hab s
  have e2 := eval_reverse (a:=b) (b:=a) (Ne.symm hab) u
  have heq : update (update u b []) a ((u b).reverse++u a)=update s a ((s a).map Bool.not) := by
    funext k; by_cases ha : k=a <;> by_cases hc : k=b <;> simp_all [u]
  rw [heq] at e2
  have hh := Eval.seq e1 e2
  convert hh using 1 <;> simp [flipWord,u] ; omega

/-- Compute the absolute difference of two binary word values. -/
def absoluteWord (a b : List Bool) : List Bool :=
  let r := subtractWord a b false
  if r.2 then incrementWord (r.1.map Bool.not) else r.1

lemma absoluteWord_length (a b : List Bool) :
    (absoluteWord a b).length≤ max a.length b.length+1 := by
  dsimp only [absoluteWord]
  split
  · exact (incrementWord_length _).trans (by simp [subtractWord_length])
  · rw [subtractWord_length]; omega

lemma absoluteWord_value (a b : List Bool) :
    wordValue (absoluteWord a b)=((wordValue a : ℤ)-(wordValue b : ℤ)).natAbs := by
  have hv := subtractWord_value a b false
  have hc := wordValue_complement (subtractWord a b false).1
  rw [subtractWord_length] at hc
  by_cases hlt : wordValue a<wordValue b
  · have hr := (subtractWord_borrow a b).mpr hlt
    simp only [absoluteWord,hr,ite_true,incrementWord_value]
    simp [hr,bitNat] at hv
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega)]
    omega
  · obtain ⟨hr,he⟩ := subtractWord_nonnegative (by omega : wordValue b≤wordValue a)
    simp [absoluteWord,hr,he,Int.natAbs_natCast_sub_natCast_of_ge (by omega : wordValue
      b≤wordValue a)]

/-- Convert the modular subtraction result to an absolute magnitude according
to its genuinely computed borrow bit. -/
def absolutize : Program (Fin 5) :=
  .seq (.branch 3 .skip .skip (.seq (flipWord 0 1) (increment 0 1 2))) (normalize 0 1 2)

lemma eval_absolutize (s : Store (Fin 5)) (c : Bool) (h3 : s 3=[c]) (h1 : s 1=[]) (h2 : s 2=[]) :
    ∃ t ≤ 30*(s 0).length+52, Eval absolutize s
      (update s 0 (wordValue (if c then incrementWord ((s 0).map Bool.not) else s 0)).bits) t := by
  let w := if c then incrementWord ((s 0).map Bool.not) else s 0
  have hw : w.length≤(s 0).length+1 := by
    cases c <;> simp only [w,Bool.false_eq_true,ite_true,ite_false]
    · omega
    · simpa using incrementWord_length ((s 0).map Bool.not)
  have hpre : ∃ t ≤ 14*(s 0).length+23,
      Eval (Program.branch (3 : Fin 5) .skip .skip (.seq (flipWord 0 1) (increment 0 1 2)))
        s (update s 0 w) t := by
    cases c with
    | false => exact ⟨2,by omega,by simpa [w] using Eval.branchFalse h3 (Eval.skip s)⟩
    | true =>
      let u := update s 0 ((s 0).map Bool.not)
      have e1 := eval_flipWord (a:=0) (b:=1) (by decide) s h1
      obtain ⟨t,ht,e2⟩ := eval_increment (a:=0) (tmp:=1) (flag:=2)
        (by decide) (by decide) (by decide) u
      have hh := Eval.branchTrue (p:=.skip) (q:=.skip) h3 (Eval.seq e1 e2)
      have heq : update (update (update u 0 (incrementWord (u 0))) 1 []) 2 []=update s 0 w := by
        funext k; fin_cases k <;> simp [u,w,h1,h2]
      rw [heq] at hh
      refine ⟨_,?_,hh⟩
      simp [u,h1,h2] at ht
      omega
  obtain ⟨t,ht,e1⟩ := hpre
  let v := update s 0 w
  obtain ⟨u,hu,e2⟩ := eval_normalize (a:=0) (tmp:=1) (flag:=2)
    (by decide) (by decide) (by decide) v
  have heq : update (update (update v 0 (normalizeWord (v 0))) 1 []) 2 []=
      update s 0 (wordValue w).bits := by
    funext k; fin_cases k <;> simp [v,h1,h2,normalizeWord_eq_bits]
  rw [heq] at e2
  refine ⟨1+t+u,?_,Eval.seq e1 e2⟩
  simp [v,h1,h2] at hu
  omega

/-- Signed difference of arbitrary naturals, in canonical signed magnitude. -/
def signedDifference : Program (Fin 5) := .seq subtract absolutize

lemma eval_signedDifference (s : Store (Fin 5)) (h2 : s 2=[]) (h3 : s 3=[]) (h4 : s 4=[]) :
    ∃ t ≤ 100*((s 0).length+(s 1).length+1), Eval signedDifference s
      (update (update (update s 0 (((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs).bits) 1 [])
        3 [decide (wordValue (s 0)<wordValue (s 1))]) t := by
  obtain ⟨t,ht,e1⟩ := eval_subtract s
  let r := subtractWord (s 0) (s 1) false
  let v := update (update s 0 r.1) 1 []
  let u := update v 3 [r.2]
  have ev1 : Eval subtract s u t := by
    have he : update (update (update (update (update s 0 r.1) 1 []) 2 []) 3 [r.2]) 4 []=u := by
      funext k; fin_cases k <;> simp [u,v,h2,h4]
    change Eval subtract s (update (update (update (update (update s 0 r.1) 1 []) 2 []) 3 [r.2])
      4 []) t at e1
    simpa only [he] using e1
  obtain ⟨u',hu,e2⟩ := eval_absolutize u r.2 (by simp [u])
    (by simp [u,v]) (by simp [u,v,h2])
  have hh := Eval.seq ev1 e2
  have hr : r.2=decide (wordValue (s 0)<wordValue (s 1)) := by
    have he := subtractWord_borrow (s 0) (s 1)
    cases hc : r.2 <;> simp_all [r]
  have heq : update u 0 (wordValue (if r.2 then incrementWord ((u 0).map Bool.not) else u 0)).bits=
      update (update (update s 0 (((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs).bits) 1 [])
        3 [decide (wordValue (s 0)<wordValue (s 1))] := by
    have hv : wordValue (if r.2 then incrementWord ((u 0).map Bool.not) else u 0)=
        ((wordValue (s 0):ℤ)-(wordValue (s 1):ℤ)).natAbs := by
      simpa [u,v,absoluteWord,r] using absoluteWord_value (s 0) (s 1)
    rw [hv]
    funext k; fin_cases k <;> simp [u,v,hr]
  rw [heq] at hh
  refine ⟨1+t+u',?_,hh⟩
  simp [u,v,r,subtractWord_length] at hu
  simp [h2,h3,h4] at ht
  omega

end RationalHitting.StackLanguage

end Complexity
