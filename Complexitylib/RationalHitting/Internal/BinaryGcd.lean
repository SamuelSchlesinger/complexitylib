/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryDivision

/-!
# Rational hitting lists: binary gcd

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryGcd.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Embed the subtraction registers in the division register bank. -/
def subEmbed : Fin 5 ↪ Fin 10 := Fin.castAddEmb 5

/-- The subtraction program renamed into ten registers. -/
def subtract10 : Program (Fin 10) := subtract.rename subEmbed

lemma eval_subtract10 (s : Store (Fin 10)) :
    ∃ t ≤ 17*((s 0).length+(s 1).length)+2*(s 2).length+2*(s 3).length+2*(s 4).length+19,
      Eval subtract10 s
        (update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 []) t := by
  obtain ⟨t,ht,he⟩ := eval_subtract (fun k : Fin 5 => s (subEmbed k))
  have hh := eval_rename_from subEmbed subEmbed.injective s he
  refine ⟨t,ht,?_⟩
  have h0 : subEmbed 0 = 0 := by decide
  have h1 : subEmbed 1 = 1 := by decide
  have h2 : subEmbed 2 = 2 := by decide
  have h3 : subEmbed 3 = 3 := by decide
  have h4 : subEmbed 4 = 4 := by decide
  simpa only [subtract10,h0,h1,h2,h3,h4,extend_update_store subEmbed subEmbed.injective,
    extend_pull_store subEmbed subEmbed.injective] using hh

/-- Select the successful subtraction result or restore the original value. -/
def reducePick : Program (Fin 10) :=
  .branch 3 .skip (.push 7 true) (.seq (copy 8 0 9) (.push 7 false))

lemma eval_reducePick (s : Store (Fin 10)) (c : Bool) (hc : s 3 = [c]) (h9 : s 9 = []) :
    ∃ t ≤ 7*(s 8).length+2*(s 0).length+10,
      Eval reducePick s
        (update (update s 0 (if c then s 8 else s 0)) 7 ((!c)::s 7)) t := by
  cases c with
  | false =>
    refine ⟨2,by omega,?_⟩
    simpa [reducePick] using (Eval.branchFalse (p := Program.skip)
      (r := Program.seq (copy 8 0 9) (.push 7 false)) hc (Eval.push (7 : Fin 10) true s))
  | true =>
    let u := update (update s 0 (s 8)) 9 []
    have hc' := eval_copy (a := (8 : Fin 10)) (b := 0) (tmp := 9) (by decide) (by decide) (by
      decide) s
    have hp : Eval (Program.push 7 false) u (update u 7 (false::s 7)) 1 := by
      simpa [u] using Eval.push (7 : Fin 10) false u
    have hh := Eval.branchTrue (p := Program.skip) (q := Program.push 7 true) hc (Eval.seq hc' hp)
    have heq : update u 7 (false::s 7) = update (update s 0 (s 8)) 7 (false::s 7) := by
      funext k; by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> by_cases hk9 : k=9 <;> simp_all [u]
    rw [heq] at hh
    refine ⟨7*(s 8).length+2*(s 0).length+10,le_refl _,?_⟩
    convert hh using 1 <;> simp [reducePick,h9,Nat.add_comm] ; omega

/-- One attempted subtraction, followed by normalization and scratch cleanup. -/
def reduceOnce : Program (Fin 10) :=
  .seq (copy 0 8 9) (.seq (copy 5 1 9) (.seq subtract10 (.seq reducePick
    (.seq (normalize 0 2 4) (.seq (clear 3) (clear 8))))))

/-- The scratch-register emptiness invariant for division. -/
def DivScratch (s : Store (Fin 10)) : Prop :=
  s 1 = [] ∧ s 2 = [] ∧ s 3 = [] ∧ s 4 = [] ∧ s 8 = [] ∧ s 9 = []

lemma eval_reduceOnce (s : Store (Fin 10)) (hs : DivScratch s) :
    ∃ t ≤ 100*((s 0).length+(s 5).length+1),
      Eval reduceOnce s (update (update s 0 (reduceWord (s 0) (s 5)).1)
        7 ((reduceWord (s 0) (s 5)).2::s 7)) t := by
  obtain ⟨h1,h2,h3,h4,h8,h9⟩ := hs
  let s₁ := update (update s 8 (s 0)) 9 []
  let s₂ := update (update s₁ 1 (s 5)) 9 []
  have hc0 : Eval (copy 0 8 9) s s₁ (7*(s 0).length+7) := by
    simpa [s₁,h8,h9] using eval_copy (a := (0 : Fin 10)) (b := 8) (tmp := 9) (by decide) (by
      decide) (by decide) s
  have hc5 : Eval (copy 5 1 9) s₁ s₂ (7*(s 5).length+7) := by
    simpa [s₂,s₁,h1] using eval_copy (a := (5 : Fin 10)) (b := 1) (tmp := 9) (by decide) (by
      decide) (by decide) s₁
  obtain ⟨t,ht,hd⟩ := eval_subtract10 s₂
  let r := subtractWord (s 0) (s 5) false
  let s₃ := update (update (update (update (update s₂ 0 r.1) 1 []) 2 []) 3 [r.2]) 4 []
  have hd' : Eval subtract10 s₂ s₃ t := by simpa [s₃,r,s₂,s₁] using hd
  obtain ⟨u,hu,hp⟩ := eval_reducePick s₃ r.2 (by simp [s₃]) (by simp [s₃,s₂])
  let s₄ := update (update s₃ 0 (if r.2 then s 0 else r.1)) 7 ((!r.2)::s 7)
  have hp' : Eval reducePick s₃ s₄ u := by simpa [s₄,s₃,s₂,s₁] using hp
  obtain ⟨v,hv,hn⟩ := eval_normalize (a := (0 : Fin 10)) (tmp := 2) (flag := 4)
    (by decide) (by decide) (by decide) s₄
  let s₅ := update (update (update s₄ 0 (normalizeWord (s₄ 0))) 2 []) 4 []
  have hn' : Eval (normalize 0 2 4) s₄ s₅ v := hn
  let s₆ := update s₅ 3 []
  have hclear3 : Eval (clear 3) s₅ s₆ 3 := by simpa [s₆,s₅,s₄,s₃] using eval_clear (3 : Fin 10) s₅
  have hclear8 : Eval (clear 8) s₆ (update s₆ 8 []) (2*(s 0).length+1) := by
    simpa [s₆,s₅,s₄,s₃,s₂,s₁] using eval_clear (8 : Fin 10) s₆
  have heval := Eval.seq hc0 (Eval.seq hc5 (Eval.seq hd' (Eval.seq hp' (Eval.seq hn' (Eval.seq
    hclear3 hclear8)))))
  have heq : update s₆ 8 [] = update (update s 0 (reduceWord (s 0) (s 5)).1)
      7 ((reduceWord (s 0) (s 5)).2::s 7) := by
    funext k
    cases hr : r.2 <;> dsimp [r] at hr <;> fin_cases k <;>
      simp [s₆,s₅,s₄,s₃,s₂,s₁,reduceWord,r,hr,h1,h2,h3,h4,h8,h9]
  rw [heq] at heval
  refine ⟨_,?_,heval⟩
  have hlen : r.1.length = max (s 0).length (s 5).length := subtractWord_length ..
  have hchosen : (if r.2 then s 0 else r.1).length ≤ (s 0).length+(s 5).length := by
    cases r.2 <;> simp [hlen]
  simp [s₂,s₁,h2,h3,h4] at ht
  simp [s₃,s₂,s₁] at hu
  simp [s₄,s₃] at hv
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

@[simp] lemma wordValue_bits (n : ℕ) : wordValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b <;> simp [wordValue,ih,Nat.bit] ; omega

/-- Remainder 0, denominator 5, unread MSD numerator 6, quotient 7. -/
def divBody : Program (Fin 10) :=
  readBit 6 fun x => .seq (.drop 6) (.seq (.push 0 x) reduceOnce)
/-- Repeat binary division steps over the input bits. -/
def divLoop : Program (Fin 10) := .loop 6 divBody

lemma eval_divBody (s : Store (Fin 10)) (hs : DivScratch s) (x : Bool) (l : List Bool)
    (h6 : s 6=x::l) :
    ∃ t ≤ 110*((s 0).length+(s 5).length+2),
      Eval divBody s (update (update (update s 6 l) 0 (reduceWord (x::s 0) (s 5)).1)
        7 ((reduceWord (x::s 0) (s 5)).2::s 7)) t := by
  let s₁ := update s 6 l
  let s₂ := update s₁ 0 (x::s 0)
  have hd : Eval (Program.drop 6) s s₁ 1 := by simpa [s₁,h6] using Eval.drop (6 : Fin 10) s
  have hp : Eval (Program.push 0 x) s₁ s₂ 1 := by simpa [s₂,s₁] using Eval.push (0 : Fin 10) x s₁
  have hs₂ : DivScratch s₂ := by simpa [DivScratch,s₂,s₁] using hs
  obtain ⟨t,ht,he⟩ := eval_reduceOnce s₂ hs₂
  have hh := eval_readBit 6 (fun x => Program.seq (.drop 6) (.seq (.push 0 x) reduceOnce)) s _ _
    (by simpa [h6] using Eval.seq hd (Eval.seq hp he))
  refine ⟨1+(2+(2+t)),?_,?_⟩
  · simp [s₂,s₁] at ht
    omega
  · simpa [divBody,s₂,s₁,update_idem] using hh

lemma eval_divLoop (s : Store (Fin 10)) (hs : DivScratch s)
    (hb : 0<wordValue (s 5)) (hr : wordValue (s 0)<wordValue (s 5))
    (B : ℕ) (hB : (s 0).length ≤ B) (hbB : (s 5).length ≤ B) :
    ∃ t ≤ (s 6).length*(250*(B+1))+1,
      Eval divLoop s
        (update (update (update s 6 []) 0 (divideDigits (s 5) (s 6) (s 0) (s 7)).1)
          7 (divideDigits (s 5) (s 6) (s 0) (s 7)).2) t := by
  generalize h6 : s 6 = l
  induction l generalizing s with
  | nil =>
    have heq : update (update (update s 6 []) 0 (s 0)) 7 (s 7) = s := by
      funext k; by_cases hk6 : k=6 <;> by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> simp_all
    refine ⟨1,by simp,?_⟩
    simpa only [divideDigits,heq,divLoop] using (Eval.whileNil (p := divBody) h6)
  | cons x l ih =>
    let r := reduceWord (x::s 0) (s 5)
    let u := update (update (update s 6 l) 0 r.1) 7 (r.2::s 7)
    have hc : wordValue (x::s 0) < 2*wordValue (s 5) := by
      have hx := bitNat_le_one x
      rw [wordValue_bit]; omega
    obtain ⟨hr',_,hlen⟩ := reduceWord_spec (x::s 0) (s 5) hb hc
    obtain ⟨t,ht,he⟩ := eval_divBody s hs x l h6
    have hs' : DivScratch u := by simpa [DivScratch,u] using hs
    obtain ⟨v,hv,hloop⟩ := ih u hs' (by simpa [u] using hb) (by simpa [u,r] using hr')
      (by simpa [u,r] using hlen.trans hbB) (by simpa [u] using hbB) (by simp [u])
    have h := Eval.whileCons (by simp [h6]) he hloop
    have heq : update (update (update u 6 []) 0 (divideDigits (u 5) l (u 0) (u 7)).1)
        7 (divideDigits (u 5) l (u 0) (u 7)).2 =
        update (update (update s 6 []) 0 (divideDigits (s 5) (x::l) (s 0) (s 7)).1)
        7 (divideDigits (s 5) (x::l) (s 0) (s 7)).2 := by
      funext k; by_cases hk6 : k=6 <;> by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;>
        simp_all [u,r,divideDigits]
    rw [heq] at h
    refine ⟨1+t+v,?_,h⟩
    simp only [List.length_cons]
    have hstep : 1+t ≤ 250*(B+1) := by omega
    nlinarith

/-- Binary division starts with numerator in 0 and denominator in 5.
The original denominator is retained; quotient is placed in 7, remainder in 0.
Every other register is cleared. -/
def divide : Program (Fin 10) :=
  .seq (reverse 0 6) (.seq divLoop (normalize 7 2 4))

lemma eval_divide (s : Store (Fin 10)) (hs : DivScratch s) (h6 : s 6=[]) (h7 : s 7=[])
    (hb : 0<wordValue (s 5)) :
    ∃ t ≤ 300*((s 0).length+1)*((s 5).length+1)+30,
      Eval divide s (update (update s 0 (wordValue (s 0)%wordValue (s 5)).bits)
        7 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  let u := update (update s 0 []) 6 (s 0).reverse
  have hre : Eval (reverse 0 6) s u (2*(s 0).length+1) := by
    simpa [u,h6] using eval_reverse (a := (0 : Fin 10)) (b := 6) (by decide) s
  have hu : DivScratch u := by simpa [DivScratch,u] using hs
  obtain ⟨t,ht,he⟩ := eval_divLoop u hu (by simpa [u] using hb)
    (by simpa [u,wordValue] using hb) (s 5).length (by simp [u]) (by simp [u])
  let r := divideDigits (s 5) (s 0).reverse [] []
  let v := update (update (update u 6 []) 0 r.1) 7 r.2
  have he' : Eval divLoop u v t := by simpa [v,r,u,h7] using he
  obtain ⟨w,hw,hn⟩ := eval_normalize (a := (7 : Fin 10)) (tmp := 2) (flag := 4)
    (by decide) (by decide) (by decide) v
  have h := Eval.seq hre (Eval.seq he' hn)
  obtain ⟨hr,hq⟩ := divideDigits_quotient_remainder (s 0) (s 5) hb
  have hrnorm : normalizeWord r.1 = r.1 := by
    -- Each nonempty digit loop ends in a normalized one-step remainder.
    have aux (b l a q : List Bool) (ha : normalizeWord a=a) :
        normalizeWord (divideDigits b l a q).1=(divideDigits b l a q).1 := by
      induction l generalizing a q with
      | nil => exact ha
      | cons x l ih =>
        apply ih
        cases hh : (subtractWord (x::a) b false).2 <;>
          simp [reduceWord,hh,normalizeWord_eq_bits]
    exact aux _ _ _ _ (by rfl)
  have hrbits : r.1=(wordValue (s 0)%wordValue (s 5)).bits := by
    rw [←hrnorm,normalizeWord_eq_bits]
    exact congrArg Nat.bits hr
  have h2 := hs.2.1
  have h4 := hs.2.2.2.1
  have heq : update (update (update v 7 (normalizeWord (v 7))) 2 []) 4 [] =
      update (update s 0 (wordValue (s 0)%wordValue (s 5)).bits)
        7 (wordValue (s 0)/wordValue (s 5)).bits := by
    funext k; by_cases hk0 : k=0 <;> by_cases hk7 : k=7 <;> by_cases hk2 : k=2 <;>
      by_cases hk4 : k=4 <;> by_cases hk6 : k=6 <;>
      simp_all [v,u,hrbits,normalizeWord_eq_bits,r]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  obtain ⟨_,_,hlen,_⟩ := divideDigits_spec (s 5) (s 0).reverse [] [] hb (by simpa [wordValue]
    using hb)
  simp [v,u,h2,h4] at hw
  simp [u] at ht
  simp at hlen
  change r.2.length = (s 0).length at hlen
  rw [hlen] at hw
  nlinarith

end RationalHitting.StackLanguage

end Complexity
