/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinarySubtract

/-!
# Rational hitting lists: binary division

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryDivision.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Subtract the next pair of bits and update the borrow flag. -/
def subtractBody : Program (Fin 5) :=
  .branch 0 (.branch 1 (clear 4) subtractDigit subtractDigit) subtractDigit subtractDigit

/-- Repeat subtraction while the control flag remains set. -/
def subtractLoop : Program (Fin 5) := .loop 4 subtractBody

/-- The register store after one bit-subtraction step. -/
def subStep (s : Store (Fin 5)) (c : Bool) : Store (Fin 5) :=
  update (update (update (update s 0 (s 0).tail) 1 (s 1).tail)
    3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
    2 (differenceBit ((s 0).headD false) ((s 1).headD false) c :: s 2)

/-- The final subtraction store, including output and borrow flag. -/
def subFinish (s : Store (Fin 5)) (c : Bool) : Store (Fin 5) :=
  let r := subtractWord (s 0) (s 1) c
  update (update (update (update (update s 0 []) 1 []) 2 (r.1.reverse++s 2))
    3 [r.2]) 4 []

lemma eval_subtractLoop (s : Store (Fin 5)) (c : Bool) (hc : s 3 = [c]) (hf : s 4 = [true]) :
    ∃ t ≤ 15*((s 0).length+(s 1).length)+7,
      Eval subtractLoop s (subFinish s c) t := by
  generalize ha : s 0 = a, hb : s 1 = b
  induction a generalizing b c s with
  | nil =>
    induction b generalizing c s with
    | nil =>
      have hclear : Eval (clear 4) s (update s 4 []) 3 := by
        simpa [hf] using eval_clear (4 :
          Fin 5) s
      have hbody : Eval subtractBody s (update s 4 []) 5 :=
        Eval.branchNone ha (Eval.branchNone hb hclear)
      have h := Eval.whileCons (k := (4 : Fin 5)) (by simp [hf]) hbody (Eval.whileNil (k := (4 :
        Fin 5)) (p := subtractBody) (by simp))
      have heq : subFinish s c = update s 4 [] := by
        ext k; fin_cases k <;> simp [subFinish,ha,hb,subtractWord,hc]
      exact ⟨7,by simp,by simpa [subtractLoop,heq] using h⟩
    | cons y b ih =>
      let u := subStep s c
      have hcd : u 3 = [borrowBit false y c] := by simp [u,subStep,ha,hb]
      have hflag : u 4 = [true] := by simp [u,subStep,hf]
      obtain ⟨t,ht,hr⟩ := ih u (borrowBit false y c) hcd hflag
        (by simp [u,subStep,ha]) (by simp [u,subStep,hb])
      have hd : Eval subtractDigit s u 12 := eval_subtractDigit s c hc
      have hbdy : Eval subtractBody s u 14 := by
        cases y with
        | false => exact Eval.branchNone ha (Eval.branchFalse hb hd)
        | true => exact Eval.branchNone ha (Eval.branchTrue hb hd)
      have heq : subFinish u (borrowBit false y c) = subFinish s c := by
        ext k; fin_cases k <;>
          simp [subFinish,u,subStep,ha,hb,subtractWord,List.reverse_cons,List.append_assoc]
      rw [heq] at hr
      refine ⟨15+t,?_,Eval.whileCons (by simp [hf]) hbdy hr⟩
      simp [List.length_cons] at *
      omega
  | cons x a ih =>
    let u := subStep s c
    have hcd : u 3 = [borrowBit x (b.headD false) c] := by simp [u,subStep,ha,hb]
    have hflag : u 4 = [true] := by simp [u,subStep,hf]
    obtain ⟨t,ht,hr⟩ := ih u (borrowBit x (b.headD false) c) hcd hflag
      b.tail (by simp [u,subStep,ha]) (by simp [u,subStep,hb])
    have hd : Eval subtractDigit s u 12 := eval_subtractDigit s c hc
    have hbdy : Eval subtractBody s u 13 := by
      cases x with
      | false => exact Eval.branchFalse ha hd
      | true => exact Eval.branchTrue ha hd
    have heq : subFinish u (borrowBit x (b.headD false) c) = subFinish s c := by
      ext k; fin_cases k <;>
        simp [subFinish,u,subStep,ha,hb,subtractWord,List.reverse_cons,List.append_assoc]
    rw [heq] at hr
    refine ⟨14+t,?_,Eval.whileCons (by simp [hf]) hbdy hr⟩
    have hlen : b.tail.length ≤ b.length := by cases b <;> simp
    simp only [List.length_cons]
    omega

/-- Subtract and compare, destructively. Output register 2 has the little-endian
fixed-width modular difference; singleton register 3 is exactly the comparison
bit (true iff the first number was smaller). -/
def subtract : Program (Fin 5) :=
  .seq (clear 2) (.seq (clear 3) (.seq (clear 4) (.seq (.push 3 false)
    (.seq (.push 4 true) (.seq subtractLoop (reverse 2 0))))))

lemma eval_subtract (s : Store (Fin 5)) :
    ∃ t ≤ 17*((s 0).length+(s 1).length)+2*(s 2).length+2*(s 3).length+2*(s 4).length+19,
      Eval subtract s
        (update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 []) t := by
  let s₁ := update s 2 []
  let s₂ := update s₁ 3 []
  let s₃ := update s₂ 4 []
  let s₄ := update s₃ 3 [false]
  let s₅ := update s₄ 4 [true]
  obtain ⟨t,ht,hl⟩ := eval_subtractLoop s₅ false (by simp [s₅,s₄]) (by simp [s₅])
  have hr := eval_reverse (a := (2 : Fin 5)) (b := 0) (by decide) (subFinish s₅ false)
  have hp3 : Eval (Program.push 3 false) s₃ s₄ 1 := by
    simpa [s₄,s₃,s₂] using Eval.push (3 : Fin
      5) false s₃
  have hp4 : Eval (Program.push 4 true) s₄ s₅ 1 := by
    simpa [s₅,s₄,s₃] using Eval.push (4 : Fin
      5) true s₄
  have h := Eval.seq (eval_clear (2 : Fin 5) s) (Eval.seq (eval_clear (3 : Fin 5) s₁)
    (Eval.seq (eval_clear (4 : Fin 5) s₂) (Eval.seq hp3 (Eval.seq hp4 (Eval.seq hl hr)))))
  have heq : update (update (subFinish s₅ false) 2 []) 0
      (((subFinish s₅ false) 2).reverse++(subFinish s₅ false) 0) =
        update (update (update (update (update s 0 (subtractWord (s 0) (s 1) false).1) 1 []) 2 [])
          3 [(subtractWord (s 0) (s 1) false).2]) 4 [] := by
    ext k; fin_cases k <;> simp [subFinish,s₅,s₄,s₃,s₂,s₁]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hlength := subtractWord_length (s 0) (s 1) false
  simp [s₅,s₄,s₃,s₂,s₁,subFinish] at *
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage

lemma bitNat_le_one (x : Bool) : bitNat x ≤ 1 := by cases x <;> decide

/-- Subtract when possible, otherwise retain the normalized original word. -/
def reduceWord (a b : List Bool) : List Bool × Bool :=
  let r := subtractWord a b false
  if r.2 then (normalizeWord a,false) else (normalizeWord r.1,true)

lemma normalize_length_of_lt (a : List Bool) (B : ℕ) (h : wordValue a < 2^B) :
    (normalizeWord a).length ≤ B := by
  rw [normalizeWord_length,Nat.size_le]
  exact h

lemma reduceWord_spec (a b : List Bool) (_hb : 0<wordValue b)
    (ha : wordValue a < 2*wordValue b) :
    wordValue (reduceWord a b).1 < wordValue b ∧
    wordValue (reduceWord a b).1+bitNat (reduceWord a b).2*wordValue b = wordValue a ∧
    (reduceWord a b).1.length ≤ b.length := by
  by_cases hl : wordValue a < wordValue b
  · have hc := (subtractWord_borrow a b).mpr hl
    simp only [reduceWord,hc,ite_true,normalizeWord_value,bitNat_false,zero_mul,add_zero,true_and]
    exact ⟨hl,normalize_length_of_lt a b.length (hl.trans (wordValue_lt b))⟩
  · obtain ⟨hc,hv⟩ := subtractWord_nonnegative (Nat.le_of_not_gt hl)
    have hs : wordValue (subtractWord a b false).1 < wordValue b := by omega
    simp only [reduceWord,hc,Bool.false_eq_true,ite_false,normalizeWord_value]
    refine ⟨hs,?_,normalize_length_of_lt _ _ (hs.trans (wordValue_lt b))⟩
    simp only [bitNat,ite_true,one_mul]
    omega

/-- Long division, scanning the original numerator most-significant-bit first.
The quotient and remainder registers remain ordinary little-endian words. -/
def divideDigits (b : List Bool) : List Bool → List Bool → List Bool → List Bool × List Bool
  | [],r,q => (r,q)
  | x::l,r,q =>
    let v := reduceWord (x::r) b
    divideDigits b l v.1 (v.2::q)

lemma divideDigits_spec (b l r q : List Bool) (hb : 0<wordValue b) (hr : wordValue r<wordValue b) :
    wordValue (divideDigits b l r q).1 < wordValue b ∧
    wordValue (divideDigits b l r q).2*wordValue b+wordValue (divideDigits b l r q).1 =
      (wordValue q*wordValue b+wordValue r)*2^l.length+wordValue l.reverse ∧
    (divideDigits b l r q).2.length = q.length+l.length ∧
    (divideDigits b l r q).1.length ≤ max r.length b.length := by
  induction l generalizing r q with
  | nil => simp [divideDigits,hr]
  | cons x l ih =>
    have hx := bitNat_le_one x
    have hc : wordValue (x::r) < 2*wordValue b := by rw [wordValue_bit]; omega
    obtain ⟨hv,he,hlen⟩ := reduceWord_spec (x::r) b hb hc
    obtain ⟨hv',he',hq',hl'⟩ := ih (reduceWord (x::r) b).1 ((reduceWord (x::r) b).2::q) hv
    refine ⟨hv',?_,?_,?_⟩
    · rw [wordValue_bit] at he he'
      simp only [divideDigits,List.length_cons]
      rw [he',List.reverse_cons,wordValue_append,wordValue_bit,wordValue_nil,mul_zero,add_zero,
        List.length_reverse]
      simp only [pow_succ]
      linear_combination (2^l.length)*he
    · simpa [divideDigits,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq'
    · exact hl'.trans (max_le (hlen.trans (Nat.le_max_right _ _)) (Nat.le_max_right _ _))

lemma divideDigits_quotient_remainder (a b : List Bool) (hb : 0<wordValue b) :
    wordValue (divideDigits b a.reverse [] []).1 = wordValue a % wordValue b ∧
    wordValue (divideDigits b a.reverse [] []).2 = wordValue a / wordValue b := by
  obtain ⟨hr,he,_,_⟩ := divideDigits_spec b a.reverse [] [] hb (by simpa [wordValue] using hb)
  simp [wordValue] at he
  have hm := congrArg (fun k => k % wordValue b) he
  simp [Nat.add_mod,Nat.mod_eq_of_lt hr] at hm
  refine ⟨hm,?_⟩
  symm
  exact Nat.div_eq_of_lt_le (by omega) (by nlinarith only [he,hr])

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Rename every register occurring in a finite stack program. -/
def Program.rename (f : K → L) : Program K → Program L
  | .skip => .skip
  | .push k b => .push (f k) b
  | .drop k => .drop (f k)
  | .transfer a b => .transfer (f a) (f b)
  | .seq a b => .seq (a.rename f) (b.rename f)
  | .branch k a b c => .branch (f k) (a.rename f) (b.rename f) (c.rename f)
  | .loop k a => .loop (f k) (a.rename f)

lemma extend_update_store (f : K → L) (hf : Injective f) (s : Store K) (S : Store L)
    (k : K) (w : List Bool) :
    extend f (update s k w) S = update (extend f s S) (f k) w := by
  classical
  funext l
  by_cases h : ∃ a, f a = l
  · obtain ⟨a,rfl⟩ := h
    by_cases ha : a=k
    · subst a; simp [hf.extend_apply]
    · have hfa : f a ≠ f k := fun h => ha (hf h)
      simp [hf.extend_apply,ha,hfa]
  · have hfk : l ≠ f k := fun he => h ⟨k,he.symm⟩
    simp [extend_apply' _ _ _ h,hfk]

lemma extend_transfer_store (f : K → L) (hf : Injective f) (s : Store K) (S : Store L)
    (a b : K) :
    extend f (transfer a b s) S = transfer (f a) (f b) (extend f s S) := by
  classical
  simp only [transfer,hf.extend_apply]
  cases he : (s a).head? with
  | none => rfl
  | some x =>
    rw [extend_update_store f hf,extend_update_store f hf]
    congr 1
    rw [←extend_update_store f hf,hf.extend_apply]

/-- Uniform register allocation: renaming injectively never changes time and
preserves every register outside its finite image. -/
theorem Eval.rename {p : Program K} {s v : Store K} {t : ℕ} (h : Eval p s v t)
    (f : K → L) (hf : Injective f) (S : Store L) :
    Eval (p.rename f) (extend f s S) (extend f v S) t := by
  classical
  induction h with
  | skip s => exact Eval.skip _
  | push k b s =>
    simpa [Program.rename,extend_update_store f hf,hf.extend_apply] using
      Eval.push (f k) b (extend f s S)
  | drop k s =>
    simpa [Program.rename,extend_update_store f hf,hf.extend_apply] using
      Eval.drop (f k) (extend f s S)
  | transfer a b s =>
    simpa [Program.rename,extend_transfer_store f hf] using Eval.transfer (f a) (f b) (extend f s S)
  | seq h1 h2 ih1 ih2 => exact Eval.seq ih1 ih2
  | branchNone he hh ih => exact Eval.branchNone (by simpa only [hf.extend_apply] using he) ih
  | branchFalse he hh ih => exact Eval.branchFalse (by simpa only [hf.extend_apply] using he) ih
  | branchTrue he hh ih => exact Eval.branchTrue (by simpa only [hf.extend_apply] using he) ih
  | whileNil he => exact Eval.whileNil (by simpa only [hf.extend_apply] using he)
  | whileCons he h1 h2 ih1 ih2 =>
    exact Eval.whileCons (by simpa only [hf.extend_apply] using
      he) ih1 ih2

lemma extend_pull_store {K L : Type}
  (f : K → L) (hf : Function.Injective f) (S : RationalHitting.StackLanguage.Store L) :
  Function.extend f (fun k => S (f k)) S = S := by
  classical
  funext l
  by_cases h : ∃ a, f a = l
  · obtain ⟨a,rfl⟩ := h; exact hf.extend_apply ..
  · exact extend_apply' _ _ _ h

lemma eval_rename_from (f : K → L) (hf : Injective f) (S : Store L)
    {p : Program K} {v : Store K} {t : ℕ} (h : Eval p (fun k => S (f k)) v t) :
    Eval (p.rename f) S (extend f v S) t := by
  simpa only [extend_pull_store f hf S] using h.rename f hf S

end RationalHitting.StackLanguage

end Complexity
