/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryGcd

/-!
# Rational hitting lists: binary factorial

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryFactorial.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- One Euclidean algorithm step on binary stack words. -/
def gcdBody : Program (Fin 10) := .seq divide (.seq (copy 5 6 9)
  (.seq (copy 0 5 9) (.seq (copy 6 0 9) (.seq (clear 6) (clear 7)))))
/-- Repeat Euclidean reduction until the second operand is zero. -/
def gcdLoop : Program (Fin 10) := .loop 5 gcdBody

/-- The scratch-register emptiness invariant for the Euclidean algorithm. -/
def GcdScratch (s : Store (Fin 10)) : Prop := DivScratch s ∧ s 6=[] ∧ s 7=[]

lemma eval_gcdBody (s : Store (Fin 10)) (hs : GcdScratch s) (hb : 0<wordValue (s 5))
    (B : ℕ) (h0 : (s 0).length ≤ B) (h5 : (s 5).length ≤ B) :
    ∃ t ≤ 500*(B+1)^2,
      Eval gcdBody s (update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits) t := by
  obtain ⟨hd,h6,h7⟩ := hs
  obtain ⟨t,ht,he⟩ := eval_divide s hd h6 h7 hb
  let r := (wordValue (s 0)%wordValue (s 5)).bits
  let q := (wordValue (s 0)/wordValue (s 5)).bits
  let u := update (update s 0 r) 7 q
  let v := update (update u 6 (s 5)) 9 []
  let w := update (update v 5 r) 9 []
  let z := update (update w 0 (s 5)) 9 []
  have h9 := hd.2.2.2.2.2
  have hc1 : Eval (copy 5 6 9) u v (7*(s 5).length+7) := by
    simpa [v,u,h6,h9] using eval_copy (a := (5 : Fin 10)) (b := 6) (tmp := 9)
      (by decide) (by decide) (by decide) u
  have hc2 : Eval (copy 0 5 9) v w (7*r.length+2*(s 5).length+7) := by
    simpa [w,v,u] using eval_copy (a := (0 : Fin 10)) (b := 5) (tmp := 9)
      (by decide) (by decide) (by decide) v
  have hc3 : Eval (copy 6 0 9) w z (7*(s 5).length+2*r.length+7) := by
    simpa [z,w,v,u] using eval_copy (a := (6 : Fin 10)) (b := 0) (tmp := 9)
      (by decide) (by decide) (by decide) w
  have hclear6 : Eval (clear 6) z (update z 6 []) (2*(s 5).length+1) := by
    simpa [z,w,v,u] using eval_clear (6 : Fin 10) z
  have hclear7 : Eval (clear 7) (update z 6 []) (update (update z 6 []) 7 []) (2*q.length+1) := by
    simpa [z,w,v,u] using eval_clear (7 : Fin 10) (update z 6 [])
  have h := Eval.seq he (Eval.seq hc1 (Eval.seq hc2 (Eval.seq hc3 (Eval.seq hclear6 hclear7))))
  have heq : update (update z 6 []) 7 [] = update (update s 0 (s 5)) 5 r := by
    funext k; fin_cases k <;> simp [z,w,v,u,h6,h7,h9]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hrlen : r.length ≤ (s 5).length := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
  have hqlen : q.length ≤ (s 0).length := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right h0 1) (Nat.add_le_add_right h5 1)
  nlinarith

/-- Euclid's product is halved at every ordered step. -/
lemma gcd_product_halving {a b : ℕ} (ha : 0<a) (hab : a≤b) :
    2*(a*(b%a)) ≤ a*b := by
  have hr := Nat.mod_lt b ha
  have hq : 1 ≤ b/a := (Nat.one_le_div_iff ha).mpr hab
  have hid := Nat.mod_add_div b a
  have hmul := Nat.mul_le_mul_left a hq
  have hhalf : 2*(b%a) ≤ b := by omega
  nlinarith

lemma eval_gcdLoop_ordered (f : ℕ) (s : Store (Fin 10)) (hs : GcdScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (hab : wordValue (s 5)≤wordValue (s 0))
    (hf : wordValue (s 0)*wordValue (s 5)<2^f)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ f*(500*(B+1)^2+1)+1,
      Eval gcdLoop s (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5
        []) t := by
  induction f generalizing s with
  | zero =>
    have hz : wordValue (s 5)=0 := by simp only [pow_zero] at hf; nlinarith
    have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
    have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
      simp [hz,hcan0,←he5]
    refine ⟨1,by simp,?_⟩
    rw [heq]
    exact Eval.whileNil he5
  | succ f ih =>
    by_cases hz : wordValue (s 5)=0
    · have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
      have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
        simp [hz,hcan0,←he5]
      refine ⟨1,by omega,?_⟩
      rw [heq]
      exact Eval.whileNil he5
    · have hb : 0<wordValue (s 5) := Nat.pos_of_ne_zero hz
      let u := update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits
      obtain ⟨t,ht,he⟩ := eval_gcdBody s hs hb B h0 h5
      have hu : GcdScratch u := by simpa [GcdScratch,DivScratch,u] using hs
      have hu0 : (wordValue (u 0)).bits=u 0 := by simpa [u] using hcan5
      have hu5 : (wordValue (u 5)).bits=u 5 := by simp [u]
      have hule : wordValue (u 5)≤wordValue (u 0) := by
        simpa [u] using Nat.le_of_lt (Nat.mod_lt
          (wordValue (s 0)) hb)
      have huf : wordValue (u 0)*wordValue (u 5)<2^f := by
        have hh := gcd_product_halving hb hab
        simp only [pow_succ] at hf
        simp [u]
        nlinarith
      have hulen : (u 5).length≤B := by
        simp only [u,update_self]
        apply le_trans _ h5
        rw [Nat.size_eq_bits_len,Nat.size_le]
        exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
      obtain ⟨v,hv,hl⟩ := ih u hu hu0 hu5 hule huf (by simpa [u] using h5) hulen
      have hnz : s 5≠[] := by intro hh; simp [hh] at hb
      have h := Eval.whileCons hnz he hl
      have hg : Nat.gcd (wordValue (s 5)) (wordValue (s 0)%wordValue (s 5)) =
          Nat.gcd (wordValue (s 0)) (wordValue (s 5)) := by
        calc _ = Nat.gcd (wordValue (s 0)%wordValue (s 5)) (wordValue (s 5)) := Nat.gcd_comm ..
             _ = Nat.gcd (wordValue (s 5)) (wordValue (s 0)) := (Nat.gcd_rec _ _).symm
             _ = _ := Nat.gcd_comm ..
      have heq : update (update u 0 (Nat.gcd (wordValue (u 0)) (wordValue (u 5))).bits) 5 [] =
          update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 [] := by
        simp [u,hg,update_idem,update_comm (show (0 : Fin 10) ≠ 5 by decide)]
      rw [heq] at h
      exact ⟨1+t+v,by nlinarith,h⟩


/-- No value-sized fuel: the compiler executes an ordinary while loop, and
Euclid's product-halving supplies a bound linear in the input bit lengths. -/
lemma eval_gcdLoop (s : Store (Fin 10)) (hs : GcdScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ (2*B+1)*(500*(B+1)^2+1)+1,
      Eval gcdLoop s (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5
        []) t := by
  by_cases hz : wordValue (s 5)=0
  · have he5 : s 5=[] := by rw [←hcan5,hz]; rfl
    have heq : update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []=s := by
      simp [hz,hcan0,←he5]
    refine ⟨1,by omega,?_⟩
    rw [heq]
    exact Eval.whileNil he5
  · have hb : 0<wordValue (s 5) := Nat.pos_of_ne_zero hz
    let u := update (update s 0 (s 5)) 5 (wordValue (s 0)%wordValue (s 5)).bits
    obtain ⟨t,ht,he⟩ := eval_gcdBody s hs hb B h0 h5
    have hu : GcdScratch u := by simpa [GcdScratch,DivScratch,u] using hs
    have hu0 : (wordValue (u 0)).bits=u 0 := by simpa [u] using hcan5
    have hu5 : (wordValue (u 5)).bits=u 5 := by simp [u]
    have hule : wordValue (u 5)≤wordValue (u 0) := by
      simpa [u] using Nat.le_of_lt (Nat.mod_lt
        (wordValue (s 0)) hb)
    have hu0len : (u 0).length≤B := by simpa [u] using h5
    have hu5len : (u 5).length≤B := by
      simp only [u,update_self]
      apply le_trans _ h5
      rw [Nat.size_eq_bits_len,Nat.size_le]
      exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
    have hf : wordValue (u 0)*wordValue (u 5)<2^(2*B) := by
      have hlt0 := (wordValue_lt (u 0)).trans_le (Nat.pow_le_pow_right (by decide) hu0len)
      have hlt5 := (wordValue_lt (u 5)).trans_le (Nat.pow_le_pow_right (by decide) hu5len)
      rw [two_mul,pow_add]
      exact mul_lt_mul'' hlt0 hlt5 (Nat.zero_le _) (Nat.zero_le _)
    obtain ⟨v,hv,hl⟩ := eval_gcdLoop_ordered (2*B) u hu hu0 hu5 hule hf B hu0len hu5len
    have hnz : s 5≠[] := by intro hh; simp [hh] at hb
    have h := Eval.whileCons hnz he hl
    have hg : Nat.gcd (wordValue (s 5)) (wordValue (s 0)%wordValue (s 5)) =
        Nat.gcd (wordValue (s 0)) (wordValue (s 5)) := by
      calc _ = Nat.gcd (wordValue (s 0)%wordValue (s 5)) (wordValue (s 5)) := Nat.gcd_comm ..
           _ = Nat.gcd (wordValue (s 5)) (wordValue (s 0)) := (Nat.gcd_rec _ _).symm
           _ = _ := Nat.gcd_comm ..
    have heq : update (update u 0 (Nat.gcd (wordValue (u 0)) (wordValue (u 5))).bits) 5 [] =
        update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 [] := by
      simp [u,hg,update_idem,update_comm (show (0 : Fin 10) ≠ 5 by decide)]
    rw [heq] at h
    exact ⟨1+t+v,by nlinarith,h⟩

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Destructive exact binary quotient, retaining its positive denominator. -/
def quotient : Program (Fin 10) := .seq divide (.seq (copy 7 0 9) (clear 7))

lemma eval_quotient (s : Store (Fin 10)) (hs : GcdScratch s)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 400*(B+1)^2,
      Eval quotient s (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨hd,h6,h7⟩ := hs
  obtain ⟨t,ht,he⟩ := eval_divide s hd h6 h7 hb
  let q := (wordValue (s 0)/wordValue (s 5)).bits
  let r := (wordValue (s 0)%wordValue (s 5)).bits
  let u := update (update s 0 r) 7 q
  let v := update (update u 0 q) 9 []
  have h9 := hd.2.2.2.2.2
  have hc : Eval (copy 7 0 9) u v (7*q.length+2*r.length+7) := by
    simpa [q,r,u,v,h9] using eval_copy (a := (7 : Fin 10)) (b := 0) (tmp := 9)
      (by decide) (by decide) (by decide) u
  have hz : Eval (clear 7) v (update s 0 q) (2*q.length+1) := by
    have hh := eval_clear (7 : Fin 10) v
    have heq : update v 7 []=update s 0 q := by
      funext k; fin_cases k <;> simp [v,u,h7,h9]
    rw [heq] at hh
    simpa [v,u] using hh
  have hbq : q.length≤B := by
    apply le_trans _ h0
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.div_le_self _ _).trans_lt (wordValue_lt _)
  have hbr : r.length≤B := by
    apply le_trans _ h5
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact (Nat.mod_lt _ hb).trans (wordValue_lt _)
  refine ⟨_,?_,Eval.seq he (Eval.seq hc hz)⟩
  have hp := Nat.mul_le_mul h0 h5
  nlinarith

/-- Extra work registers for retaining numerator and denominator through Euclid. -/
def fractionArith : Fin 10 ↪ Fin 12 :=
  Fin.castAddEmb 2

@[simp] lemma fractionArith_val (i : Fin 10) : (fractionArith i).val=i.val := rfl

/-- The clean-register invariant for reducing a rational fraction. -/
def FractionScratch (s : Store (Fin 12)) : Prop :=
  ∀ k : Fin 10, k≠0 → k≠5 → s (fractionArith k)=[]

lemma fractionScratch_gcd (s : Store (Fin 12)) (hs : FractionScratch s) :
    GcdScratch (fun k => s (fractionArith k)) := by
  unfold GcdScratch DivScratch
  exact ⟨⟨hs 1 (by decide) (by decide),hs 2 (by decide) (by decide),
    hs 3 (by decide) (by decide),hs 4 (by decide) (by decide),
    hs 8 (by decide) (by decide),hs 9 (by decide) (by decide)⟩,
    hs 6 (by decide) (by decide),hs 7 (by decide) (by decide)⟩

lemma eval_fractionGcd (s : Store (Fin 12)) (hs : FractionScratch s)
    (hcan0 : (wordValue (s 0)).bits=s 0) (hcan5 : (wordValue (s 5)).bits=s 5)
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ (2*B+1)*(500*(B+1)^2+1)+1,
      Eval (gcdLoop.rename fractionArith) s
        (update (update s 0 (Nat.gcd (wordValue (s 0)) (wordValue (s 5))).bits) 5 []) t := by
  obtain ⟨t,ht,he⟩ := eval_gcdLoop (fun k => s (fractionArith k))
    (fractionScratch_gcd s hs) hcan0 hcan5 B h0 h5
  have hh := eval_rename_from fractionArith fractionArith.injective s he
  simp only [extend_update_store fractionArith fractionArith.injective,
    extend_pull_store fractionArith fractionArith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma eval_fractionQuotient (s : Store (Fin 12)) (hs : FractionScratch s)
    (hb : 0<wordValue (s 5)) (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t ≤ 400*(B+1)^2,
      Eval (quotient.rename fractionArith) s
        (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_quotient (fun k => s (fractionArith k))
    (fractionScratch_gcd s hs) hb B h0 h5
  have hh := eval_rename_from fractionArith fractionArith.injective s he
  simp only [extend_update_store fractionArith fractionArith.injective,
    extend_pull_store fractionArith fractionArith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma fractionScratch_update (s : Store (Fin 12)) (hs : FractionScratch s)
    (i : Fin 12) (hi : i = 0 ∨ i = 5 ∨ 10 ≤ i.val) (w : List Bool) :
    FractionScratch (update s i w) := by
  intro k h0 h5
  have hki : fractionArith k≠i := by
    rcases hi with rfl|rfl|hi
    · intro h; have hh := congrArg Fin.val h; apply h0; apply Fin.ext; exact hh
    · intro h; have hh := congrArg Fin.val h; apply h5; apply Fin.ext; exact hh
    · intro h; have hh := congrArg Fin.val h; simp only [fractionArith_val] at hh; omega
  simp [hki,hs k h0 h5]

end RationalHitting.StackLanguage

end Complexity
