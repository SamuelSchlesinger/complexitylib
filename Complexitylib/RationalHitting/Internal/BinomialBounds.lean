/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryBinomial

/-!
# Rational hitting lists: binomial bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinomialBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage.Binomial
open Function

/-- Compute the three factorials in the binomial formula. -/
def allFactors : Program (Fin 18) :=
  .seq (factorBlock 14 10) (.seq (factorBlock 15 11) (factorBlock 12 16))
/-- The register store containing the three computed factorials. -/
def factored (n k : ℕ) : Store (Fin 18) :=
  update (update (update (prepared n k) 10 n.factorial.bits) 11 k.factorial.bits) 16
    (n-k).factorial.bits

lemma eval_allFactors (n k : ℕ) :
    ∃ t≤factorCost n 0+factorCost k 0+factorCost (n-k) 0+2,
      Eval allFactors (prepared n k) (factored n k) t := by
  let u := update (prepared n k) 10 n.factorial.bits
  let v := update u 11 k.factorial.bits
  obtain ⟨t1,ht1,h1⟩ := eval_factorBlock 14 10 (by decide) (by decide) (by decide) (by decide)
    (prepared n k) (lowEmpty_prepared n k) (by simp [prepared,input])
  have e1 : Eval (factorBlock 14 10) (prepared n k) u t1 := by simpa [u,prepared,input] using h1
  have hu : LowEmpty u := lowEmpty_update _ (lowEmpty_prepared n k) 10 (by decide) _
  obtain ⟨t2,ht2,h2⟩ := eval_factorBlock 15 11 (by decide) (by decide) (by decide) (by decide)
    u hu (by simp [u,prepared,input])
  have e2 : Eval (factorBlock 15 11) u v t2 := by simpa [v,u,prepared,input] using h2
  have hv : LowEmpty v := lowEmpty_update _ hu 11 (by decide) _
  obtain ⟨t3,ht3,h3⟩ := eval_factorBlock 12 16 (by decide) (by decide) (by decide) (by decide)
    v hv (by simp [v,u,prepared,input])
  have e3 : Eval (factorBlock 12 16) v (factored n k) t3 := by
    simpa [factored,v,u,prepared,
      input] using h3
  refine ⟨_,?_,Eval.seq e1 (Eval.seq e2 e3)⟩
  simp [v,u,prepared,input] at ht1 ht2 ht3
  omega

/-- Binary multiplication embedded in the binomial register bank. -/
def cleanMul : Program (Fin 18) := (multiplyClean.rename factorMul).rename arith
lemma eval_cleanMul (s : Store (Fin 18))
    (hs : ∀ j : Fin 18, 2≤j.val → j.val<8 → s j=[])
    (B : ℕ) (h0 : (s 0).length≤B) (h1 : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval cleanMul s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,he⟩ := eval_factorMul (fun j => s (arith j))
    (fun j hj hj' => hs (arith j) hj hj') B h0 h1
  have hh := eval_rename_from arith arith.injective s he
  simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective] at hh
  exact ⟨t,ht,hh⟩

lemma eval_cleanQuotient (s : Store (Fin 18))
    (hs : GcdScratch (fun j => s (arith j))) (hd : 0<wordValue (s 5))
    (B : ℕ) (h0 : (s 0).length≤B) (h5 : (s 5).length≤B) :
    ∃ t≤400*(B+1)^2, Eval (quotient.rename arith) s
      (update s 0 (wordValue (s 0)/wordValue (s 5)).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_quotient (fun j => s (arith j)) hs hd B h0 h5
  have hh := eval_rename_from arith arith.injective s he
  simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective] at hh
  exact ⟨t,ht,hh⟩

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

lemma eval_copy_clean {a b : Fin 18} (hab : a≠b) (ha : a≠17) (hb : b≠17)
    (s : Store (Fin 18)) (h17 : s 17=[]) :
    Eval (copy a b 17) s (update s b (s a)) (7*(s a).length+2*(s b).length+7) := by
  have hh := eval_copy hab ha hb s
  have heq : update (update s b (s a)) 17 []=update s b (s a) := by
    funext j; by_cases hj : j=b <;> by_cases hj17 : j=17 <;> simp_all
  rw [heq] at hh
  simpa [h17] using hh

/-- Form the factorial quotient giving the binomial coefficient. -/
def ratio : Program (Fin 18) :=
  .seq (copy 11 0 17) (.seq (copy 16 1 17) (.seq cleanMul
    (.seq (copy 0 5 17) (.seq (copy 10 0 17) (.seq (quotient.rename arith)
      (.seq (clear 5) (.seq (clear 10) (.seq (clear 11) (.seq (clear 12) (clear 16))))))))))

/-- A bound on the combined binary widths of the three factorials. -/
def width (n k : ℕ) : ℕ := (1+n*(n+1))+(1+k*(k+1))+(1+(n-k)*((n-k)+1))
/-- Polynomial stack-step bound for the factorial quotient. -/
def ratioCost (n k : ℕ) : ℕ :=
  200*(width n k+1)^4+400*(width n k+1)^2+100*width n k+10*(n+k)+100

lemma eval_ratio (n k : ℕ) (hk : k≤n) :
    ∃ t≤ratioCost n k, Eval ratio (factored n k)
      (update (input n k) 0 (n.choose k).bits) t := by
  let a := n.factorial
  let b := k.factorial
  let c := (n-k).factorial
  let s := factored n k
  let u1 := update s 0 b.bits
  let u2 := update u1 1 c.bits
  let u3 := update (update u2 0 (b*c).bits) 1 []
  let u4 := update u3 5 (b*c).bits
  let u5 := update u4 0 a.bits
  let u6 := update u5 0 (a/(b*c)).bits
  let u7 := update u6 5 []
  let u8 := update u7 10 []
  let u9 := update u8 11 []
  let u10 := update u9 12 []
  have ha : a.bits.length≤1+n*(n+1) := factorial_bits_length n
  have hb : b.bits.length≤1+k*(k+1) := factorial_bits_length k
  have hc : c.bits.length≤1+(n-k)*((n-k)+1) := factorial_bits_length (n-k)
  have hp : (b*c).bits.length≤b.bits.length+c.bits.length := by
    simpa using product_bits_length b.bits c.bits
  have hal : a.bits.length≤width n k := by unfold width;omega
  have hbl : b.bits.length≤width n k := by unfold width;omega
  have hcl : c.bits.length≤width n k := by unfold width;omega
  have hpl : (b*c).bits.length≤width n k := by unfold width;omega
  have e1 : Eval (copy 11 0 17) s u1 (7*b.bits.length+7) := by
    simpa [u1,s,factored,prepared,input,b] using
      eval_copy_clean (a:=(11 : Fin 18)) (b:=0) (by decide) (by decide) (by decide) s (by simp
        [s,factored,prepared,input])
  have e2 : Eval (copy 16 1 17) u1 u2 (7*c.bits.length+7) := by
    simpa [u2,u1,s,factored,prepared,input,c] using
      eval_copy_clean (a:=(16 : Fin 18)) (b:=1) (by decide) (by decide) (by decide) u1 (by simp
        [u1,s,factored,prepared,input])
  have hf : ∀ j : Fin 18, 2≤j.val → j.val<8 → u2 j=[] := by
    intro j hj hj'
    simp [u2,u1,s,factored,prepared,input,show j≠0 by omega,show j≠1 by omega,
      show j≠10 by omega,show j≠11 by omega,show j≠12 by omega,show j≠13 by omega,
      show j≠14 by omega,show j≠15 by omega,show j≠16 by omega]
  obtain ⟨t3,ht3,h3⟩ := eval_cleanMul u2 hf (width n k)
    (by simpa [u2,u1] using hbl) (by simpa [u2] using hcl)
  have e3 : Eval cleanMul u2 u3 t3 := by simpa [u3,u2,u1] using h3
  have e4 : Eval (copy 0 5 17) u3 u4 (7*(b*c).bits.length+7) := by
    simpa [u4,u3,u2,u1,s,factored,prepared,input] using
      eval_copy_clean (a:=(0 : Fin 18)) (b:=5) (by decide) (by decide) (by decide) u3 (by simp
        [u3,u2,u1,s,factored,prepared,input])
  have e5 : Eval (copy 10 0 17) u4 u5 (7*a.bits.length+2*(b*c).bits.length+7) := by
    simpa [u5,u4,u3,u2,u1,s,factored,prepared,input,a] using
      eval_copy_clean (a:=(10 : Fin 18)) (b:=0) (by decide) (by decide) (by decide) u4 (by simp
        [u4,u3,u2,u1,s,factored,prepared,input])
  have hg : GcdScratch (fun j => u5 (arith j)) := by
    change (u5 1=[] ∧ u5 2=[] ∧ u5 3=[] ∧ u5 4=[] ∧ u5 8=[] ∧ u5 9=[]) ∧ u5 6=[] ∧ u5 7=[]
    simp [u5,u4,u3,u2,u1,s,factored,prepared,input]
  obtain ⟨t6,ht6,h6⟩ := eval_cleanQuotient u5 hg (by simp [u5,u4,b,c,Nat.factorial_pos])
    (width n k) (by simpa [u5] using hal) (by simpa [u5,u4] using hpl)
  have e6 : Eval (quotient.rename arith) u5 u6 t6 := by simpa [u6,u5,u4] using h6
  have e7 : Eval (clear 5) u6 u7 (2*(b*c).bits.length+1) := by
    simpa [u7,u6,u5,u4] using
      eval_clear (5 : Fin 18) u6
  have e8 : Eval (clear 10) u7 u8 (2*a.bits.length+1) := by
    simpa [u8,u7,u6,u5,u4,u3,u2,u1,s,
      factored,a] using eval_clear (10 : Fin 18) u7
  have e9 : Eval (clear 11) u8 u9 (2*b.bits.length+1) := by
    simpa [u9,u8,u7,u6,u5,u4,u3,u2,u1,s,
      factored,b] using eval_clear (11 : Fin 18) u8
  have e10 : Eval (clear 12) u9 u10 (2*(n-k)+1) := by
    simpa [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,
      factored,prepared] using eval_clear (12 : Fin 18) u9
  have e11 := eval_clear (16 : Fin 18) u10
  have heq : update u10 16 []=update (input n k) 0 (n.choose k).bits := by
    funext j; fin_cases j <;>
      simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,prepared,input,a,b,c,
        Nat.choose_eq_factorial_div_factorial hk,Nat.sub_eq_zero_of_le hk]
  rw [heq] at e11
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 e11)))))))))
  refine ⟨_,?_,hh⟩
  have hlen : u10 16=c.bits := by simp [u10,u9,u8,u7,u6,u5,u4,u3,u2,u1,s,factored,c]
  rw [hlen]
  unfold ratioCost
  omega

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

/-- Compute the factorials and their quotient. -/
def compute : Program (Fin 18) := .seq allFactors ratio
/-- Clear the difference and underflow registers in the zero-result case. -/
def discard : Program (Fin 18) := .seq (clear 12) (clear 13)
/-- Compute a binomial coefficient, including the out-of-range zero case. -/
def choose : Program (Fin 18) := .seq prepare (.branch 13 compute discard discard)
/-- Polynomial stack-step bound for the complete binomial program. -/
def cost (n k : ℕ) : ℕ := factorCost n 0+factorCost k 0+factorCost (n-k) 0+ratioCost n
    k+20*(n+k)+100

/-- A single finite program for every binomial coefficient; the inputs are
unary counters, not a factorial oracle. The out-of-range case is tested by the
actual stack guard. -/
theorem eval_choose (n k : ℕ) : ∃ t≤cost n k,
    Eval choose (input n k) (update (input n k) 0 (n.choose k).bits) t := by
  have ep := eval_prepare n k
  by_cases hk : k≤n
  · obtain ⟨t1,ht1,h1⟩ := eval_allFactors n k
    obtain ⟨t2,ht2,h2⟩ := eval_ratio n k hk
    have ec : Eval compute (prepared n k) (update (input n k) 0 (n.choose k).bits) (1+t1+t2) :=
      Eval.seq h1 h2
    have hg : prepared n k 13=[] := by simp [prepared,Nat.sub_eq_zero_of_le hk]
    have hb : Eval (.branch 13 compute discard discard) (prepared n k)
        (update (input n k) 0 (n.choose k).bits) (1+(1+t1+t2)) := Eval.branchNone hg ec
    refine ⟨_,?_,Eval.seq ep hb⟩
    unfold cost;omega
  · have hlt : n<k := Nat.lt_of_not_ge hk
    let u := update (prepared n k) 12 []
    have e1 : Eval (clear 12) (prepared n k) u 1 := by
      simpa [u,prepared,Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)] using eval_clear (12 : Fin 18)
        (prepared n k)
    have e2 := eval_clear (13 : Fin 18) u
    have hx : update u 13 []=update (input n k) 0 (n.choose k).bits := by
      funext j; fin_cases j <;> simp [u,prepared,input,Nat.choose_eq_zero_of_lt hlt]
    rw [hx] at e2
    have ec : Eval discard (prepared n k) (update (input n k) 0 (n.choose k).bits) (2*(k-n)+3) := by
      convert Eval.seq e1 e2 using 1 <;> simp [discard,u,prepared] ; omega
    have hp : 0<k-n := Nat.sub_pos_of_lt hlt
    obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    have hg : prepared n k 13=true::List.replicate l true := by
      simp [prepared,hl,
        List.replicate_succ]
    have hb : Eval (.branch 13 compute discard discard) (prepared n k)
        (update (input n k) 0 (n.choose k).bits) (1+(2*(k-n)+3)) := Eval.branchTrue hg ec
    refine ⟨_,?_,Eval.seq ep hb⟩
    unfold cost;omega

lemma factorCost_bound (j R : ℕ) (hR : 1≤R) (hj : j≤R) : factorCost j 0≤77000*R^10 := by
  have hj2 : j*(1+j)≤R*(1+R) := Nat.mul_le_mul hj (by omega)
  have hb : 1+j*(1+j)+1≤4*R^2 := by nlinarith
  have hb4 := Nat.pow_le_pow_left hb 4
  have hw := Nat.mul_le_mul hj (Nat.add_le_add_right (Nat.mul_le_mul_left 300 hb4) 1)
  have hm : j*(300*(1+j*(1+j)+1)^4+1)≤76800*R^9+R := by
    calc
      _ ≤ R*(300*((4*R^2)^4)+1) := hw
      _ = _ := by ring
  have hr : 9*j+9*(1+j*(j+1))+30≤100*R^2 := by nlinarith
  have hpow2 : R^2≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hpow9 : R^9≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hpow1 : R≤R^10 := by simpa using Nat.pow_le_pow_right hR (show 1≤10 by decide)
  unfold factorCost factorialCost
  nlinarith only [hm,hr,hpow2,hpow9,hpow1]

lemma width_bound (n k R : ℕ) (hR : 1≤R) (hn : n≤R) (hk : k≤R) : width n k≤9*R^2 := by
  have hf (j : ℕ) (hj : j≤R) : 1+j*(j+1)≤3*R^2 := by
    have hh := Nat.mul_le_mul hj (Nat.add_le_add_right hj 1)
    nlinarith
  have h1 := hf n hn
  have h2 := hf k hk
  have h3 := hf (n-k) ((Nat.sub_le ..).trans hn)
  unfold width;omega

lemma cost_bound (n k : ℕ) : cost n k≤3000000*(n+k+1)^10 := by
  let R := n+k+1
  have hR : 1≤R := by dsimp [R];omega
  have hn : n≤R := by dsimp [R];omega
  have hk : k≤R := by dsimp [R];omega
  have hf1 := factorCost_bound n R hR hn
  have hf2 := factorCost_bound k R hR hk
  have hf3 := factorCost_bound (n-k) R hR ((Nat.sub_le ..).trans hn)
  have hw := width_bound n k R hR hn hk
  have hw' : width n k+1≤10*R^2 := by nlinarith
  have h4 : (width n k+1)^4≤10000*R^8 := by
    calc
      _ ≤ (10*R^2)^4 := Nat.pow_le_pow_left hw' 4
      _ = _ := by ring
  have h2 : (width n k+1)^2≤100*R^4 := by
    calc
      _ ≤ (10*R^2)^2 := Nat.pow_le_pow_left hw' 2
      _ = _ := by ring
  have hp8 : R^8≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp4 : R^4≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp2 : R^2≤R^10 := Nat.pow_le_pow_right hR (by decide)
  have hp1 : R≤R^10 := by simpa using Nat.pow_le_pow_right hR (show 1≤10 by decide)
  have hp0 : 1≤R^10 := Nat.one_le_pow _ _ hR
  have hnk : n+k≤R := by dsimp [R];omega
  change cost n k≤3000000*R^10
  unfold cost ratioCost
  nlinarith only [hf1,hf2,hf3,hw,h4,h2,hp8,hp4,hp2,hp1,hp0,hnk]

/-- The exact binary binomial coefficient with a fixed polynomial bound
in the unary input length. -/

theorem eval_choose_polynomial (n k : ℕ) : ∃ t≤3000000*(n+k+1)^10,
    Eval choose (input n k) (update (input n k) 0 (n.choose k).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_choose n k
  exact ⟨t,ht.trans (cost_bound n k),he⟩

end RationalHitting.StackLanguage.Binomial

end Complexity
