/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryFactorial

/-!
# Rational hitting lists: binary binomial

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryBinomial.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Clean multiplication interface used by the finite rising-product loop. -/
def multiplyClean : Program (Fin 8) :=
  .seq multiply (.seq (clear 0) (.seq (copy 2 0 7) (clear 2)))

lemma eval_multiplyClean (s : Store (Fin 8)) (hf : ∀ k : Fin 8, 2≤k.val → s k=[])
    (B : ℕ) (ha : (s 0).length≤B) (hb : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval multiplyClean s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,hm⟩ := eval_multiply s (hf 2 (by decide)) (fun k hk => hf k (by omega))
  let A := wordValue (s 0)
  let D := wordValue (s 1)
  let u := update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 []) 2 (A*D).bits
  let v := update u 0 []
  let z := update v 0 (A*D).bits
  have h1 : Eval (clear 0) u v (2*((s 1).length+(s 0).length)+1) := by
    simpa [u,v] using eval_clear (0 : Fin 8) u
  have h2 : Eval (copy 2 0 7) v z (7*(A*D).bits.length+7) := by
    have hh := eval_copy (a:=(2 : Fin 8)) (b:=0) (tmp:=7) (by decide) (by decide) (by decide) v
    have he : update (update v 0 (v 2)) 7 []=z := by
      funext k; fin_cases k <;> simp [u,v,z,hf 7 (by decide)]
    rw [he] at hh
    simpa [u,v,hf 7 (by decide)] using hh
  have h3 := eval_clear (2 : Fin 8) z
  have he : update z 2 []=update (update s 0 (A*D).bits) 1 [] := by
    funext k; fin_cases k <;> simp [z,v,u,hf 2 (by decide)]
  rw [he] at h3
  have hm' : Eval multiply s u t := hm
  have h := Eval.seq hm' (Eval.seq h1 (Eval.seq h2 h3))
  refine ⟨_,?_,h⟩
  have hp : (A*D).bits.length≤2*B := (product_bits_length (s 0) (s 1)).trans (by omega)
  simp [z,v,u] at *
  have h₀ : (s 0).length+(s 1).length≤2*B := by omega
  have h₁ : (s 1).length*((s 0).length+(s 1).length)≤2*B^2 := by nlinarith
  have h₂ : ((s 0).length+(s 1).length)*(7*((s 1).length*((s 0).length+(s 1).length))+34)≤
      2*B*(14*B^2+34) := Nat.mul_le_mul h₀ (by omega)
  have h₃ := Nat.mul_le_mul hb (Nat.add_le_add_right h₂ 23)
  nlinarith only [ht,hp,h₀,h₁,h₃,Nat.zero_le (B^2),Nat.zero_le (B^3)]

/-- Embed the multiplication registers in the factorial register bank. -/
def factorMul : Fin 8 ↪ Fin 10 := Fin.castAddEmb 2

/-- The clean scratch registers used by factorial iteration. -/
def FactorialScratch (s : Store (Fin 10)) : Prop :=
  ∀ k : Fin 10, 1≤k.val → k.val<8 → s k=[]

lemma eval_factorMul (s : Store (Fin 10)) (hf : ∀ k : Fin 10, 2≤k.val → k.val<8 → s k=[])
    (B : ℕ) (ha : (s 0).length≤B) (hb : (s 1).length≤B) :
    ∃ t≤200*(B+1)^4, Eval (multiplyClean.rename factorMul) s
      (update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 []) t := by
  obtain ⟨t,ht,he⟩ := eval_multiplyClean (fun k => s (factorMul k))
    (fun k hk => hf (factorMul k) hk (by exact k.isLt)) B ha hb
  have hh := eval_rename_from factorMul factorMul.injective s he
  have hx : extend factorMul (update (update (fun k => s (factorMul k)) 0
      (wordValue (s 0)*wordValue (s 1)).bits) 1 []) s =
      update (update s 0 (wordValue (s 0)*wordValue (s 1)).bits) 1 [] := by
    simp only [extend_update_store _ factorMul.injective,extend_pull_store _ factorMul.injective]
    rfl
  change Eval (multiplyClean.rename factorMul) s
    (extend factorMul (update (update (fun k => s (factorMul k)) 0
      (wordValue (s 0)*wordValue (s 1)).bits) 1 []) s) t at hh
  rw [hx] at hh
  exact ⟨t,ht,hh⟩

/-- One rising-product step: multiply accumulator by the copied current index,
advance the binary index, and drop one symbol of the unary loop counter. -/
def factorialBody : Program (Fin 10) :=
  .seq (copy 8 1 7) (.seq (multiplyClean.rename factorMul)
    (.seq (increment 8 5 6) (.drop 9)))

lemma eval_factorialBody (s : Store (Fin 10)) (hf : FactorialScratch s)
    (B : ℕ) (h0 : (s 0).length≤B) (h8 : (s 8).length≤B) :
    ∃ t≤300*(B+1)^4, Eval factorialBody s
      (update (update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits)
        8 (incrementWord (s 8))) 9 (s 9).tail) t := by
  let u := update s 1 (s 8)
  let v := update s 0 (wordValue (s 0)*wordValue (s 8)).bits
  let z := update v 8 (incrementWord (s 8))
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
  obtain ⟨t',ht',hi⟩ := eval_increment (a:=(8 : Fin 10)) (tmp:=5) (flag:=6)
    (by decide) (by decide) (by decide) v
  have he' : update (update (update v 8 (incrementWord (v 8))) 5 []) 6 []=z := by
    funext k; fin_cases k <;> simp [z,v,hf 5 (by decide) (by decide),hf 6 (by decide) (by decide)]
  rw [he'] at hi
  have hd : Eval (Program.drop 9) z (update z 9 (s 9).tail) 1 := by
    simpa [z,v] using Eval.drop (9 : Fin 10) z
  have hs := Eval.seq h1 (Eval.seq hh (Eval.seq hi hd))
  refine ⟨_,?_,hs⟩
  simp [v,hf 5 (by decide) (by decide),hf 6 (by decide) (by decide)] at ht'
  nlinarith only [ht,ht',h8,Nat.zero_le (B^2),Nat.zero_le (B^3)]

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

lemma factorial_wordValue_bits (n : ℕ) : wordValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn]
    cases b <;> simp [wordValue,ih,Nat.bit] ; omega

/-- Repeat factorial multiplication over the unary counter. -/
def factorialLoop : Program (Fin 10) := .loop 9 factorialBody

/-- Rising products, with a unary iteration budget obtained from the input.
No scalar factorial operation occurs in this fixed finite program. -/
lemma eval_factorialLoop (n L : ℕ) (s : Store (Fin 10))
    (hf : FactorialScratch s) (hcan : (wordValue (s 0)).bits=s 0)
    (hn : (s 9).length=n)
    (hp : (s 0).length+n*((s 8).length+n)≤L)
    (hi : (s 8).length+n≤L) :
    ∃ t≤n*(300*(L+1)^4+1)+1, ∃ v,
      Eval factorialLoop s v t ∧
      v 0 = (wordValue (s 0)*(wordValue (s 8)).ascFactorial n).bits ∧
      wordValue (v 8)=wordValue (s 8)+n ∧ v 9=[] ∧ FactorialScratch v ∧
      (v 8).length≤(s 8).length+n := by
  induction n generalizing s with
  | zero =>
    have hz : s 9=[] := List.length_eq_zero_iff.mp hn
    exact ⟨1,by simp,s,Eval.whileNil hz,by simpa using hcan.symm,by simp,hz,hf,by simp⟩
  | succ n ih =>
    let u := update (update (update s 0 (wordValue (s 0)*wordValue (s 8)).bits)
      8 (incrementWord (s 8))) 9 (s 9).tail
    obtain ⟨t,ht,he⟩ := eval_factorialBody s hf L (by omega) (by omega)
    have hu : FactorialScratch u := by
      intro k hk hk'; simpa [u,show k≠0 by omega,show k≠8 by omega,show k≠9 by omega]
        using hf k hk hk'
    have hc : (wordValue (u 0)).bits=u 0 := by simp [u]
    have hcnt : (u 9).length=n := by simp [u,List.length_tail,hn]
    have hlen0 : (u 0).length≤(s 0).length+(s 8).length := by
      simpa [u] using product_bits_length (s 0) (s 8)
    have hlen8 : (u 8).length≤(s 8).length+1 := by
      simpa [u] using incrementWord_length (s 8)
    have hpot : (u 0).length+n*((u 8).length+n)≤L := by nlinarith
    have hidx : (u 8).length+n≤L := by omega
    obtain ⟨w,hw,v,hv,hv0,hv8,hv9,hvf,hvl⟩ := ih u hu hc hcnt hpot hidx
    have hstep : Eval factorialBody s u t := he
    have hne : s 9≠[] := by intro h; simp [h] at hn
    refine ⟨1+t+w,by nlinarith,v,Eval.whileCons hne hstep hv,?_,?_,hv9,hvf,?_⟩
    · have hasc := Nat.ascFactorial_mul_ascFactorial (wordValue (s 8)) 1 n
      have hid : wordValue (s 8)*(wordValue (s 8)+1).ascFactorial n =
          (wordValue (s 8)).ascFactorial (n+1) := by
        simpa [Nat.ascFactorial_succ,Nat.add_comm] using hasc
      simpa [u,Nat.mul_assoc,hid] using hv0
    · simpa [u,Nat.add_assoc,Nat.add_comm] using hv8
    · omega

/-- Ordinary factorial on unary n, including zero, with polynomial bit cost.
The two binary registers initially contain 1; no computed value is an input. -/
theorem eval_factorial (n : ℕ) (s : Store (Fin 10))
    (hf : FactorialScratch s) (h0 : s 0=[true]) (h8 : s 8=[true])
    (h9 : (s 9).length=n) :
    ∃ t≤n*(300*(1+n*(1+n)+1)^4+1)+1, ∃ v,
      Eval factorialLoop s v t ∧ v 0=n.factorial.bits ∧
      wordValue (v 8)=n+1 ∧ v 9=[] ∧ FactorialScratch v := by
  obtain ⟨t,ht,v,hv,hv0,hv8,hv9,hvf,hvl⟩ :=
    eval_factorialLoop n (1+n*(1+n)) s hf (by simp [h0,wordValue]) h9
      (by simp [h0,h8]) (by simp [h8]; nlinarith)
  exact ⟨t,ht,v,hv,by simpa [h0,h8,wordValue,Nat.one_ascFactorial] using hv0,
    by simpa [h8,wordValue,Nat.add_comm] using hv8,hv9,hvf⟩

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

lemma factorial_bits_length (n : ℕ) : n.factorial.bits.length≤1+n*(n+1) := by
  have hbits (k : ℕ) : k.bits.length≤k := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    induction k with
    | zero => decide
    | succ k ih => simp only [pow_succ]; nlinarith
  induction n with
  | zero => decide
  | succ n ih =>
    have hm := product_bits_length (n+1).bits n.factorial.bits
    simp only [factorial_wordValue_bits,←Nat.factorial_succ] at hm
    have hn := hbits (n+1)
    nlinarith

/-- Factorial with clean local registers: only the unary counter and output
register are changed. This is the binary subroutine for the Taylor binomials. -/
def factorialCore : Program (Fin 10) :=
  .seq (.push 0 true) (.seq (.push 8 true) (.seq factorialLoop (clear 8)))

lemma eval_factorialCore (s : Store (Fin 10))
    (hs : ∀ k : Fin 10, k.val<9 → s k=[]) :
    ∃ t≤(s 9).length*(300*(1+(s 9).length*(1+(s 9).length)+1)^4+1)+2*(s 9).length+10,
    Eval factorialCore s (update (update s 0 (s 9).length.factorial.bits) 9 []) t := by
  let u := update s 0 [true]
  let v := update u 8 [true]
  have h1 : Eval (Program.push 0 true) s u 1 := by
    simpa [u,hs 0 (by decide)] using Eval.push (0
      : Fin 10) true s
  have h2 : Eval (Program.push 8 true) u v 1 := by
    simpa [v,u,hs 8 (by decide)] using Eval.push
      (8 : Fin 10) true u
  have hf : FactorialScratch v := by
    intro k hk hk'; simp [v,u,show k≠0 by omega,show k≠8 by omega,hs k (by omega)]
  obtain ⟨t,ht,z,hz,hz0,hz8,hz9,hzf,hzl⟩ := eval_factorialLoop (s 9).length
    (1+(s 9).length*(1+(s 9).length)) v hf (by simp [v,u,wordValue])
    (by simp [v,u]) (by simp [v,u]) (by simp [v,u];nlinarith)
  have hz0' : z 0=(s 9).length.factorial.bits := by
    simpa [v,u,wordValue,Nat.one_ascFactorial] using hz0
  have h3 := eval_clear (8 : Fin 10) z
  have heq : update z 8 []=update (update s 0 (s 9).length.factorial.bits) 9 [] := by
    funext k; fin_cases k <;> simp [hz0',hz9,hzf 1 (by decide) (by decide),hzf 2 (by decide) (by
      decide),
      hzf 3 (by decide) (by decide),hzf 4 (by decide) (by decide),hzf 5 (by decide) (by decide),
      hzf 6 (by decide) (by decide),hzf 7 (by decide) (by decide),hs 1 (by decide),hs 2 (by decide),
      hs 3 (by decide),hs 4 (by decide),hs 5 (by decide),hs 6 (by decide),hs 7 (by decide),hs 8
        (by decide)]
  rw [heq] at h3
  have hh := Eval.seq h1 (Eval.seq h2 (Eval.seq hz h3))
  refine ⟨_,?_,hh⟩
  simp [v,u] at ht hzl
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Cancel one unary digit, recording when the minuend is exhausted. -/
def unaryDiffBody (a b flag : K) : Program K :=
  .branch a (.seq (.drop b) (.push flag true))
    (.seq (.drop a) (.drop b)) (.seq (.drop a) (.drop b))
/-- Subtract unary counters while retaining an underflow flag. -/
def unaryDiff (a b flag : K) : Program K := .loop b (unaryDiffBody a b flag)

/-- Variable-length subtraction of unary loop counters. The leftover flag is
nonempty exactly when the second counter exceeded the first. -/
theorem eval_unaryDiff {a b flag : K} (hab : a≠b) (haf : a≠flag) (hbf : b≠flag)
    (s : Store K) :
    Eval (unaryDiff a b flag) s
      (update (update (update s a ((s a).drop (s b).length)) b [])
        flag (List.replicate ((s b).length-(s a).length) true++s flag))
      (5*(s b).length+1) := by
  generalize he : s b=w
  induction w generalizing s with
  | nil =>
    have heq : update (update (update s a (s a)) b []) flag (s flag)=s := by
      simp [←he]
    simp only [List.length_nil,List.drop_zero,Nat.zero_sub,List.replicate_zero,List.nil_append,
      Nat.mul_zero,Nat.zero_add,heq]
    exact Eval.whileNil he
  | cons x w ih =>
    cases ha : s a with
    | nil =>
      let u := update (update s b w) flag (true::s flag)
      have h1 : Eval (Program.drop b) s (update s b w) 1 := by
        simpa [he] using Eval.drop b s
      have h2 : Eval (Program.push flag true) (update s b w) u 1 := by
        simpa [u,Ne.symm hbf] using Eval.push flag true (update s b w)
      have hb : Eval (unaryDiffBody a b flag) s u 4 := Eval.branchNone ha (Eval.seq h1 h2)
      have hu : u b=w := by simp [u,hbf]
      have hl := ih u hu
      have hh := Eval.whileCons (by simp [he]) hb hl
      have heq : update (update (update u a ((u a).drop w.length)) b [])
          flag (List.replicate (w.length-(u a).length) true++u flag) =
          update (update (update s a ((s a).drop (x::w).length)) b [])
          flag (List.replicate ((x::w).length-(s a).length) true++s flag) := by
        funext k; by_cases hk : k=a <;> by_cases hk' : k=b <;> by_cases hk'' : k=flag <;>
          simp_all [u,List.replicate_add,List.append_assoc]
      rw [heq] at hh
      convert hh using 1 <;> simp [unaryDiff,ha] ; ring
    | cons y v =>
      let u := update (update s a v) b w
      have h1 : Eval (Program.drop a) s (update s a v) 1 := by simpa [ha] using Eval.drop a s
      have h2 : Eval (Program.drop b) (update s a v) u 1 := by
        simpa [u,Ne.symm hab,he] using Eval.drop b (update s a v)
      have hb : Eval (unaryDiffBody a b flag) s u 4 := by
        cases y
        · exact Eval.branchFalse ha (Eval.seq h1 h2)
        · exact Eval.branchTrue ha (Eval.seq h1 h2)
      have hu : u b=w := by simp [u]
      have hl := ih u hu
      have hh := Eval.whileCons (by simp [he]) hb hl
      have heq : update (update (update u a ((u a).drop w.length)) b [])
          flag (List.replicate (w.length-(u a).length) true++u flag) =
          update (update (update s a ((s a).drop (x::w).length)) b [])
          flag (List.replicate ((x::w).length-(s a).length) true++s flag) := by
        funext k; by_cases hk : k=a <;> by_cases hk' : k=b <;> by_cases hk'' : k=flag <;>
          simp_all [u]
      rw [heq] at hh
      convert hh using 1 <;> simp [unaryDiff,ha] ; ring

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage.Binomial
open Function

/-- Embed the arithmetic register bank in the binomial-coefficient program. -/
def arith : Fin 10 ↪ Fin 18 := Fin.castAddEmb 8

/-- The lower arithmetic registers are all empty. -/
def LowEmpty (s : Store (Fin 18)) : Prop := ∀ k : Fin 18, k.val<10 → s k=[]
/-- Polynomial bound on the stack steps of factorial computation. -/
def factorialCost (n : ℕ) : ℕ := n*(300*(1+n*(1+n)+1)^4+1)+2*n+10

/-- Compute one factorial and copy its binary result to the chosen register. -/
def factorBlock (a b : Fin 18) : Program (Fin 18) :=
  .seq (copy a 9 17) (.seq (factorialCore.rename arith) (.seq (copy 0 b 17) (clear 0)))

/-- Stack-step bound for a factorial block, including copies and cleanup. -/
def factorCost (n b : ℕ) : ℕ := factorialCost n+7*n+9*(1+n*(n+1))+2*b+20

lemma eval_factorBlock (a b : Fin 18) (ha : 10≤a.val) (hb : 10≤b.val)
    (ha17 : a≠17) (hb17 : b≠17) (s : Store (Fin 18)) (hs : LowEmpty s) (h17 : s 17=[]) :
    ∃ t≤factorCost (s a).length (s b).length,
      Eval (factorBlock a b) s (update s b (s a).length.factorial.bits) t := by
  have ha9 : a≠9 := by omega
  have hb0 : b≠0 := by omega
  let n := (s a).length
  let f := n.factorial.bits
  let u := update s 9 (s a)
  let v := update s 0 f
  let w := update v b f
  have e1 : Eval (copy a 9 17) s u (7*n+7) := by
    have hh := eval_copy (a:=a) (b:=9) (tmp:=17) ha9 ha17 (by decide) s
    have hx : update (update s 9 (s a)) 17 []=u := by
      funext k; by_cases h9 : k=9 <;> by_cases h17k : k=17 <;> simp_all [u]
    rw [hx] at hh
    simpa [n,hs 9 (by decide),h17] using hh
  obtain ⟨t,ht,he⟩ := eval_factorialCore (fun k => u (arith k)) (by
    intro k hk
    have ha9 : arith k≠9 := by
      intro hh
      have hv := congrArg (fun k : Fin 18 => k.val) hh
      change k.val=9 at hv
      omega
    simpa [u,ha9] using hs (arith k) (by change k.val<10;omega))
  have he' := eval_rename_from arith arith.injective u he
  have hx : extend arith (update (update (fun k => u (arith k)) 0
      (u (arith 9)).length.factorial.bits) 9 []) u = v := by
    simp only [extend_update_store _ arith.injective,extend_pull_store _ arith.injective]
    change update (update u 0 (u 9).length.factorial.bits) 9 []=v
    funext k; by_cases h0 : k=0 <;> by_cases h9 : k=9 <;> simp_all [u,v,f,n,hs 9 (by decide)]
  rw [hx] at he'
  have e2 : Eval (factorialCore.rename arith) u v t := he'
  have e3 : Eval (copy 0 b 17) v w (7*f.length+2*(s b).length+7) := by
    have hh := eval_copy (a:=(0 : Fin 18)) (b:=b) (tmp:=17) (Ne.symm hb0) (by decide) hb17 v
    have hx : update (update v b (v 0)) 17 []=w := by
      funext k; by_cases h0 : k=0 <;> by_cases hbk : k=b <;>
        by_cases h17k : k=17 <;> simp_all [v,w]
    rw [hx] at hh
    simpa [v,h17,hb0] using hh
  have e4 := eval_clear (0 : Fin 18) w
  have hx' : update w 0 []=update s b f := by
    funext k; by_cases h0 : k=0 <;> by_cases hbk : k=b <;> simp_all [w,v,hs 0 (by decide)]
  rw [hx'] at e4
  have hh := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 e4))
  refine ⟨_,?_,hh⟩
  change t≤factorialCost n at ht
  have hfl : f.length ≤ 1+n*(n+1) := factorial_bits_length n
  simp only [w,update_of_ne (Ne.symm hb0),v,update_self]
  change _≤factorCost n (s b).length
  unfold factorCost
  omega

end RationalHitting.StackLanguage.Binomial

namespace RationalHitting.StackLanguage.Binomial
open Function

/-- Initial register store containing the two unary binomial arguments. -/
def input (n k : ℕ) : Store (Fin 18) :=
  update (update (fun _ => []) 14 (List.replicate n true)) 15 (List.replicate k true)
/-- The input store extended with both truncated differences of its arguments. -/
def prepared (n k : ℕ) : Store (Fin 18) :=
  update (update (input n k) 12 (List.replicate (n-k) true)) 13 (List.replicate (k-n) true)

/-- Compute the unary difference and underflow flag for binomial evaluation. -/
def prepare : Program (Fin 18) :=
  .seq (copy 14 12 17) (.seq (copy 15 16 17) (unaryDiff 12 16 13))

lemma eval_prepare (n k : ℕ) : Eval prepare (input n k) (prepared n k) (7*n+12*k+17) := by
  let s := input n k
  let u := update s 12 (List.replicate n true)
  let v := update u 16 (List.replicate k true)
  have h1 := eval_copy (a:=(14 : Fin 18)) (b:=12) (tmp:=17) (by decide) (by decide) (by decide) s
  have he1 : update (update s 12 (s 14)) 17 []=u := by
    funext j; fin_cases j <;> simp [s,u,input]
  rw [he1] at h1
  have e1 : Eval (copy 14 12 17) s u (7*n+7) := by simpa [s,input] using h1
  have h2 := eval_copy (a:=(15 : Fin 18)) (b:=16) (tmp:=17) (by decide) (by decide) (by decide) u
  have he2 : update (update u 16 (u 15)) 17 []=v := by
    funext j; fin_cases j <;> simp [v,u,s,input]
  rw [he2] at h2
  have e2 : Eval (copy 15 16 17) u v (7*k+7) := by simpa [u,s,input] using h2
  have h3 := eval_unaryDiff (a:=(12 : Fin 18)) (b:=16) (flag:=13) (by decide) (by decide) (by
    decide) v
  have he3 : update (update (update v 12 ((v 12).drop (v 16).length)) 16 []) 13
      (List.replicate ((v 16).length-(v 12).length) true++v 13)=prepared n k := by
    funext j; fin_cases j <;> simp [prepared,v,u,s,input]
  rw [he3] at h3
  have e3 : Eval (unaryDiff 12 16 13) v (prepared n k) (5*k+1) := by simpa [v,u,s,input] using h3
  convert Eval.seq e1 (Eval.seq e2 e3) using 1 <;> first |rfl |omega

lemma lowEmpty_input (n k : ℕ) : LowEmpty (input n k) := by
  intro j hj
  simp [input,show j≠14 by omega,show j≠15 by omega]
lemma lowEmpty_update (s : Store (Fin 18)) (hs : LowEmpty s) (j : Fin 18) (hj : 10≤j.val) (w :
    List Bool) :
    LowEmpty (update s j w) := by
  intro i hi
  simpa [show i≠j by intro he;subst j;omega] using hs i hi
lemma lowEmpty_prepared (n k : ℕ) : LowEmpty (prepared n k) :=
  lowEmpty_update _ (lowEmpty_update _ (lowEmpty_input n k) 12 (by decide) _) 13 (by decide) _

end RationalHitting.StackLanguage.Binomial

end Complexity
