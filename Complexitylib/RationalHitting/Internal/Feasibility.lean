/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.ProcedureControl

/-!
# Rational hitting lists: feasibility

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Feasibility.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
namespace Feasible
variable {A B C D : Type} {ca : A → List Bool} {cb : B → List Bool}
  {cc : C → List Bool} {cd : D → List Bool} {f : A → B} {g : B → C}

theorem id (ca : A → List Bool) : Feasible ca ca (fun x => x) := ⟨Procedure.identity ca⟩
theorem const (ca : A → List Bool) (cb : B → List Bool) (b : B) :
    Feasible ca cb (fun _ => b) := ⟨Procedure.const ca cb b⟩
theorem comp (hg : Feasible cb cc g) (hf : Feasible ca cb f) : Feasible ca cc (g ∘ f) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨q.comp p⟩
theorem pair {f : A → B} {g : A → C} (hf : Feasible ca cb f) (hg : Feasible ca cc g) :
    Feasible ca (pairCode cb cc) (fun a => (f a,g a)) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨p.pair q⟩
theorem fst (ca : A → List Bool) (cb : B → List Bool) :
    Feasible (pairCode ca cb) ca Prod.fst := ⟨Procedure.fst ca cb⟩
theorem snd (ca : A → List Bool) (cb : B → List Bool) :
    Feasible (pairCode ca cb) cb Prod.snd := ⟨Procedure.snd ca cb⟩
theorem prodMap {f : A → B} {g : C → D} (hf : Feasible ca cb f) (hg : Feasible cc cd g) :
    Feasible (pairCode ca cc) (pairCode cb cd) (Prod.map f g) :=
  (hf.comp (fst ca cc)).pair (hg.comp (snd ca cc))
theorem recode {A' B' : Type} (hf : Feasible ca cb f) (ca' : A' → List Bool)
    (cb' : B' → List Bool) (f' : A' → B') (e : A' → A)
    (hi : ∀ a,ca (e a)=ca' a) (ho : ∀ a,cb (f (e a))=cb' (f' a)) : Feasible ca' cb' f' := by
  obtain ⟨p⟩ := hf; exact ⟨p.recode ca' cb' f' e hi ho⟩
theorem of_eq {g : A → B} (hf : Feasible ca cb f) (h : ∀ a,f a=g a) : Feasible ca cb g := by
  have : f=g := funext h
  simpa only [this] using hf

theorem branch {f g : A → B} (hf : Feasible ca cb f) (hg : Feasible ca cb g) :
    Feasible (pairCode boolCode ca) cb (fun a => if a.1 then f a.2 else g a.2) := by
  obtain ⟨p⟩ := hf; obtain ⟨q⟩ := hg; exact ⟨p.branch q⟩
theorem cond {c : A → Bool} {f g : A → B} (hc : Feasible ca boolCode c)
    (hf : Feasible ca cb f) (hg : Feasible ca cb g) :
    Feasible ca cb (fun a => if c a then f a else g a) :=
  (hf.branch hg).comp (hc.pair (id ca))

theorem iterate {f : A → A} (hf : Feasible ca ca f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (ca (f^[i] a)).length≤Q.eval ((pairCode unaryCode ca (n,a)).length+1)) :
    Feasible (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := by
  obtain ⟨p⟩ := hf; exact ⟨p.iterate Q hQ⟩

theorem appendWord : Feasible (pairCode (fun x => x) (fun x => x)) (fun x => x)
    (fun a : List Bool×List Bool => a.1++a.2) := ⟨Procedure.appendWord⟩
theorem reverseWord : Feasible (fun x => x) (fun x => x) (List.reverse : List Bool → List Bool) :=
  ⟨Procedure.reverseWord⟩

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.TimeBound

/-- A natural power of a polynomial time-bound expression. -/
def power (p : TimeBound) : ℕ → TimeBound
  | 0 => 1
  | n+1 => power p n*p
instance : Pow TimeBound ℕ := ⟨power⟩
@[simp] lemma eval_pow (p : TimeBound) (k n : ℕ) : (p^k).eval n=(p.eval n)^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (p^k*p).eval n=(p.eval n)^(k+1)
    rw [eval_mul,ih,pow_succ]
end RationalHitting.TimeBound


namespace RationalHitting.StackLanguage
open Function

lemma add_bits_length (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length := by
  have hh := wordValue_lt (addWord a.bits b.bits)
  simp only [addWord_value,wordValue_bits] at hh
  exact (by rw [Nat.size_eq_bits_len,Nat.size_le]; exact hh :
    (a+b).bits.length≤(addWord a.bits b.bits).length) |>.trans (addWord_length _ _)

lemma eval_normalize_single {K : Type} [DecidableEq K] {a tmp flag : K}
    (hat : a≠tmp) (haf : a≠flag) (htf : tmp≠flag) (w : List Bool) :
    ∃ t≤7*w.length+16, Eval (normalize a tmp flag) (single a w)
      (single a (wordValue w).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_normalize hat haf htf (single a w)
  have hx : update (update (update (single a w) a (normalizeWord w)) tmp []) flag []=
      single a (wordValue w).bits := by
    funext k
    by_cases ha : k=a <;> by_cases ht : k=tmp <;> by_cases hf : k=flag <;>
      simp_all [single]
  rw [single_self,hx] at he
  refine ⟨t,?_,he⟩
  simpa [hat.symm,haf.symm] using ht

/-- Binary addition followed by output normalization. -/
def addClean : Program (Fin 5) := .seq (add 0 1 2 3 4) (normalize 0 3 4)
lemma eval_addClean (a b : ℕ) : ∃ t≤50*(a.bits.length+b.bits.length+1)^2,
    Eval addClean (both (0 : Fin 5) 1 a.bits b.bits) (single 0 (a+b).bits) t := by
  obtain ⟨t,ht,he⟩ := eval_add (a:=(0 : Fin 5)) (b:=1) (out:=2) (tmp:=3) (flag:=4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (both 0 1 a.bits b.bits)
  have hx : update (update (update (update (update (both (0 : Fin 5) 1 a.bits b.bits)
      0 (addWord a.bits b.bits)) 1 []) 2 []) 3 []) 4 []=single 0 (addWord a.bits b.bits) := by
    funext k; fin_cases k <;> simp [single,both]
  simp only [both_first (by decide : (0 : Fin 5)≠1),both_second,hx] at he
  obtain ⟨u,hu,he'⟩ := eval_normalize_single (a:=(0 : Fin 5)) (tmp:=3) (flag:=4)
    (by decide) (by decide) (by decide) (addWord a.bits b.bits)
  simp only [addWord_value,wordValue_bits] at he'
  refine ⟨1+t+u,?_,Eval.seq he he'⟩
  have hl := addWord_length a.bits b.bits
  simp [both,single] at ht
  nlinarith only [ht,hu,hl,Nat.zero_le (a.bits.length^2),Nat.zero_le (b.bits.length^2)]

namespace Procedure

/-- A polynomially bounded clean procedure for binary addition. -/
def binaryAdd : Procedure (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1+a.2) :=
  fromBinary addClean 0 1 0 (by decide) (50*TimeBound.variable^2)
    (by intro a b; simpa using eval_addClean a b) (by
      intro a b
      have h := add_bits_length a b
      simp
      nlinarith only [h,Nat.zero_le ((a.bits.length+b.bits.length)^2)])

/-- A polynomially bounded clean procedure for binary multiplication. -/
def binaryMul : Procedure (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1*a.2) :=
  fromBinary multiplyClean 0 1 0 (by decide) (200*(TimeBound.variable+1)^4)
    (by
      intro a b
      obtain ⟨t,ht,he⟩ := eval_multiplyClean (both (0 : Fin 8) 1 a.bits b.bits)
        (by intro k hk; simp [both,single,show k≠0 by omega,show k≠1 by omega])
        (a.bits.length+b.bits.length+1) (by simp; omega) (by simp; omega)
      have hx : update (update (both (0 : Fin 8) 1 a.bits b.bits) 0 (a*b).bits) 1 []=
          single 0 (a*b).bits := by
        funext k
        by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> simp_all [both,single]
      simp only [both_first (by decide : (0 : Fin 8)≠1),both_second,wordValue_bits,hx] at he
      exact ⟨t,ht,he⟩)
    (by
      intro a b
      have hl : (a*b).bits.length≤a.bits.length+b.bits.length := by
        simpa only [wordValue_bits] using product_bits_length a.bits b.bits
      have hpow : a.bits.length+b.bits.length+2≤(a.bits.length+b.bits.length+2)^4 :=
        Nat.le_self_pow (by omega) _
      simp only [TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_add,TimeBound.eval_variable,]
      simp only [Nat.add_assoc, show (1:ℕ)+1=2 from rfl] at hpow ⊢
      omega)

end Procedure
namespace Feasible

theorem binaryAdd : Feasible (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1+a.2) :=
  ⟨Procedure.binaryAdd⟩
theorem binaryMul : Feasible (pairCode Nat.bits Nat.bits) Nat.bits (fun a => a.1*a.2) :=
  ⟨Procedure.binaryMul⟩

theorem unaryAdd : Feasible (pairCode unaryCode unaryCode) unaryCode (fun a => a.1+a.2) := by
  exact appendWord.recode _ _ _ (fun a => (unaryCode a.1,unaryCode a.2))
    (by intro a; rfl) (by intro a; simp only [unaryCode,List.replicate_append_replicate])

end Feasible
end RationalHitting.StackLanguage

end Complexity
