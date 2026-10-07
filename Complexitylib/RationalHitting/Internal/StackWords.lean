/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Compiler

/-!
# Rational hitting lists: stack words

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/StackWords.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Empty a stack by repeatedly dropping its head. -/
def clear (a : K) : Program K := .loop a (.drop a)
/-- Move a stack onto another stack in reverse order. -/
def reverse (a b : K) : Program K := .loop a (.transfer a b)

lemma eval_clear (a : K) (s : Store K) :
    Eval (clear a) s (update s a []) (2*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update s a [] = s := by ext k; by_cases hk : k=a <;> simp_all
    simpa [clear,he,hh] using (Eval.whileNil (p:=Program.drop a) he)
  | cons b l ih =>
    let s₁ := update s a l
    have h₁ : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
    have h₂ := ih s₁ (by simp [s₁])
    have hh : update s₁ a [] = update s a [] := by simp [s₁]
    have h := Eval.whileCons (by simp [he]) h₁ h₂
    convert h using 1 <;> simp_all [clear,s₁,Nat.mul_add,Nat.add_assoc] ; omega

lemma transfer_cons {a b : K} (hab : a ≠ b) (s : Store K) (x : Bool) (l : List Bool)
    (hs : s a = x::l) : transfer a b s = update (update s a l) b (x::s b) := by
  simp [transfer,hs,Ne.symm hab]

lemma eval_reverse {a b : K} (hab : a ≠ b) (s : Store K) :
    Eval (reverse a b) s (update (update s a []) b ((s a).reverse ++ s b))
      (2*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update s a []) b (s b) = s := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> simp_all
    simpa [reverse,he,hh] using (Eval.whileNil (p:=Program.transfer a b) he)
  | cons x l ih =>
    let s₁ := update (update s a l) b (x::s b)
    have ha : s₁ a = l := by simp [s₁,hab]
    have hb : s₁ b = x::s b := by simp [s₁]
    have h₁ : Eval (Program.transfer a b) s s₁ 1 := by
      simpa [transfer_cons hab s x l he,s₁] using Eval.transfer a b s
    have h₂ := ih s₁ ha
    have hh : update (update s₁ a []) b (l.reverse++s₁ b) =
        update (update s a []) b ((x::l).reverse++s b) := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;>
        simp_all [s₁,List.reverse_cons,List.append_assoc]
    have h := Eval.whileCons (by simp [he]) h₁ h₂
    convert h using 1 <;> simp_all [reverse,Nat.mul_add,Nat.add_assoc] ; omega

/-- Copy a nonempty head to another register without consuming it. -/
def copyHead (a b : K) : Program K := .branch a .skip (.push b false) (.push b true)

lemma eval_copyHead {a b : K} (s : Store K) (x : Bool) (l : List Bool) (hs : s a = x::l) :
    Eval (copyHead a b) s (update s b (x::s b)) 2 := by
  cases x with
  | false => exact Eval.branchFalse hs (Eval.push b false s)
  | true => exact Eval.branchTrue hs (Eval.push b true s)

/-- Two simultaneous reversed copies of a word, consuming the operand. -/
def duplicateReverse (a b c : K) : Program K :=
  .loop a (.seq (.transfer a b) (copyHead b c))

lemma eval_duplicateReverse {a b c : K} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (s : Store K) :
    Eval (duplicateReverse a b c) s
      (update (update (update s a []) b ((s a).reverse++s b)) c ((s a).reverse++s c))
      (5*(s a).length+1) := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s a []) b (s b)) c (s c) = s := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkc : k=c <;> simp_all
    simpa [duplicateReverse,he,hh] using
      (Eval.whileNil (p:=Program.seq (.transfer a b) (copyHead b c)) he)
  | cons x l ih =>
    let s₁ := update (update s a l) b (x::s b)
    let s₂ := update s₁ c (x::s c)
    have h₁ : Eval (Program.transfer a b) s s₁ 1 := by
      simpa [transfer_cons hab s x l he,s₁] using Eval.transfer a b s
    have h₂ : Eval (copyHead b c) s₁ s₂ 2 := by
      simpa [s₂,s₁,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] using
        eval_copyHead (a:=b) (b:=c) s₁ x (s b) (by simp [s₁])
    have ha : s₂ a = l := by simp [s₂,s₁,hab,hac,]
    have ht := ih s₂ ha
    have hh : update (update (update s₂ a []) b (l.reverse++s₂ b)) c (l.reverse++s₂ c) =
        update (update (update s a []) b ((x::l).reverse++s b)) c ((x::l).reverse++s c) := by
      ext k
      by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkc : k=c <;>
        simp_all [s₂,s₁,List.reverse_cons,List.append_assoc]
    have h := Eval.whileCons (by simp [he]) (Eval.seq h₁ h₂) ht
    convert h using 1 <;> simp_all [duplicateReverse,Nat.mul_add,Nat.add_assoc] ; omega

/-- Copy an arbitrary binary word, restoring the operand and clearing
temporary storage; all registers have fixed indices. -/
def copy (a b tmp : K) : Program K :=
  .seq (clear b) (.seq (clear tmp) (.seq (reverse a tmp) (duplicateReverse tmp a b)))

lemma eval_copy {a b tmp : K} (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp)
    (s : Store K) :
    Eval (copy a b tmp) s (update (update s b (s a)) tmp [])
      (7*(s a).length+2*(s b).length+2*(s tmp).length+7) := by
  let s₁ := update s b []
  let s₂ := update s₁ tmp []
  let s₃ := update (update s₂ a []) tmp ((s₂ a).reverse++s₂ tmp)
  have h₁ := eval_clear b s
  have h₂ := eval_clear tmp s₁
  have h₃ := eval_reverse hat s₂
  have h₄ := eval_duplicateReverse (Ne.symm hat) (Ne.symm hbt) hab s₃
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  have hh : update (update (update s₃ tmp []) a ((s₃ tmp).reverse++s₃ a)) b
        ((s₃ tmp).reverse++s₃ b) = update (update s b (s a)) tmp [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkt : k=tmp <;>
      simp_all [s₃,s₂,s₁]
  change Eval (copy a b tmp) s
    (update (update (update s₃ tmp []) a ((s₃ tmp).reverse++s₃ a)) b
        ((s₃ tmp).reverse++s₃ b)) _ at h
  rw [hh] at h
  convert h using 1
  simp [s₃,s₂,s₁,hab,hat,Ne.symm hbt]
  omega

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

/-- Little-endian binary words; zero has the empty word. -/
def wordValue : List Bool → ℕ
  | [] => 0
  | b::l => (if b then 1 else 0)+2*wordValue l

/-- Increment a little-endian binary word, allowing a new high bit. -/
def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::l => true::l
  | true::l => false::incrementWord l

@[simp] theorem incrementWord_value (l : List Bool) : wordValue (incrementWord l) = wordValue
    l+1 := by
  induction l with
  | nil => simp [incrementWord,wordValue]
  | cons b l ih => cases b <;> simp [incrementWord,wordValue,ih] <;> omega

/-- Separate the initial carry chain from the incremented remainder. -/
def carrySplit : List Bool → ℕ × List Bool
  | [] => (0,[true])
  | false::l => (0,true::l)
  | true::l => let r := carrySplit l; (r.1+1,r.2)

theorem carrySplit_spec (l : List Bool) :
    incrementWord l = List.replicate (carrySplit l).1 false ++ (carrySplit l).2 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b with
    | false => rfl
    | true => simp [incrementWord,carrySplit,List.replicate_succ,ih]

theorem carrySplit_length (l : List Bool) : (carrySplit l).1 ≤ l.length := by
  induction l with
  | nil => simp [carrySplit]
  | cons b l ih => cases b <;> simp [carrySplit] ; omega

theorem incrementWord_length (l : List Bool) : (incrementWord l).length ≤ l.length+1 := by
  induction l with
  | nil => simp [incrementWord]
  | cons b l ih => cases b <;> simp [incrementWord] ; omega

/-- One carry-propagation step of binary increment. -/
def incrementBody (a tmp flag : K) : Program K := .branch a
  (.seq (.push a true) (clear flag))
  (.seq (.drop a) (.seq (.push a true) (clear flag)))
  (.seq (.drop a) (.push tmp false))

/-- Propagate the increment carry until the flag is cleared. -/
def incrementLoop (a tmp flag : K) : Program K := .loop flag (incrementBody a tmp flag)

lemma eval_incrementLoop {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) (hf : s flag = [true]) :
    ∃ t ≤ 5*(s a).length+10, Eval (incrementLoop a tmp flag) s
      (update (update (update s a (carrySplit (s a)).2) tmp
        (List.replicate (carrySplit (s a)).1 false ++ s tmp)) flag []) t := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    let s₁ := update s a [true]
    have hf₁ : s₁ flag = [true] := by simp [s₁,Ne.symm haf,hf]
    have hclear : Eval (clear flag) s₁ (update s₁ flag []) 3 := by
      simpa [hf₁] using eval_clear flag s₁
    have hpush : Eval (Program.push a true) s s₁ 1 := by
      simpa [s₁,he] using Eval.push a true s
    have hb : Eval (incrementBody a tmp flag) s (update s₁ flag []) 6 :=
      Eval.branchNone he (Eval.seq hpush hclear)
    have halt : Eval (incrementLoop a tmp flag) (update s₁ flag []) (update s₁ flag []) 1 :=
      Eval.whileNil (by simp)
    have h := Eval.whileCons (by simp [hf]) hb halt
    have hh : update (update (update s a [true]) tmp (s tmp)) flag [] = update s₁ flag [] := by
      ext k
      by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;> simp_all [s₁]
    refine ⟨8,by simp,?_⟩
    simpa [incrementLoop,he,carrySplit,hh] using h
  | cons b l ih =>
    cases b with
    | false =>
      let s₁ := update s a l
      let s₂ := update s₁ a (true::l)
      have hf₂ : s₂ flag = [true] := by simp [s₂,s₁,Ne.symm haf,hf]
      have hclear : Eval (clear flag) s₂ (update s₂ flag []) 3 := by
        simpa [hf₂] using eval_clear flag s₂
      have hdrop : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hpush : Eval (Program.push a true) s₁ s₂ 1 := by simpa [s₂,s₁] using Eval.push a true s₁
      have hb : Eval (incrementBody a tmp flag) s (update s₂ flag []) 8 :=
        Eval.branchFalse he (Eval.seq hdrop (Eval.seq hpush hclear))
      have halt : Eval (incrementLoop a tmp flag) (update s₂ flag []) (update s₂ flag []) 1 :=
        Eval.whileNil (by simp)
      have h := Eval.whileCons (by simp [hf]) hb halt
      have hh : update (update (update s a (true::l)) tmp (s tmp)) flag [] = update s₂ flag [] := by
        ext k
        by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;> simp_all [s₂,s₁]
      refine ⟨10,by simp,?_⟩
      simpa [incrementLoop,he,carrySplit,hh] using h
    | true =>
      let s₁ := update s a l
      let s₂ := update s₁ tmp (false::s tmp)
      have ha₂ : s₂ a = l := by simp [s₂,s₁,hat]
      have hf₂ : s₂ flag = [true] := by simp [s₂,s₁,Ne.symm haf,Ne.symm htf,hf]
      have hdrop : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hpush : Eval (Program.push tmp false) s₁ s₂ 1 := by
        simpa [s₂,s₁,Ne.symm hat] using
          Eval.push tmp false s₁
      have hb : Eval (incrementBody a tmp flag) s s₂ 4 :=
        Eval.branchTrue he (Eval.seq hdrop hpush)
      obtain ⟨t,ht,hev⟩ := ih s₂ hf₂ ha₂
      have h := Eval.whileCons (by simp [hf]) hb hev
      have hh :
        update (update (update s₂ a (carrySplit l).2) tmp
          (List.replicate (carrySplit l).1 false++s₂ tmp)) flag [] =
        update (update (update s a (carrySplit l).2) tmp
          (List.replicate ((carrySplit l).1+1) false++s tmp)) flag [] := by
        ext k
        by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
          simp_all [s₂,s₁,List.replicate_add,List.append_assoc]
      refine ⟨5+t,by simp only [List.length_cons] at *; omega,?_⟩
      simpa only [incrementLoop,ha₂,carrySplit,hh] using h

/-- Increment a binary stack word and restore its orientation. -/
def increment (a tmp flag : K) : Program K :=
  .seq (clear tmp) (.seq (clear flag) (.seq (.push flag true)
    (.seq (incrementLoop a tmp flag) (reverse tmp a))))

lemma eval_increment {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ 7*(s a).length+2*(s tmp).length+2*(s flag).length+18,
      Eval (increment a tmp flag) s
        (update (update (update s a (incrementWord (s a))) tmp []) flag []) t := by
  let s₁ := update s tmp []
  let s₂ := update s₁ flag []
  let s₃ := update s₂ flag [true]
  have ha₃ : s₃ a = s a := by simp [s₃,s₂,s₁,hat,haf]
  have ht₃ : s₃ tmp = [] := by simp [s₃,s₂,s₁,htf]
  obtain ⟨t,ht,hloop⟩ := eval_incrementLoop hat haf htf s₃ (by simp [s₃])
  let s₄ := update (update (update s₃ a (carrySplit (s a)).2) tmp
        (List.replicate (carrySplit (s a)).1 false)) flag []
  change Eval (incrementLoop a tmp flag) s₃ _ t at hloop
  have hloop' : Eval (incrementLoop a tmp flag) s₃ s₄ t := by
    simpa [ha₃,ht₃,s₄] using hloop
  have h₁ := eval_clear tmp s
  have h₂ := eval_clear flag s₁
  have hp : Eval (Program.push flag true) s₂ s₃ 1 := by simpa [s₂,s₃] using Eval.push flag true s₂
  have hrev := eval_reverse (Ne.symm hat) s₄
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq hp (Eval.seq hloop' hrev)))
  have hfinal : update (update s₄ tmp []) a ((s₄ tmp).reverse++s₄ a) =
      update (update (update s a (incrementWord (s a))) tmp []) flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₄,s₃,s₂,s₁,carrySplit_spec]
  rw [hfinal] at h
  refine ⟨_,?_,h⟩
  have hc := carrySplit_length (s a)
  simp only [ha₃] at ht
  simp [s₄,s₃,s₂,s₁,htf,Ne.symm htf]
  omega

end RationalHitting.StackLanguage

end Complexity
