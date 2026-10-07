/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryAddition
public import Mathlib.Data.Nat.Size

/-!
# Rational hitting lists: binary multiply

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryMultiply.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_append (a b : List Bool) :
    wordValue (a++b) = wordValue a + 2^a.length * wordValue b := by
  induction a with
  | nil => simp [wordValue]
  | cons x a ih => simp [wordValue,ih,pow_succ]; ring

/-- Removes the high zero bits of a most-significant-first word. -/
def trimMSD : List Bool → List Bool
  | [] => []
  | false::l => trimMSD l
  | true::l => true::l

lemma trimMSD_length (l : List Bool) : (trimMSD l).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [trimMSD] ; omega

lemma trimMSD_reverse_value (l : List Bool) :
    wordValue (trimMSD l).reverse = wordValue l.reverse := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [trimMSD,List.reverse_cons,wordValue_append,wordValue,ih]

/-- A little-endian word with no redundant high zero bits. -/
def Canonical (l : List Bool) : Prop := l = [] ∨ ∃ w, l = w++[true]

lemma canonical_tail {b : Bool} {l : List Bool} (h : Canonical (b::l)) : Canonical l := by
  obtain h | ⟨w,hw⟩ := h
  · contradiction
  · cases w with
    | nil => simp only [List.nil_append,List.cons.injEq] at hw; exact Or.inl hw.2
    | cons x w =>
      simp only [List.cons_append,List.cons.injEq] at hw
      exact Or.inr ⟨w,hw.2⟩

lemma canonical_single {b : Bool} (h : Canonical [b]) : b = true := by
  obtain h | ⟨w,hw⟩ := h
  · contradiction
  · cases w with
    | nil => simpa using hw
    | cons a w =>
      have hl := congrArg List.length hw
      simp only [List.length_cons,List.length_append] at hl
      omega

lemma bits_wordValue (l : List Bool) (h : Canonical l) : (wordValue l).bits = l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have htail := ih (canonical_tail h)
    have hz : wordValue l = 0 → b = true := by
      intro hh
      have hl : l = [] := by simpa [hh] using htail.symm
      subst l
      exact canonical_single h
    have he : wordValue (b::l) = Nat.bit b (wordValue l) := by
      cases b <;> simp [wordValue,Nat.bit] ; omega
    rw [he,Nat.bits_append_bit _ _ hz,htail]

lemma canonical_trim_reverse (l : List Bool) : Canonical (trimMSD l).reverse := by
  induction l with
  | nil => exact Or.inl rfl
  | cons b l ih =>
    cases b with
    | false => exact ih
    | true => exact Or.inr ⟨l.reverse,by simp [trimMSD]⟩

/-- Remove redundant high zero bits from a binary word. -/
def normalizeWord (l : List Bool) : List Bool := (trimMSD l.reverse).reverse

theorem normalizeWord_value (l : List Bool) : wordValue (normalizeWord l) = wordValue l
    := by
  simpa [normalizeWord] using trimMSD_reverse_value l.reverse

@[simp] theorem normalizeWord_eq_bits (l : List Bool) : normalizeWord l = (wordValue l).bits := by
  rw [← normalizeWord_value l]
  exact (bits_wordValue _ (canonical_trim_reverse l.reverse)).symm

lemma normalizeWord_length (l : List Bool) : (normalizeWord l).length = (wordValue l).size := by
  rw [normalizeWord_eq_bits,Nat.size_eq_bits_len]

/-- One step removing high zero bits from a reversed word. -/
def trimBody (a flag : K) : Program K := .branch a (clear flag) (.drop a) (clear flag)
/-- Trim high zeros until the leading one or the empty word is reached. -/
def trimLoop (a flag : K) : Program K := .loop flag (trimBody a flag)

lemma eval_trimLoop {a flag : K} (haf : a ≠ flag) (s : Store K) (hf : s flag = [true]) :
    ∃ t ≤ 3*(s a).length+6,
      Eval (trimLoop a flag) s (update (update s a (trimMSD (s a))) flag []) t := by
  generalize he : s a = l
  induction l generalizing s with
  | nil =>
    have hh : update (update s a []) flag [] = update s flag [] := by
      ext k; by_cases hka : k=a <;> by_cases hkf : k=flag <;> simp_all
    have hc : Eval (clear flag) s (update s flag []) 3 := by simpa [hf] using eval_clear flag s
    have hb : Eval (trimBody a flag) s (update s flag []) 4 := Eval.branchNone he hc
    have halt : Eval (trimLoop a flag) (update s flag []) (update s flag []) 1 := Eval.whileNil
      (by simp)
    refine ⟨6,by simp,?_⟩
    simpa [trimLoop,he,trimMSD,hh] using Eval.whileCons (by simp [hf]) hb halt
  | cons b l ih =>
    cases b with
    | false =>
      let s₁ := update s a l
      have hh : s₁ flag = [true] := by simp [s₁,Ne.symm haf,hf]
      obtain ⟨t,ht,hloop⟩ := ih s₁ hh (by simp [s₁])
      have hd : Eval (Program.drop a) s s₁ 1 := by simpa [s₁,he] using Eval.drop a s
      have hb : Eval (trimBody a flag) s s₁ 2 := Eval.branchFalse he hd
      have h := Eval.whileCons (by simp [hf]) hb hloop
      refine ⟨3+t,by simp only [List.length_cons]; omega,?_⟩
      simpa [trimLoop,trimMSD,s₁] using h
    | true =>
      have hh : update (update s a (true::l)) flag [] = update s flag [] := by
        ext k; by_cases hka : k=a <;> by_cases hkf : k=flag <;> simp_all
      have hc : Eval (clear flag) s (update s flag []) 3 := by simpa [hf] using eval_clear flag s
      have hb : Eval (trimBody a flag) s (update s flag []) 4 := Eval.branchTrue he hc
      have halt : Eval (trimLoop a flag) (update s flag []) (update s flag []) 1 :=
        Eval.whileNil (by simp)
      refine ⟨6,by simp,?_⟩
      simpa [trimLoop,trimMSD,hh] using Eval.whileCons (by simp [hf]) hb halt

/-- Normalize a binary stack word using a reversed temporary copy. -/
def normalize (a tmp flag : K) : Program K :=
  .seq (clear tmp) (.seq (clear flag) (.seq (.push flag true)
    (.seq (reverse a tmp) (.seq (trimLoop tmp flag) (reverse tmp a)))))

lemma eval_normalize {a tmp flag : K} (hat : a ≠ tmp) (haf : a ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ 7*(s a).length+2*(s tmp).length+2*(s flag).length+16,
      Eval (normalize a tmp flag) s
        (update (update (update s a (normalizeWord (s a))) tmp []) flag []) t := by
  let s₁ := update s tmp []
  let s₂ := update s₁ flag []
  let s₃ := update s₂ flag [true]
  let s₄ := update (update s₃ a []) tmp (s a).reverse
  have hr : Eval (reverse a tmp) s₃ s₄ (2*(s a).length+1) := by
    simpa [s₄,s₃,s₂,s₁,hat,haf,htf] using eval_reverse hat s₃
  obtain ⟨t,ht,htrim⟩ := eval_trimLoop htf s₄ (by simp [s₄,s₃,Ne.symm htf,Ne.symm haf])
  let s₅ := update (update s₄ tmp (trimMSD (s a).reverse)) flag []
  have htr : Eval (trimLoop tmp flag) s₄ s₅ t := by simpa [s₅,s₄] using htrim
  have hp : Eval (Program.push flag true) s₂ s₃ 1 := by simpa [s₃,s₂] using Eval.push flag true s₂
  have h := Eval.seq (eval_clear tmp s) (Eval.seq (eval_clear flag s₁)
    (Eval.seq hp (Eval.seq hr (Eval.seq htr (eval_reverse (Ne.symm hat) s₅)))))
  have heq : update (update s₅ tmp []) a ((s₅ tmp).reverse++s₅ a) =
      update (update (update s a (normalizeWord (s a))) tmp []) flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₅,s₄,s₃,s₂,s₁,normalizeWord]
  rw [heq] at h
  refine ⟨_,?_,h⟩
  have hl := trimMSD_length (s a).reverse
  simp [s₄] at ht
  simp [s₅,s₄,s₃,s₂,s₁,htf,Ne.symm htf]
  simp only [List.length_reverse] at hl
  omega

end RationalHitting.StackLanguage

end Complexity
