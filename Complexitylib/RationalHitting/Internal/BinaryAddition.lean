/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.StackWords

/-!
# Rational hitting lists: binary addition

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinaryAddition.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma wordValue_head_tail (l : List Bool) :
    wordValue l = (if l.headD false then 1 else 0)+2*wordValue l.tail := by
  cases l with
  | nil => rfl
  | cons b l => rfl

/-- Grade-school addition, scanning the second operand one bit at a time.
The first operand is shifted after adding the incoming low bit. -/
def addWord : List Bool → List Bool → List Bool
  | a, [] => a
  | a, false::b => a.headD false :: addWord a.tail b
  | a, true::b => (incrementWord a).headD false :: addWord (incrementWord a).tail b

@[simp] theorem addWord_value (a b : List Bool) :
    wordValue (addWord a b) = wordValue a + wordValue b := by
  induction b generalizing a with
  | nil => simp [addWord,wordValue]
  | cons x b ih =>
    cases x with
    | false =>
      simp only [addWord,wordValue,Bool.false_eq_true,↓reduceIte,zero_add,ih]
      rw [wordValue_head_tail a]
      omega
    | true =>
      simp only [addWord,wordValue,↓reduceIte,ih]
      have hh := wordValue_head_tail (incrementWord a)
      rw [incrementWord_value] at hh
      omega

lemma incrementWord_tail_length (a : List Bool) : (incrementWord a).tail.length ≤ a.length := by
  have hh := incrementWord_length a
  rw [List.length_tail]
  omega

lemma addWord_length (a b : List Bool) : (addWord a b).length ≤ a.length+b.length := by
  induction b generalizing a with
  | nil => simp [addWord]
  | cons x b ih =>
    cases x with
    | false =>
      have hh := ih a.tail
      simp only [addWord,List.length_cons]
      have ht : a.tail.length ≤ a.length := by simp
      omega
    | true =>
      have hh := ih (incrementWord a).tail
      have ht := incrementWord_tail_length a
      simp only [addWord,List.length_cons]
      omega

/-- Emits one least-significant bit, supplying zero for an exhausted operand. -/
def emitLow (a out : K) : Program K :=
  .branch a (.push out false) (.transfer a out) (.transfer a out)

lemma eval_emitLow {a out : K} (hao : a ≠ out) (s : Store K) :
    Eval (emitLow a out) s
      (update (update s a (s a).tail) out ((s a).headD false::s out)) 2 := by
  cases he : s a with
  | nil =>
    have hh : update (update s a (s a).tail) out ((s a).headD false::s out) =
        update s out (false::s out) := by
      ext k; by_cases hka : k=a <;> by_cases hko : k=out <;> simp_all
    simp only [he] at hh
    rw [hh]
    exact Eval.branchNone he (Eval.push out false s)
  | cons x xs =>
    have ht := Eval.transfer a out s
    simp only [transfer,he,Function.update_of_ne (Ne.symm hao)] at ht
    cases x with
    | false => simpa [emitLow,he] using Eval.branchFalse he ht
    | true => simpa [emitLow,he] using Eval.branchTrue he ht

/-- Output invariant for the single pass: a reversed low part is on `out`. -/
def addSplit : List Bool → List Bool → List Bool × List Bool
  | a, [] => ([],a)
  | a, false::b =>
    let r := addSplit a.tail b
    (a.headD false::r.1,r.2)
  | a, true::b =>
    let r := addSplit (incrementWord a).tail b
    ((incrementWord a).headD false::r.1,r.2)

lemma addSplit_spec (a b : List Bool) : (addSplit a b).1++(addSplit a b).2 = addWord a b := by
  induction b generalizing a with
  | nil => rfl
  | cons x b ih => cases x <;> simp [addSplit,addWord,ih]

lemma addSplit_first_length (a b : List Bool) : (addSplit a b).1.length = b.length := by
  induction b generalizing a with
  | nil => rfl
  | cons x b ih => cases x <;> simp [addSplit,ih]

/-- Consume one addend bit, propagating its contribution to the accumulator. -/
def addBody (a b out tmp flag : K) : Program K :=
  .branch b .skip (.seq (.drop b) (emitLow a out))
    (.seq (.drop b) (.seq (increment a tmp flag) (emitLow a out)))

/-- Repeat the addition step until the addend stack is empty. -/
def addLoop (a b out tmp flag : K) : Program K := .loop b (addBody a b out tmp flag)

lemma eval_addLoop {a b out tmp flag : K}
    (hab : a ≠ b) (hao : a ≠ out) (hat : a ≠ tmp) (haf : a ≠ flag)
    (hbo : b ≠ out) (hbt : b ≠ tmp) (hbf : b ≠ flag)
    (hot : out ≠ tmp) (hof : out ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) (ht : s tmp = []) (hf : s flag = []) :
    ∃ t ≤ (s b).length*(7*(s a).length+25)+1,
      Eval (addLoop a b out tmp flag) s
        (update (update (update s a (addSplit (s a) (s b)).2) b []) out
          ((addSplit (s a) (s b)).1.reverse++s out)) t := by
  generalize he : s b = l
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s a (s a)) b []) out (s out) = s := by
      ext k; by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;> simp_all
    refine ⟨1,by simp,?_⟩
    change Eval (addLoop a b out tmp flag) s
      (update (update (update s a (s a)) b []) out (s out)) 1
    rw [hh]
    exact Eval.whileNil he
  | cons x l ih =>
    let s₁ := update s b l
    have hdrop : Eval (Program.drop b) s s₁ 1 := by simpa [s₁,he] using Eval.drop b s
    cases x with
    | false =>
      let s₂ := update (update s₁ a (s a).tail) out ((s a).headD false::s out)
      have hh : Eval (emitLow a out) s₁ s₂ 2 := by
        simpa [s₂,s₁,hab,Ne.symm hbo] using eval_emitLow hao s₁
      have hb : Eval (addBody a b out tmp flag) s s₂ 5 :=
        Eval.branchFalse he (Eval.seq hdrop hh)
      have hta : s₂ a = (s a).tail := by simp [s₂,hao]
      have htb : s₂ b = l := by simp [s₂,s₁,hbo,Ne.symm hab]
      have htt : s₂ tmp = [] := by simp [s₂,s₁,Ne.symm hot,Ne.symm hat,Ne.symm hbt,ht]
      have htf' : s₂ flag = [] := by simp [s₂,s₁,Ne.symm hof,Ne.symm haf,Ne.symm hbf,hf]
      obtain ⟨t,htime,hloop⟩ := ih s₂ htt htf' htb
      have h := Eval.whileCons (by simp [he]) hb hloop
      have hfinal :
        update (update (update s₂ a (addSplit (s₂ a) (s₂ b)).2) b []) out
          ((addSplit (s₂ a) (s₂ b)).1.reverse++s₂ out) =
        update (update (update s a (addSplit (s a) (false::l)).2) b []) out
          ((addSplit (s a) (false::l)).1.reverse++s out) := by
        ext k
        by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
          simp_all [s₂,s₁,addSplit,List.append_assoc]
      simp only [htb] at hfinal
      rw [hfinal] at h
      refine ⟨6+t,?_,by simpa [addLoop,he] using h⟩
      simp only [hta] at htime
      have hlen : (s a).tail.length ≤ (s a).length := by simp
      have hmul := Nat.mul_le_mul_left l.length (Nat.add_le_add_right (Nat.mul_le_mul_left 7
        hlen) 25)
      simp only [List.length_cons]
      nlinarith
    | true =>
      obtain ⟨u,hu,hinc⟩ := eval_increment hat haf htf s₁
      let s₂ := update (update (update s₁ a (incrementWord (s a))) tmp []) flag []
      have hii : Eval (increment a tmp flag) s₁ s₂ u := by simpa [s₂,s₁,hab] using hinc
      let s₃ := update (update s₂ a (incrementWord (s a)).tail) out
        ((incrementWord (s a)).headD false::s out)
      have hh : Eval (emitLow a out) s₂ s₃ 2 := by
        simpa [s₃,s₂,s₁,hat,haf,Ne.symm hao,Ne.symm hbo,hot,hof] using eval_emitLow hao s₂
      have hb : Eval (addBody a b out tmp flag) s s₃ (6+u) := by
        simpa [addBody,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          (Eval.branchTrue he (Eval.seq hdrop (Eval.seq hii hh)))
      have hta : s₃ a = (incrementWord (s a)).tail := by simp [s₃,hao]
      have htb : s₃ b = l := by simp [s₃,s₂,s₁,hbo,hbt,hbf,Ne.symm hab]
      have htt : s₃ tmp = [] := by simp [s₃,s₂,Ne.symm hot,Ne.symm hat,htf]
      have htf' : s₃ flag = [] := by simp [s₃,s₂,Ne.symm hof,Ne.symm haf]
      obtain ⟨t,htime,hloop⟩ := ih s₃ htt htf' htb
      have h := Eval.whileCons (by simp [he]) hb hloop
      have hfinal :
        update (update (update s₃ a (addSplit (s₃ a) (s₃ b)).2) b []) out
          ((addSplit (s₃ a) (s₃ b)).1.reverse++s₃ out) =
        update (update (update s a (addSplit (s a) (true::l)).2) b []) out
          ((addSplit (s a) (true::l)).1.reverse++s out) := by
        ext k
        by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
        by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
          simp_all [s₃,s₂,s₁,addSplit,List.append_assoc]
      simp only [htb] at hfinal
      rw [hfinal] at h
      refine ⟨7+u+t,?_,by simpa [addLoop,he,←Nat.add_assoc] using h⟩
      simp only [hta] at htime
      have hlen := incrementWord_tail_length (s a)
      have hmul := Nat.mul_le_mul_left l.length (Nat.add_le_add_right (Nat.mul_le_mul_left 7
        hlen) 25)
      simp [s₁,hab,Ne.symm hbt,Ne.symm hbf,ht,hf] at hu
      simp only [List.length_cons]
      nlinarith

/-- Destructive binary addition. The second operand and all scratch words are
cleared; the first register holds the exact sum. -/
def add (a b out tmp flag : K) : Program K :=
  .seq (clear out) (.seq (clear tmp) (.seq (clear flag)
    (.seq (addLoop a b out tmp flag) (reverse out a))))

lemma eval_add {a b out tmp flag : K}
    (hab : a ≠ b) (hao : a ≠ out) (hat : a ≠ tmp) (haf : a ≠ flag)
    (hbo : b ≠ out) (hbt : b ≠ tmp) (hbf : b ≠ flag)
    (hot : out ≠ tmp) (hof : out ≠ flag) (htf : tmp ≠ flag)
    (s : Store K) :
    ∃ t ≤ (s b).length*(7*(s a).length+27)+
        2*(s out).length+2*(s tmp).length+2*(s flag).length+9,
      Eval (add a b out tmp flag) s
        (update (update (update (update (update s a (addWord (s a) (s b))) b []) out []) tmp [])
          flag []) t := by
  let s₁ := update s out []
  let s₂ := update s₁ tmp []
  let s₃ := update s₂ flag []
  have ha₃ : s₃ a = s a := by simp [s₃,s₂,s₁,hao,hat,haf]
  have hb₃ : s₃ b = s b := by simp [s₃,s₂,s₁,hbo,hbt,hbf]
  have ho₃ : s₃ out = [] := by simp [s₃,s₂,s₁,hot,hof]
  obtain ⟨t,ht,hloop⟩ := eval_addLoop hab hao hat haf hbo hbt hbf hot hof htf s₃
    (by simp [s₃,s₂,htf]) (by simp [s₃])
  let s₄ := update (update (update s₃ a (addSplit (s a) (s b)).2) b []) out
      (addSplit (s a) (s b)).1.reverse
  have hlo : Eval (addLoop a b out tmp flag) s₃ s₄ t := by
    simpa [s₄,ha₃,hb₃,ho₃] using hloop
  have hrev := eval_reverse (Ne.symm hao) s₄
  have h := Eval.seq (eval_clear out s) (Eval.seq (eval_clear tmp s₁)
    (Eval.seq (eval_clear flag s₂) (Eval.seq hlo hrev)))
  have hfinal : update (update s₄ out []) a ((s₄ out).reverse++s₄ a) =
      update (update (update (update (update s a (addWord (s a) (s b))) b []) out []) tmp [])
        flag [] := by
    ext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hko : k=out <;>
    by_cases hkt : k=tmp <;> by_cases hkf : k=flag <;>
      simp_all [s₄,s₃,s₂,s₁,addSplit_spec]
  rw [hfinal] at h
  refine ⟨_,?_,h⟩
  rw [ha₃,hb₃] at ht
  simp [s₄,s₃,s₂,s₁,Ne.symm hot,Ne.symm hof,Ne.symm htf,addSplit_first_length]
  nlinarith

end RationalHitting.StackLanguage

end Complexity
