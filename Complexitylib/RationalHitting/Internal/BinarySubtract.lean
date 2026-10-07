/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.BinaryMultiply

/-!
# Rational hitting lists: binary subtract

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/BinarySubtract.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Shift-and-add on explicit little-endian words. -/
def mulAccWord : List Bool → List Bool → List Bool → List Bool
  | _a, [], c => c
  | a, false::b, c => mulAccWord (false::a) b c
  | a, true::b, c => mulAccWord (false::a) b (addWord c a)

@[simp] theorem mulAccWord_value (a b c : List Bool) :
    wordValue (mulAccWord a b c) = wordValue c + wordValue a*wordValue b := by
  induction b generalizing a c with
  | nil => simp [mulAccWord,wordValue]
  | cons x b ih => cases x <;> simp [mulAccWord,wordValue,ih,addWord_value] <;> ring

lemma mulAccWord_length (a b c : List Bool) :
    (mulAccWord a b c).length ≤ c.length+b.length*(a.length+b.length) := by
  induction b generalizing a c with
  | nil => simp [mulAccWord]
  | cons x b ih =>
    cases x with
    | false =>
      have h := ih (false::a) c
      simp only [mulAccWord,List.length_cons] at *
      nlinarith
    | true =>
      have h := ih (false::a) (addWord c a)
      have hh := addWord_length c a
      simp only [mulAccWord,List.length_cons] at *
      nlinarith

/-- Registers: 0 multiplicand, 1 multiplier, 2 accumulator,
3 copied addend, 4/5/6 addition scratch, 7 copy scratch. -/
def mulBody : Program (Fin 8) := .branch 1 .skip
  (.seq (.drop 1) (.push 0 false))
  (.seq (.drop 1) (.seq (copy 0 3 7) (.seq (add 2 3 4 5 6) (.push 0 false))))

/-- Repeat the multiplication body over the multiplier bits. -/
def mulLoop : Program (Fin 8) := .loop 1 mulBody

lemma eval_mulLoop (s : Store (Fin 8))
    (hf : ∀ k : Fin 8, 3 ≤ k.val → s k = []) (A C : ℕ)
    (hA : (s 0).length+(s 1).length ≤ A)
    (hC : (s 2).length+(s 1).length*((s 0).length+(s 1).length) ≤ C) :
    ∃ t ≤ (s 1).length*(A*(7*C+34)+23)+1,
      Eval mulLoop s
        (update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
          2 (mulAccWord (s 0) (s 1) (s 2))) t := by
  generalize he : s 1 = l at *
  induction l generalizing s with
  | nil =>
    have hh : update (update (update s 0 (s 0)) 1 []) 2 (s 2) = s := by
      ext k; fin_cases k <;> simp_all
    refine ⟨1,by simp,?_⟩
    change Eval mulLoop s (update (update (update s 0 (s 0)) 1 []) 2 (s 2)) 1
    rw [hh]
    exact Eval.whileNil he
  | cons x l ih =>
    let s₁ := update s 1 l
    have hd : Eval (Program.drop 1) s s₁ 1 := by simpa [s₁,he] using Eval.drop (1 : Fin 8) s
    cases x with
    | false =>
      let s₂ := update s₁ 0 (false::s 0)
      have hp : Eval (Program.push 0 false) s₁ s₂ 1 := by
        simpa [s₂,s₁] using Eval.push (0 : Fin
          8) false s₁
      have hb : Eval mulBody s s₂ 4 := Eval.branchFalse he (Eval.seq hd hp)
      have hf₂ : ∀ k : Fin 8, 3 ≤ k.val → s₂ k = [] := by
        intro k hk; fin_cases k <;> simp_all [s₂,s₁]
      have hA₂ : (s₂ 0).length+(s₂ 1).length ≤ A := by
        simp [s₂,s₁]; simp only
          [List.length_cons] at hA; omega
      have hC₂ : (s₂ 2).length+(s₂ 1).length*((s₂ 0).length+(s₂ 1).length) ≤ C := by
        simp [s₂,s₁]; simp only [List.length_cons] at hC
        nlinarith
      obtain ⟨t,ht,hloop⟩ := ih s₂ hf₂ (by simp [s₂,s₁]) (by simpa [s₂,s₁] using hA₂) (by simpa
        [s₂,s₁] using hC₂)
      have h := Eval.whileCons (by simp [he]) hb hloop
      have heq :
        update (update (update s₂ 0 (List.replicate l.length false++s₂ 0)) 1 [])
          2 (mulAccWord (s₂ 0) l (s₂ 2)) =
        update (update (update s 0 (List.replicate (l.length+1) false++s 0)) 1 [])
          2 (mulAccWord (s 0) (false::l) (s 2)) := by
        ext k; fin_cases k <;> simp [s₂,s₁,mulAccWord,List.replicate_add,List.append_assoc]
      rw [heq] at h
      refine ⟨5+t,?_,by simpa [mulLoop] using h⟩
      simp only [List.length_cons]
      nlinarith
    | true =>
      have hc := eval_copy (a := (0 : Fin 8)) (b := 3) (tmp := 7) (by decide) (by decide) (by
        decide) s₁
      let s₂ := update (update s₁ 3 (s 0)) 7 []
      have hc' : Eval (copy 0 3 7) s₁ s₂ (7*(s 0).length+7) := by
        have h3 := hf 3 (by decide); have h7 := hf 7 (by decide)
        simpa [s₂,s₁,h3,h7] using hc
      obtain ⟨u,hu,ha⟩ := eval_add (a := (2 : Fin 8)) (b := 3) (out := 4) (tmp := 5) (flag := 6)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) s₂
      let s₃ := update (update (update (update (update s₂ 2 (addWord (s 2) (s 0))) 3 []) 4 []) 5
        []) 6 []
      have ha' : Eval (add 2 3 4 5 6) s₂ s₃ u := by simpa [s₃,s₂,s₁] using ha
      let s₄ := update s₃ 0 (false::s 0)
      have hp : Eval (Program.push 0 false) s₃ s₄ 1 := by
        simpa [s₄,s₃,s₂,s₁] using Eval.push (0 : Fin 8) false s₃
      have hb : Eval mulBody s s₄ (6+(7*(s 0).length+7)+u) := by
        convert (Eval.branchTrue (p := Program.skip)
          (q := Program.seq (.drop 1) (.push 0 false)) he
          (Eval.seq hd (Eval.seq hc' (Eval.seq ha' hp)))) using 1 <;> first | rfl | omega
      have hf₄ : ∀ k : Fin 8, 3 ≤ k.val → s₄ k = [] := by
        intro k hk; fin_cases k <;> simp_all [s₄,s₃,s₂,s₁]
      have hA₄ : (s₄ 0).length+(s₄ 1).length ≤ A := by
        simp [s₄,s₃,s₂,s₁]; simp only
          [List.length_cons] at hA; omega
      have hC₄ : (s₄ 2).length+(s₄ 1).length*((s₄ 0).length+(s₄ 1).length) ≤ C := by
        have hh := addWord_length (s 2) (s 0)
        simp [s₄,s₃,s₂,s₁]; simp only [List.length_cons] at hC
        nlinarith
      obtain ⟨t,ht,hloop⟩ := ih s₄ hf₄ (by simp [s₄,s₃,s₂,s₁]) (by simpa [s₄,s₃,s₂,s₁] using
        hA₄) (by simpa [s₄,s₃,s₂,s₁] using hC₄)
      have h := Eval.whileCons (by simp [he]) hb hloop
      have heq :
        update (update (update s₄ 0 (List.replicate l.length false++s₄ 0)) 1 [])
          2 (mulAccWord (s₄ 0) l (s₄ 2)) =
        update (update (update s 0 (List.replicate (l.length+1) false++s 0)) 1 [])
          2 (mulAccWord (s 0) (true::l) (s 2)) := by
        have h3 := hf 3 (by decide); have h4 := hf 4 (by decide)
        have h5 := hf 5 (by decide); have h6 := hf 6 (by decide); have h7 := hf 7 (by decide)
        ext k; fin_cases k <;> simp [s₄,s₃,s₂,s₁,mulAccWord,List.replicate_add,
          List.append_assoc,h3,h4,h5,h6,h7]
      rw [heq] at h
      refine ⟨7+(7*(s 0).length+7)+u+t,?_,by simpa [mulLoop,←Nat.add_assoc] using h⟩
      have ha0 : (s 0).length ≤ A := by simp only [List.length_cons] at hA; omega
      have hc0 : (s 2).length ≤ C := by omega
      have h4 := hf 4 (by decide); have h5 := hf 5 (by decide); have h6 := hf 6 (by decide)
      simp [s₂,s₁,h4,h5,h6] at hu
      have hmul := Nat.mul_le_mul ha0 (Nat.add_le_add_right (Nat.mul_le_mul_left 7 hc0) 34)
      simp only [List.length_cons]
      nlinarith

/-- The normalized multiplication instruction; the accumulator starts at zero.
After execution register 2 is the canonical binary product. -/
def multiply : Program (Fin 8) := .seq mulLoop (normalize 2 5 6)

lemma eval_multiply (s : Store (Fin 8)) (hzero : s 2 = [])
    (hf : ∀ k : Fin 8, 3 ≤ k.val → s k = []) :
    let A := (s 0).length+(s 1).length
    let C := (s 1).length*A
    ∃ t ≤ (s 1).length*(A*(7*C+34)+23)+7*C+18,
      Eval multiply s
        (update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
          2 (wordValue (s 0)*wordValue (s 1)).bits) t := by
  dsimp only
  obtain ⟨t,ht,hloop⟩ := eval_mulLoop s hf ((s 0).length+(s 1).length)
    ((s 1).length*((s 0).length+(s 1).length)) (le_refl _) (by simp [hzero])
  let v := update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
    2 (mulAccWord (s 0) (s 1) (s 2))
  obtain ⟨u,hu,hnorm⟩ := eval_normalize (a := (2 : Fin 8)) (tmp := 5) (flag := 6)
    (by decide) (by decide) (by decide) v
  have h := Eval.seq hloop hnorm
  have h5 := hf 5 (by decide); have h6 := hf 6 (by decide)
  have heq : update (update (update v 2 (normalizeWord (v 2))) 5 []) 6 [] =
      update (update (update s 0 (List.replicate (s 1).length false++s 0)) 1 [])
        2 (wordValue (s 0)*wordValue (s 1)).bits := by
    ext k; fin_cases k <;> simp [v,normalizeWord_eq_bits,mulAccWord_value,hzero,wordValue,h5,h6]
  rw [heq] at h
  refine ⟨1+t+u,?_,h⟩
  have hl := mulAccWord_length (s 0) (s 1) (s 2)
  simp [v,h5,h6,hzero] at hu
  simp [hzero] at hl
  omega

lemma wordValue_lt (l : List Bool) : wordValue l < 2^l.length := by
  induction l with
  | nil => simp [wordValue]
  | cons b l ih => cases b <;> simp [wordValue,pow_succ] <;> omega

lemma product_bits_length (a b : List Bool) :
    (wordValue a * wordValue b).bits.length ≤ a.length+b.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (wordValue_lt a) (wordValue_lt b)

end RationalHitting.StackLanguage

namespace RationalHitting.StackLanguage
open Function

/-- Boolean full-subtractor gate. -/
def differenceBit (x y c : Bool) : Bool := (x ^^ y) ^^ c
/-- The outgoing borrow bit for one full subtractor. -/
def borrowBit (x y c : Bool) : Bool := ((!x) && (y || c)) || (y && c)
/-- Interpret a Boolean bit as zero or one. -/
def bitNat (x : Bool) : ℕ := if x then 1 else 0
@[simp] lemma bitNat_false : bitNat false = 0 := rfl
lemma wordValue_bit (x : Bool) (a : List Bool) : wordValue (x::a) = bitNat x+2*wordValue a := rfl
@[simp] lemma wordValue_nil : wordValue [] = 0 := rfl

lemma digit_subtract (x y c : Bool) :
    bitNat x + 2*bitNat (borrowBit x y c) =
      bitNat (differenceBit x y c)+bitNat y+bitNat c := by
  cases x <;> cases y <;> cases c <;> decide

/-- Fixed-width subtraction, returning the overflow borrow. Registers may have
leading zeros. Width is exactly the larger input word length. -/
def subtractWord : List Bool → List Bool → Bool → List Bool × Bool
  | [],[],c => ([],c)
  | x::a,b,c =>
    let u := subtractWord a b.tail (borrowBit x (b.headD false) c)
    (differenceBit x (b.headD false) c :: u.1,u.2)
  | [],y::b,c =>
    let u := subtractWord [] b (borrowBit false y c)
    (differenceBit false y c :: u.1,u.2)

lemma subtractWord_length (a b : List Bool) (c : Bool) :
    (subtractWord a b c).1.length = max a.length b.length := by
  fun_induction subtractWord a b c with
  | case1 c => simp []
  | case2 x a b c u ih =>
    cases b <;> simp_all [u,Nat.succ_max_succ]
  | case3 y b c u ih => simp_all [u]

lemma subtractWord_value (a b : List Bool) (c : Bool) :
    wordValue a + 2^(max a.length b.length)*bitNat (subtractWord a b c).2 =
      wordValue (subtractWord a b c).1 + wordValue b + bitNat c := by
  fun_induction subtractWord a b c with
  | case1 c => simp [wordValue]
  | case2 x a b c u ih =>
    have hd := digit_subtract x (b.headD false) c
    cases b <;>
      simp only [u,List.tail_nil,List.tail_cons,List.headD_nil,List.headD_cons,
        List.length_nil,List.length_cons,Nat.max_zero,Nat.succ_max_succ,
        pow_succ,wordValue_bit,wordValue_nil,bitNat_false] at * <;>
      linear_combination 2*ih+hd
  | case3 y b c u ih =>
    have hd := digit_subtract false y c
    simp only [u,List.length_nil,List.length_cons,Nat.zero_max,
      pow_succ,wordValue_bit,wordValue_nil,bitNat_false] at *
    linear_combination 2*ih+hd

lemma subtractWord_borrow (a b : List Bool) :
    (subtractWord a b false).2 = true ↔ wordValue a < wordValue b := by
  have hv := subtractWord_value a b false
  have hx := wordValue_lt (subtractWord a b false).1
  rw [subtractWord_length] at hx
  have ha := (wordValue_lt a).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_left
    a.length b.length))
  have hb := (wordValue_lt b).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_max_right
    a.length b.length))
  cases he : (subtractWord a b false).2 <;> simp [he,bitNat] at hv ⊢ <;> omega

lemma subtractWord_nonnegative {a b : List Bool} (h : wordValue b ≤ wordValue a) :
    (subtractWord a b false).2 = false ∧
      wordValue (subtractWord a b false).1 = wordValue a-wordValue b := by
  have hn : (subtractWord a b false).2 = false := by
    cases he : (subtractWord a b false).2
    · rfl
    · have := (subtractWord_borrow a b).mp he; omega
  have hv := subtractWord_value a b false
  simp [hn,bitNat] at hv
  exact ⟨hn,by omega⟩

variable {K : Type} [DecidableEq K]

/-- Branch on the head bit, treating an empty stack as false. -/
def readBit (k : K) (f : Bool → Program K) : Program K := .branch k (f false) (f false) (f true)
lemma eval_readBit (k : K) (f : Bool → Program K) (s v : Store K) (t : ℕ)
    (h : Eval (f ((s k).headD false)) s v t) : Eval (readBit k f) s v (1+t) := by
  cases he : s k with
  | nil => exact Eval.branchNone he (by simpa [he] using h)
  | cons b l =>
    cases b with
    | false => exact Eval.branchFalse he (by simpa [he] using h)
    | true => exact Eval.branchTrue he (by simpa [he] using h)

/-- Registers 0,1 input, 2 reverse output, 3 singleton borrow, 4 loop flag. -/
def subtractDigit : Program (Fin 5) :=
  readBit 0 fun x => readBit 1 fun y => readBit 3 fun c =>
    .seq (.drop 0) (.seq (.drop 1) (.seq (.drop 3)
      (.seq (.push 3 (borrowBit x y c)) (.push 2 (differenceBit x y c)))))

lemma eval_subtractDigit (s : Store (Fin 5)) (c : Bool) (hc : s 3 = [c]) :
    Eval subtractDigit s
      (update (update (update (update s 0 (s 0).tail) 1 (s 1).tail)
        3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
        2 (differenceBit ((s 0).headD false) ((s 1).headD false) c :: s 2)) 12 := by
  unfold subtractDigit
  apply eval_readBit (t := 11)
  apply eval_readBit (t := 10)
  apply eval_readBit (t := 9)
  let s₁ := update s 0 (s 0).tail
  let s₂ := update s₁ 1 (s 1).tail
  let s₃ := update s₂ 3 []
  have h1 := Eval.drop (0 : Fin 5) s
  have h2 := Eval.drop (1 : Fin 5) s₁
  have h3 : Eval (Program.drop 3) s₂ s₃ 1 := by simpa [s₃,s₂,s₁,hc] using Eval.drop (3 : Fin 5) s₂
  have h4 := Eval.push (3 : Fin 5) (borrowBit ((s 0).headD false) ((s 1).headD false) c) s₃
  have h4' : Eval (Program.push 3 (borrowBit ((s 0).headD false) ((s 1).headD false) c)) s₃
    (update s₃ 3 [borrowBit ((s 0).headD false) ((s 1).headD false) c]) 1 := by simpa [s₃] using h4
  have h5 := Eval.push (2 : Fin 5) (differenceBit ((s 0).headD false) ((s 1).headD false) c)
    (update s₃ 3 [borrowBit ((s 0).headD false) ((s 1).headD false) c])
  simpa [s₃,s₂,s₁,hc] using Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4' h5)))

end RationalHitting.StackLanguage

end Complexity
