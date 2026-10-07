/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.GridComputation

/-!
# Rational hitting lists: output computation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/OutputComputation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Strip the one literal separator of the required unary input, remembering
its first field in a separate finite stack. -/
def unaryScanBody : Program (Fin 3) :=
  .branch 0 (clear 2) (.seq (.drop 0) (clear 2)) (.transfer 0 1)

/-- Copy a unary input segment until its scan register is exhausted. -/
def unaryScan : Program (Fin 3) := .loop 2 unaryScanBody

lemma eval_unaryScan (n : ℕ) (w : List Bool) (s : Store (Fin 3))
    (h0 : s 0=List.replicate n true++false::w) (h2 : s 2=[true]) :
    Eval unaryScan s
      (update (update (update s 0 w) 1 (List.replicate n true++s 1)) 2 [])
      (3*n+8) := by
  unfold unaryScan
  induction n generalizing s with
  | zero =>
    have hs : s 0=false::w := by simpa using h0
    have hd := Eval.drop (0:Fin 3) s
    have hc := eval_clear (2:Fin 3) (update s 0 w)
    simp only [update_of_ne (by decide : (2:Fin 3)≠0),h2,List.length_singleton] at hc
    have hb : Eval unaryScanBody s (update (update s 0 w) 2 []) 6 := by
      exact Eval.branchFalse hs (Eval.seq (by simpa [hs] using hd) hc)
    have hl := Eval.whileCons (by simp [h2]) hb
      (Eval.whileNil (p:=unaryScanBody) (by simp : (update (update s 0 w) 2 []) 2=[]))
    have he : update (update (update s 0 w) 1 (List.replicate 0 true++s 1)) 2 []=
        update (update s 0 w) 2 [] := by
      funext j
      fin_cases j <;> simp
    rw [he]
    exact hl
  | succ n ih =>
    let s' := update (update s 0 (List.replicate n true++false::w)) 1 (true::s 1)
    have hs : s 0=true::(List.replicate n true++false::w) := by
      simpa only [List.replicate_succ,List.cons_append] using h0
    have ht : Eval (Program.transfer (0:Fin 3) 1) s s' 1 := by
      simpa only [transfer_cons (by decide : (0:Fin 3)≠1) s true _ hs] using Eval.transfer
        (0:Fin 3) 1 s
    have hb : Eval unaryScanBody s s' 2 := Eval.branchTrue hs ht
    have hh := ih s' (by simp [s']) (by simp [s',h2])
    have he : update (update (update s' 0 w) 1 (List.replicate n true++s' 1)) 2 []=
        update (update (update s 0 w) 1 (List.replicate (n+1) true++s 1)) 2 [] := by
      funext j
      fin_cases j <;> simp [s',List.replicate_succ',List.append_assoc]
    rw [he] at hh
    have hl := Eval.whileCons (by simp [h2]) hb hh
    convert hl using 1; omega

namespace Procedure

/-- A fixed three-stack parser for the *literal*, unescaped unary input.
Its output is the ordinary typed pair coding used by the closure library. -/
def unaryInput : Procedure
    (fun a : ℕ×ℕ => ExecutableGenerator.unaryWord a.1 a.2)
    (code : Unary×Unary → List Bool) (fun a => (Unary.mk a.1,Unary.mk a.2)) where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq (.push 2 true) (.seq unaryScan (prependRecord 1 0 2))
  bound := 20*TimeBound.variable
  correct a := by
    let w := List.replicate a.2 true
    let s := single (0:Fin 3) (ExecutableGenerator.unaryWord a.1 a.2)
    have hi : Eval (Program.push (2:Fin 3) true) s (update s 2 [true]) 1 := by
      simpa [s,single] using Eval.push (2:Fin 3) true s
    have hh := eval_unaryScan a.1 w (update s 2 [true])
      (by simp [s,single,w,ExecutableGenerator.unaryWord]) (by simp)
    have he : update (update (update (update s 2 [true]) 0 w) 1
        (List.replicate a.1 true++(update s 2 [true]) 1)) 2 [] =
        both (1:Fin 3) 0 (List.replicate a.1 true) w := by
      funext j
      fin_cases j <;> simp [s,single,both]
    rw [he] at hh
    have hf := eval_prependRecord_both (a:=(1:Fin 3)) (b:=0) (tmp:=2)
      (by decide) (by decide) (by decide) (List.replicate a.1 true) w
    refine ⟨9*a.1+16,?_,?_⟩
    · simp [ExecutableGenerator.unaryWord];omega
    · have hr := Eval.seq hi (Eval.seq hh hf)
      convert hr using 1 <;> simp [w,code,pairCode,unaryCode]; omega
  size a := by
    change (pairCode unaryCode unaryCode a).length≤_
    simp [ExecutableGenerator.unaryWord,pairCode,unaryCode];omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

/-- Literal canonical output, including dimension and accepted-list length. -/
def word (p : Params) : BitWord :=
  ⟨encodeNat (p.m*p.q)++encodeNat (words p).length++(words p).flatMap BitWord.val⟩

@[fun_prop] theorem word_poly : Poly word := by
  have hd : Poly (fun p : Params => p.2.2.1*p.2.2.2.1) := by fun_prop
  have hn := Poly.encodeUnary.comp (Poly.listLength.comp words_poly)
  have he := Poly.encodeUnary.comp hd
  exact Poly.wordAppend.comp ((Poly.wordAppend.comp (he.pair hn)).pair
    (Poly.wordConcat.comp words_poly))

lemma word_eq (n s : ℕ) : (word (Params.of n s)).val=ExecutableGenerator.encoded n s := by
  unfold word
  rw [words_eq]
  simp only [List.length_map,List.flatMap_map]
  rfl

lemma word_ext {x y : BitWord} (h : x.val=y.val) : x=y := by
  cases x;cases y;congr

theorem output_poly : Poly (fun a : Unary×Unary =>
    BitWord.mk (ExecutableGenerator.encoded a.1.val a.2.val)) :=
  (word_poly.comp Poly.params).of_eq (by intro a;exact word_ext (word_eq _ _))

/-- Polynomial feasibility of the canonical output construction. -/

theorem raw_feasible : Feasible
    (fun a : ℕ×ℕ => ExecutableGenerator.unaryWord a.1 a.2)
    (fun x => x) (fun a => (ExecutableGenerator.encoded a.1 a.2).reverse) := by
  have ho : Feasible (code : Unary×Unary → List Bool) (fun x => x)
      (fun a => ExecutableGenerator.encoded a.1.val a.2.val) :=
    output_poly.recode _ _ _ (fun x => x) (by intro a;rfl) (by intro a;rfl)
  have hi := (show Feasible _ _ _ from ⟨Procedure.unaryInput⟩)
  have hm := ho.comp hi
  have hr := Feasible.reverseWord.comp hm
  exact hr.of_eq (by intro a;simp only [Function.comp_apply])

end Runtime
end RationalHitting.StackLanguage

end Complexity
