/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Feasibility

/-!
# Rational hitting lists: tabulation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Tabulation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

/-- Reusable dense records. Individual word lengths need not be fixed. -/
def listCode {A : Type} (ca : A → List Bool) (l : List A) : List Bool :=
  l.flatMap (fun a => codeWord (ca a))
@[simp] lemma listCode_nil {A : Type} (ca : A → List Bool) : listCode ca []=[] := rfl
@[simp] lemma listCode_cons {A : Type} (ca : A → List Bool) (a : A) (l : List A) :
    listCode ca (a::l)=codeWord (ca a)++listCode ca l := rfl
@[simp] lemma listCode_append {A : Type} (ca : A → List Bool) (l m : List A) :
    listCode ca (l++m)=listCode ca l++listCode ca m := by simp [listCode]
lemma listCode_singleton {A : Type} (ca : A → List Bool) (a : A) :
    listCode ca [a]=codeWord (ca a) := by simp
lemma length_le_listCode {A : Type} (ca : A → List Bool) (l : List A) :
    l.length≤(listCode ca l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp; omega
lemma listCode_length_le {A : Type} (ca : A → List Bool) (l : List A) (B : ℕ)
    (h : ∀ a∈l,(ca a).length≤B) : (listCode ca l).length≤l.length*(2*B+1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ht := ih (by intro b hb; exact h b (by simp [hb]))
    simp
    nlinarith only [ht,ha]
lemma listCode_element {A : Type} (ca : A → List Bool) (l : List A) (a : A) (h : a∈l) :
    (ca a).length≤(listCode ca l).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl|h
    · simp; omega
    · have ht := ih h; simp; omega

namespace Feasible
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool}

theorem listCons (ca : A → List Bool) :
    Feasible (pairCode ca (listCode ca)) (listCode ca) (fun a => a.1::a.2) :=
  (id (pairCode ca (listCode ca))).recode _ _ _ (fun x => x) (by intro a; rfl) (by intro a; rfl)

theorem listSingleton (ca : A → List Bool) : Feasible ca (listCode ca) (fun a => [a]) :=
  (listCons ca).comp ((id ca).pair (const ca (listCode ca) []))

theorem listAppend (ca : A → List Bool) :
    Feasible (pairCode (listCode ca) (listCode ca)) (listCode ca) (fun a => a.1++a.2) :=
  appendWord.recode _ _ _ (fun a => (listCode ca a.1,listCode ca a.2))
    (by intro a; rfl) (by intro a; exact (listCode_append ca a.1 a.2).symm)

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

namespace Feasible

theorem unarySucc : Feasible unaryCode unaryCode Nat.succ := by
  exact (unaryAdd.comp ((id unaryCode).pair (const unaryCode unaryCode 1))).of_eq
    (by intro n; rfl)

end Feasible

/-- A complete uniform table-building step: evaluation of a compiled callback,
indexed counter update, and append of an escaped dense record. -/
def tableStep {A B : Type} (f : A × ℕ → B) (a : A × (ℕ × List B)) : A × (ℕ × List B) :=
  (a.1, (a.2.1+1, a.2.2 ++ [f (a.1,a.2.1)]))

/-- Encode a tabulation state consisting of input, counter, and accumulated outputs. -/
def tableStateCode {A B : Type} (ca : A → List Bool) (cb : B → List Bool) :=
  pairCode ca (pairCode unaryCode (listCode cb))

@[simp] lemma tableStateCode_length {A B : Type} (ca : A → List Bool)
    (cb : B → List Bool) (a : A × (ℕ × List B)) :
    (tableStateCode ca cb a).length = 2*(ca a.1).length+2*a.2.1+(listCode cb a.2.2).length+2 := by
  simp [tableStateCode]; omega

lemma tableStep_iterate_fields {A B : Type} (f : A × ℕ → B) (a : A × (ℕ × List B)) (j : ℕ) :
    ((tableStep f)^[j] a).1 = a.1 ∧ ((tableStep f)^[j] a).2.1 = a.2.1+j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply']
    simp [tableStep,ih.1,ih.2,Nat.add_assoc]

lemma tableStep_iterate_size {A B : Type} {ca : A → List Bool} {cb : B → List Bool}
    {f : A × ℕ → B} (p : Procedure (pairCode ca unaryCode) cb f)
    (n : ℕ) (a : A × (ℕ × List B)) (j : ℕ) (hj : j≤n) :
    (tableStateCode ca cb ((tableStep f)^[j] a)).length ≤
      (TimeBound.variable*(2*p.bound+4)).eval
        ((pairCode unaryCode (tableStateCode ca cb) (n,a)).length+1) := by
  let N := (pairCode unaryCode (tableStateCode ca cb) (n,a)).length+1
  let P := p.bound.eval N
  have hN : N = 2*n+2*(ca a.1).length+2*a.2.1+(listCode cb a.2.2).length+4 := by
    dsimp [N]
    simp only [pairCode_length,unaryCode_length,tableStateCode_length]
    omega
  have hb : ∀ j≤n, (tableStateCode ca cb ((tableStep f)^[j] a)).length ≤
      (tableStateCode ca cb a).length+j*(2*P+3) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have ih := ih (by omega)
      have hh := tableStep_iterate_fields f a j
      have hf : (cb (f (((tableStep f)^[j] a).1,((tableStep f)^[j] a).2.1))).length≤P := by
        refine (p.size _).trans (p.bound.monotone ?_)
        simp only [pairCode_length,unaryCode_length,hh.1,hh.2]
        omega
      rw [iterate_succ_apply']
      simp only [tableStateCode_length,tableStep,listCode_append,
        listCode_singleton,List.length_append,codeWord_length] at *
      nlinarith only [ih,hf]
  have hb' := hb j hj
  have hbase : (tableStateCode ca cb a).length≤N := by
    rw [tableStateCode_length,hN]; omega
  have hjN : j≤N := by omega
  change _ ≤ N*(2*P+4)
  nlinarith only [hb',hbase,Nat.mul_le_mul_right (2*P+3) hjN]

lemma tableStep_iterate_start {A B : Type} (f : A × ℕ → B) (a : A) (n : ℕ) :
    (tableStep f)^[n] (a,0,[]) = (a,n,(List.range n).map (fun i => f (a,i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply',ih]
    simp [tableStep,List.range_succ]

namespace Feasible
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool} {f : A × ℕ → B}

theorem tableStep (hf : Feasible (pairCode ca unaryCode) cb f) :
    Feasible (tableStateCode ca cb) (tableStateCode ca cb) (StackLanguage.tableStep f) := by
  have ha := fst ca (pairCode unaryCode (listCode cb))
  have hr := snd ca (pairCode unaryCode (listCode cb))
  have hi := (fst unaryCode (listCode cb)).comp hr
  have hl := (snd unaryCode (listCode cb)).comp hr
  have hv := hf.comp (ha.pair hi)
  exact (ha.pair ((unarySucc.comp hi).pair
    ((listAppend cb).comp (hl.pair ((listSingleton cb).comp hv))))).of_eq (by intro a; rfl)

/-- Polynomial-time tabulation of an arbitrary polynomial-time callback.
The construction uses only one finite stack program, including all indexing,
record layout, and loop control; the counter is unary. -/
theorem tabulate (hf : Feasible (pairCode ca unaryCode) cb f) :
    Feasible (pairCode unaryCode ca) (listCode cb)
      (fun a => (List.range a.1).map (fun i => f (a.2,i))) := by
  obtain ⟨p⟩ := hf
  have ht := tableStep (show Feasible (pairCode ca unaryCode) cb f from ⟨p⟩)
  have hi := ht.iterate (TimeBound.variable*(2*p.bound+4)) (tableStep_iterate_size p)
  have ha := snd unaryCode ca
  have hn := fst unaryCode ca
  have hinit := ha.pair ((const (pairCode unaryCode ca) unaryCode 0).pair
    (const (pairCode unaryCode ca) (listCode cb) []))
  have he := hi.comp (hn.pair hinit)
  have ho := ((snd unaryCode (listCode cb)).comp (snd ca (pairCode unaryCode (listCode
    cb)))).comp he
  exact ho.of_eq (by intro a; simp only [comp_apply,tableStep_iterate_start])

end Feasible
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

/-- Canonical storage format for the compositional finite-program proofs. -/
class Coding (A : Type) where
  /-- The canonical Boolean encoding. -/
  code : A → List Bool
export Coding (code)

instance : Coding ℕ := ⟨Nat.bits⟩
instance : Coding Bool := ⟨boolCode⟩
instance {A B : Type} [Coding A] [Coding B] : Coding (A×B) := ⟨pairCode code code⟩
instance {A : Type} [Coding A] : Coding (List A) := ⟨listCode code⟩
instance {A : Type} [Coding A] (P : A → Prop) : Coding {a // P a} := ⟨fun a => code a.val⟩

/-- A natural number whose computation interface uses unary encoding. -/
structure Unary where
  /-- The natural number represented in unary. -/
  val : ℕ
  deriving DecidableEq
instance : Coding Unary := ⟨fun n => unaryCode n.val⟩

/-- A Boolean word whose computation interface uses its raw bits. -/
structure BitWord where
  /-- The raw Boolean word. -/
  val : List Bool
  deriving DecidableEq
instance : Coding BitWord := ⟨BitWord.val⟩

/-- Polynomial time means a concrete finite clean stack program and actual
step bound, through Procedure. It is not machine advice or an oracle. -/
@[fun_prop] def Poly {A B : Type} [Coding A] [Coding B] (f : A → B) : Prop :=
  Feasible code code f

namespace Poly
open Function
variable {A B C D : Type} [Coding A] [Coding B] [Coding C] [Coding D]

@[fun_prop] theorem id : Poly (fun a : A => a) := Feasible.id code
@[fun_prop] theorem const (b : B) : Poly (fun _ : A => b) := Feasible.const code code b
@[fun_prop] theorem comp {f : A → B} {g : B → C} (hg : Poly g) (hf : Poly f) :
    Poly (fun a => g (f a)) := Feasible.comp hg hf
@[fun_prop] theorem pair {f : A → B} {g : A → C} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => (f a,g a)) := Feasible.pair hf hg
@[fun_prop] theorem fst : Poly (Prod.fst : A×B → A) := Feasible.fst code code
@[fun_prop] theorem snd : Poly (Prod.snd : A×B → B) := Feasible.snd code code
@[fun_prop] theorem subtypeVal (P : A → Prop) : Poly (Subtype.val : {a // P a} → A) :=
  (Feasible.id (code : A → List Bool)).recode _ _ _ Subtype.val (by intro a; rfl) (by intro a; rfl)

theorem subtypeMk {f : A → B} {P : B → Prop} (hf : Poly f) (h : ∀ a,P (f a)) :
    Poly (fun a => (⟨f a,h a⟩ : {b // P b})) :=
  hf.recode _ _ _ (fun x => x) (by intro a; rfl) (by intro a; rfl)

theorem of_eq {f g : A → B} (hf : Poly f) (h : ∀ a,f a=g a) : Poly g :=
  Feasible.of_eq hf h

@[fun_prop] theorem cond {c : A → Bool} {f g : A → B} (hc : Poly c)
    (hf : Poly f) (hg : Poly g) : Poly (fun a => if c a then f a else g a) :=
  Feasible.cond hc hf hg

@[fun_prop] theorem natAdd : Poly (fun a : ℕ×ℕ => a.1+a.2) := Feasible.binaryAdd
@[fun_prop] theorem natMul : Poly (fun a : ℕ×ℕ => a.1*a.2) := Feasible.binaryMul

@[fun_prop] theorem unarySucc : Poly (fun a : Unary => Unary.mk (a.val+1)) :=
  Feasible.unarySucc.recode _ _ _ Unary.val (by intro a; rfl) (by intro a; rfl)
@[fun_prop] theorem unaryAdd : Poly (fun a : Unary×Unary => Unary.mk (a.1.val+a.2.val)) :=
  Feasible.unaryAdd.recode _ _ _ (fun a => (a.1.val,a.2.val)) (by intro a; rfl) (by intro a; rfl)

@[fun_prop] theorem listCons : Poly (fun a : A×List A => a.1::a.2) := Feasible.listCons code
@[fun_prop] theorem listSingleton : Poly (fun a : A => [a]) := Feasible.listSingleton code
@[fun_prop] theorem listAppend : Poly (fun a : List A×List A => a.1++a.2) := Feasible.listAppend
    code
@[fun_prop] theorem wordAppend : Poly (fun a : BitWord×BitWord => BitWord.mk (a.1.val++a.2.val)) :=
  Feasible.appendWord.recode _ _ _ (fun a => (a.1.val,a.2.val)) (by intro a; rfl) (by intro a; rfl)

theorem tabulate {f : A×Unary → B} (hf : Poly f) :
    Poly (fun a : Unary×A => (List.range a.1.val).map (fun i => f (a.2,⟨i⟩))) := by
  have h := hf.recode (pairCode (code : A→List Bool) unaryCode) code
    (fun a : A×ℕ => f (a.1,⟨a.2⟩)) (fun a => (a.1,Unary.mk a.2))
    (by intro a; rfl) (by intro a; rfl)
  exact h.tabulate.recode _ _ _ (fun a => (a.1.val,a.2)) (by intro a; rfl) (by intro a; rfl)

example : Poly (fun a : ℕ×ℕ => a.1*a.2+a.2) := by fun_prop
example : Poly (fun a : (ℕ×ℕ)×ℕ => (a.1.1+a.2,a.1.2*a.2)) := by fun_prop

end Poly
end RationalHitting.StackLanguage

end Complexity
