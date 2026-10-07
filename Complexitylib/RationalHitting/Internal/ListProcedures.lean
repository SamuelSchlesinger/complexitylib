/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Tabulation

/-!
# Rational hitting lists: list procedures

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/ListProcedures.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function

namespace Procedure

/-- Append an empty list component to a coded value. -/
def padEmpty (w : List Bool) : Procedure (fun x => x) (fun x => x)
    (fun a : List Bool => if a=[] then w else a) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .branch () (pushWord () w) .skip .skip
  bound := TimeBound.variable+TimeBound.const (2*w.length+3)
  correct a := by
    cases a with
    | nil =>
      refine ⟨1+(2*w.length+1),by simp,?_⟩
      have h := eval_pushWord () w (single () [])
      simp only [single_self,List.append_nil] at h
      have e : update (single () []) () w=single () w := by simp [single]
      rw [e] at h
      exact Eval.branchNone (by simp) h
    | cons b a =>
      refine ⟨2,by simp; omega,?_⟩
      cases b
      · exact Eval.branchFalse (ls:=a) (by simp [single]) (Eval.skip _)
      · exact Eval.branchTrue (ls:=a) (by simp [single]) (Eval.skip _)
  size a := by split_ifs <;> simp_all <;> omega

/-- Test whether a raw input word is empty. -/
def wordEmpty : Procedure (fun x => x) boolCode (fun a : List Bool => a.isEmpty) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .branch () (.push () true) (.seq (clear ()) (.push () false))
    (.seq (clear ()) (.push () false))
  bound := 2*TimeBound.variable+4
  correct a := by
    cases a with
    | nil =>
      refine ⟨2,by simp,?_⟩
      have h : Eval (.push () true) (single () []) (single () (boolCode true)) 1 := by
        simpa [single,boolCode] using Eval.push () true (single () [])
      exact Eval.branchNone (by simp) h
    | cons b a =>
      have h := Eval.seq (eval_clear_single () (b::a)) (Eval.push () false (fun _ : Unit => []))
      have h' : Eval (.seq (clear ()) (.push () false)) (single () (b::a))
          (single () (boolCode false)) (2*(b::a).length+3) := by
        convert h using 1 <;> simp [single,boolCode]; omega
      refine ⟨1+(2*(b::a).length+3),by simp; omega,?_⟩
      cases b
      · exact Eval.branchFalse (ls:=a) (by simp [single]) h'
      · exact Eval.branchTrue (ls:=a) (by simp [single]) h'
  size a := by simp

end Procedure

namespace Feasible
variable {A : Type} (ca : A → List Bool)

theorem listUncons (z : A) : Feasible (listCode ca) (pairCode ca (listCode ca))
    (fun a => (a.headD z,a.tail)) := by
  refine (show Feasible (fun x => x) (fun x => x) _ from ⟨Procedure.padEmpty (codeWord (ca
    z))⟩).recode
    _ _ _ (listCode ca) (by intro a; rfl) ?_
  intro a
  cases a with
  | nil => simp [pairCode]
  | cons b a =>
    have hne : codeWord (ca b)++listCode ca a≠[] := by
      intro h
      have := congrArg List.length h
      simp at this
    simp [pairCode,hne]

theorem listTail (z : A) : Feasible (listCode ca) (listCode ca) List.tail :=
  (snd ca (listCode ca)).comp (listUncons ca z)

theorem listHeadD (z : A) : Feasible (listCode ca) ca (fun a => a.headD z) :=
  (fst ca (listCode ca)).comp (listUncons ca z)

theorem listEmpty : Feasible (listCode ca) boolCode (List.isEmpty : List A → Bool) := by
  refine (show Feasible (fun x => x) boolCode _ from ⟨Procedure.wordEmpty⟩).recode
    _ _ _ (listCode ca) (by intro a; rfl) ?_
  intro a
  cases a with
  | nil => rfl
  | cons b a =>
    cases h : ca b <;> simp [listCode,codeWord,h]

end Feasible

lemma listCode_tail_le {A : Type} (ca : A → List Bool) (a : List A) :
    (listCode ca a.tail).length≤(listCode ca a).length := by
  cases a <;> simp

lemma listCode_iterate_tail_le {A : Type} (ca : A → List Bool) (a : List A) (n : ℕ) :
    (listCode ca (List.tail^[n] a)).length≤(listCode ca a).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    exact (listCode_tail_le ca _).trans ih

namespace Poly
variable {A : Type} [Coding A]

@[fun_prop] theorem listTail [Inhabited A] : Poly (List.tail : List A → List A) :=
  Feasible.listTail code default
@[fun_prop] theorem listHeadD (z : A) : Poly (fun a : List A => a.headD z) :=
  Feasible.listHeadD code z
@[fun_prop] theorem listEmpty : Poly (List.isEmpty : List A → Bool) := Feasible.listEmpty code

theorem iterate {f : A → A} (hf : Poly f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (code (f^[i] a)).length≤Q.eval ((pairCode unaryCode code (n,a)).length+1)) :
    Poly (fun a : Unary×A => f^[a.1.val] a.2) :=
  (Feasible.iterate hf Q hQ).recode _ _ _ (fun a => (a.1.val,a.2))
    (by intro a; rfl) (by intro a; rfl)

theorem listDrop [Inhabited A] : Poly (fun a : Unary×List A => a.2.drop a.1.val) := by
  have hh := (listTail (A:=A)).iterate TimeBound.variable (by
    intro n a i hi
    have h := listCode_iterate_tail_le (code : A → List Bool) a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    change (listCode code (List.tail^[i] a)).length≤_ at ⊢
    change _≤2*n+1+(listCode code a).length+1
    omega)
  refine hh.of_eq ?_
  intro a
  exact List.tail_iterate _ _

theorem listGetD [Inhabited A] (z : A) :
    Poly (fun a : Unary×List A => (a.2.drop a.1.val).headD z) :=
  (listHeadD z).comp listDrop

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- Count record delimiters, skipping both the escape bit and payload bit. -/
def recordCount : List Bool → ℕ
  | [] => 0
  | true::w => recordCount w+1
  | false::[] => 0
  | false::_::w => recordCount w

@[simp] lemma recordCount_false (w : List Bool) : recordCount (false::w)=recordCount w.tail := by
  cases w <;> rfl

/-- Consume one encoded record and increment a unary length counter. -/
def countRecordsBody : Program (Fin 2) :=
  .branch 0 .skip (.seq (.drop 0) (.drop 0)) (.seq (.drop 0) (.push 1 true))
/-- Count all records in an encoded list. -/
def countRecords : Program (Fin 2) := .loop 0 countRecordsBody

lemma drop_both_left (w v : List Bool) :
    Eval (.drop (0 : Fin 2)) (both 0 1 w v) (both 0 1 w.tail v) 1 := by
  convert Eval.drop (0 : Fin 2) (both 0 1 w v) using 1
  funext k; fin_cases k <;> simp [both,single]
lemma push_both_right (w v : List Bool) (b : Bool) :
    Eval (.push (1 : Fin 2) b) (both 0 1 w v) (both 0 1 w (b::v)) 1 := by
  simpa [both] using Eval.push (1 : Fin 2) b (both 0 1 w v)

lemma eval_countRecords (w v : List Bool) : ∃ t≤5*w.length+1,
    Eval countRecords (both 0 1 w v)
      (single 1 (unaryCode (recordCount w)++v)) t := by
  cases w with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa [countRecords,both,single,recordCount,unaryCode] using
      (Eval.whileNil (p:=countRecordsBody) (show both (0 : Fin 2) 1 [] v 0=[] by simp [both,
        single]))
  | cons b w =>
    cases b with
    | false =>
      obtain ⟨t,ht,he⟩ := eval_countRecords w.tail v
      have hb : Eval countRecordsBody (both 0 1 (false::w) v) (both 0 1 w.tail v) 4 :=
        Eval.branchFalse (ls:=w) (by simp [both,single])
          (Eval.seq (drop_both_left (false::w) v) (drop_both_left w v))
      refine ⟨1+4+t,?_,?_⟩
      · simp at ht ⊢; omega
      · simpa only [recordCount_false,countRecords] using Eval.whileCons (by simp [both,single])
          hb he
    | true =>
      obtain ⟨t,ht,he⟩ := eval_countRecords w (true::v)
      have hb : Eval countRecordsBody (both 0 1 (true::w) v) (both 0 1 w (true::v)) 4 :=
        Eval.branchTrue (ls:=w) (by simp [both,single])
          (Eval.seq (drop_both_left (true::w) v) (push_both_right w v true))
      have hout : unaryCode (recordCount w)++true::v=unaryCode (recordCount (true::w))++v := by
        simp only [recordCount,unaryCode,List.replicate_add,List.replicate_one,List.append_assoc,
          List.singleton_append]
      rw [hout] at he
      exact ⟨1+4+t,by simp at ht ⊢;omega,Eval.whileCons (by simp [both,single]) hb he⟩
termination_by w.length

lemma recordCount_codeWord (w tail : List Bool) :
    recordCount (codeWord w++tail)=recordCount tail+1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [codeWord,recordCount] using ih

lemma recordCount_listCode {A : Type} (ca : A → List Bool) (l : List A) :
    recordCount (listCode ca l)=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [recordCount_codeWord,ih]

namespace Procedure

/-- A polynomially bounded procedure computing encoded list length in unary. -/
def listLength {A : Type} (ca : A → List Bool) : Procedure (listCode ca) unaryCode List.length where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := countRecords
  bound := 5*TimeBound.variable+1
  correct a := by
    obtain ⟨t,ht,he⟩ := eval_countRecords (listCode ca a) []
    refine ⟨t,by simp;omega,?_⟩
    simpa [both_nil_right (by decide : (0 : Fin 2)≠1),recordCount_listCode] using he
  size a := by
    have hh := length_le_listCode ca a
    simpa only [unaryCode_length,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_variable] using (by omega : a.length≤5*((listCode ca a).length+1)+1)

end Procedure
namespace Poly

@[fun_prop] theorem listLength {A : Type} [Coding A] : Poly (fun a : List A => Unary.mk a.length) :=
  (show Feasible (listCode code) unaryCode List.length from ⟨Procedure.listLength code⟩).recode
    _ _ _ (fun x => x) (by intro a; rfl) (by intro a; rfl)

end Poly
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

lemma range_map_drop_headD {A : Type} (l : List A) (z : A) :
    (List.range l.length).map (fun i => (l.drop i).headD z) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    rw [List.headD_eq_getD, List.getD_eq_getElem]
    · exact List.getElem_drop
    · simp;omega

namespace Poly
variable {A B C : Type} [Coding A] [Coding B] [Coding C]

theorem listMap [Inhabited B] {f : A×B → C} (hf : Poly f) :
    Poly (fun a : A×List B => a.2.map (fun b => f (a.1,b))) := by
  have hb : Poly (fun a : (A×List B)×Unary => (a.1.2.drop a.2.val).headD default) :=
    (listGetD (default : B)).comp (show Poly (fun a : (A×List B)×Unary => (a.2,a.1.2)) by fun_prop)
  have hg := hf.comp ((show Poly (fun a : (A×List B)×Unary => a.1.1) by fun_prop).pair hb)
  have ht := hg.tabulate.comp
    ((listLength.comp (show Poly (Prod.snd : A×List B → List B) from snd)).pair
      (show Poly (fun a : A×List B => a) from id))
  refine ht.of_eq ?_
  intro a
  have hh := congrArg (List.map (fun b => f (a.1,b))) (range_map_drop_headD a.2 default)
  rw [List.map_map] at hh
  exact hh

end Poly
end RationalHitting.StackLanguage

end Complexity
