/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.ProcedurePairs

/-!
# Rational hitting lists: procedure control

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/ProcedureControl.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
namespace Procedure
variable {A B : Type} {ca : A → List Bool} {cb : B → List Bool} {f : A → B}

/-- Give a procedure a single external input/output port. The two transfers
are real stack programs; scratch registers remain clean. -/
def toPort (p : Procedure ca cb f) : Procedure ca cb f where
  Registers := p.Registers ⊕ Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inr 0
  output := Sum.inr 0
  program := .seq (move (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.rename Sum.inl) (move (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound := 5*p.bound+4*TimeBound.variable+8
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    refine ⟨1+(4*(ca a).length+3)+(1+t+(4*(cb (f a)).length+3)),?_,?_⟩
    · have hs := p.size a
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
        TimeBound.eval_variable]
      omega
    · exact Eval.seq (Eval.move_single (by simp) (by simp) (by simp) _)
        (Eval.seq (hp.rename_single Sum.inl Sum.inl_injective)
          (Eval.move_single (by simp) (by simp) (by simp) _))
  size a := by
    have hs := p.size a
    simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
    omega

end Procedure

/-- Unpack an encoded pair into the designated registers. -/
def splitPair {K : Type}  (a b tmp : K) : Program K :=
  .seq (unpackRecord.rename (threeRegs b tmp a)) (reverse tmp a)

lemma eval_splitPair {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp) (x y : List Bool) :
    Eval (splitPair a b tmp) (single b (codeWord x++y)) (both a b x y) (7*x.length+10) := by
  let f := threeRegs b tmp a
  have hf : Injective f := threeRegs_inj hbt hab.symm hat.symm
  have he := (eval_unpack_pair x y).rename f hf (fun _ => [])
  have hx : extend f (both (0 : Fin 3) 1 y x.reverse) (fun _ => [])=both b tmp y x.reverse := by
    simp only [both,extend_update_store f hf,extend_single f hf]
    rfl
  rw [extend_single f hf,hx] at he
  have hrev := eval_reverse hat.symm (both b tmp y x.reverse)
  have heq : update (update (both b tmp y x.reverse) tmp []) a
      ((both b tmp y x.reverse tmp).reverse++both b tmp y x.reverse a)=both a b x y := by
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=tmp <;>
      simp_all [both,single]
  rw [heq] at hrev
  have hh := Eval.seq he hrev
  convert hh using 1 <;> simp [splitPair,f,threeRegs,both] ; omega

lemma extend_both {K L : Type} [DecidableEq K] [DecidableEq L] (f : K → L) (hf : Injective f)
    (i j : K) (x y : List Bool) :
    extend f (both i j x y) (fun _ => [])=both (f i) (f j) x y := by
  simp only [both,extend_update_store f hf,extend_single f hf]

namespace Procedure
variable {A B C K : Type} [Fintype K] [DecidableEq K]
  {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool} {f : A×B → C}

/-- Package an independently proved two-input clean register routine as a
serialized procedure. Its polynomial bound is not an operation oracle: the
actual Eval proof is required. -/
def fromBinary (p : Program K) (i j o : K) (hij : i≠j) (bnd : TimeBound)
    (hp : ∀ a b, ∃ t ≤ bnd.eval ((ca a).length+(cb b).length+1),
      Eval p (both i j (ca a) (cb b)) (single o (cc (f (a,b)))) t)
    (hs : ∀ a b, (cc (f (a,b))).length ≤ bnd.eval ((ca a).length+(cb b).length+1)) :
    Procedure (pairCode ca cb) cc f where
  Registers := K ⊕ Unit
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl j
  output := Sum.inl o
  program := .seq (splitPair (Sum.inl i) (Sum.inl j) (Sum.inr ())) (p.rename Sum.inl)
  bound := bnd + 7*TimeBound.variable+12
  correct a := by
    obtain ⟨t,ht,he⟩ := hp a.1 a.2
    refine ⟨1+(7*(ca a.1).length+10)+t,?_,?_⟩
    · have hh : (ca a.1).length+(cb a.2).length+1 ≤ (pairCode ca cb a).length+1 := by simp; omega
      have ht' := ht.trans (bnd.monotone hh)
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
        TimeBound.eval_variable]
      simp only [pairCode_length] at *
      omega
    · exact Eval.seq (eval_splitPair (by simpa using hij) (by simp) (by simp) _ _)
        (by
          simpa only [extend_single Sum.inl Sum.inl_injective,
            extend_both Sum.inl Sum.inl_injective]
            using he.rename (Sum.inl : K → K ⊕ Unit) Sum.inl_injective (fun _ => []))
  size a := by
    have hh : (ca a.1).length+(cb a.2).length+1 ≤ (pairCode ca cb a).length+1 := by simp; omega
    have ht := (hs a.1 a.2).trans (bnd.monotone hh)
    simp only [Prod.mk.eta] at ht
    simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_variable]
    omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- The one-bit encoding of a Boolean value. -/
def boolCode (b : Bool) : List Bool := [b]
@[simp] lemma boolCode_length (b : Bool) : (boolCode b).length=1 := rfl

namespace Procedure
variable {A B K : Type} [Fintype K] [DecidableEq K]
  {ca : A → List Bool} {cb : B → List Bool} {f g : A → B}

/-- Embed a procedure in a larger finite register type. -/
def rename (p : Procedure ca cb f) (e : p.Registers → K) (he : Injective e) : Procedure ca cb f
    where
  Registers := K
  finite := inferInstance
  decEq := inferInstance
  input := e p.input
  output := e p.output
  program := p.program.rename e
  bound := p.bound
  correct a := by
    obtain ⟨t,ht,he'⟩ := p.correct a
    exact ⟨t,ht,he'.rename_single e he⟩
  size := p.size

/-- Deterministic Boolean branching on a serialized pair. Only the selected
finite subprogram runs; the tag is physically consumed. -/
def branch (p : Procedure ca cb f) (q : Procedure ca cb g) :
    Procedure (pairCode boolCode ca) cb (fun a => if a.1 then f a.2 else g a.2) := by
  let R := (p.Registers ⊕ q.Registers) ⊕ Fin 3
  let e₁ : p.toPort.Registers → R := Sum.map Sum.inl Fin.castSucc
  let e₂ : q.toPort.Registers → R := Sum.map Sum.inr Fin.castSucc
  have he₁ : Injective e₁ := Sum.inl_injective.sumMap (Fin.castSucc_injective 2)
  have he₂ : Injective e₂ := Sum.inr_injective.sumMap (Fin.castSucc_injective 2)
  let p' := p.toPort.rename e₁ he₁
  let q' := q.toPort.rename e₂ he₂
  let port : R := Sum.inr 0
  let flag : R := Sum.inr 2
  let tmp : R := Sum.inr 1
  have hfp : flag≠port := by simp [flag,port,R]
  have hft : flag≠tmp := by simp [flag,tmp,R]
  have hpt : port≠tmp := by simp [port,tmp,R]
  have hp : p'.input=port ∧ p'.output=port := ⟨rfl,rfl⟩
  have hq : q'.input=port ∧ q'.output=port := ⟨rfl,rfl⟩
  let P := Program.seq (splitPair flag port tmp)
    (.branch flag .skip (.seq (.drop flag) q'.program) (.seq (.drop flag) p'.program))
  refine {
    Registers := R
    finite := inferInstance
    decEq := inferInstance
    input := port
    output := port
    program := P
    bound := p'.bound+q'.bound+25
    correct := ?_
    size := ?_ }
  · intro a
    have hs := eval_splitPair (a:=flag) (b:=port) (tmp:=tmp) hfp hft hpt
      (boolCode a.1) (ca a.2)
    simp only [boolCode_length] at hs
    have hd : Eval (.drop flag) (both flag port (boolCode a.1) (ca a.2)) (single port (ca a.2))
      1 := by
      have hh := Eval.drop flag (both flag port (boolCode a.1) (ca a.2))
      have hx : update (both flag port (boolCode a.1) (ca a.2)) flag [] = single port (ca a.2) := by
        rw [both_comm hfp]
        simp only [both,update_idem]
        exact update_eq_self_iff.mpr (by simp [hfp])
      rw [both_first hfp] at hh
      change Eval _ _ (update (both flag port (boolCode a.1) (ca a.2)) flag []) 1 at hh
      rw [hx] at hh
      exact hh
    have hlen : (ca a.2).length+1≤(pairCode boolCode ca a).length+1 := by simp
    cases hb : a.1 with
    | false =>
      obtain ⟨t,ht,he⟩ := q'.correct a.2
      rw [hq.1,hq.2] at he
      refine ⟨1+17+(1+(1+1+t)),?_,?_⟩
      · have ht' := ht.trans (q'.bound.monotone hlen)
        simp only [TimeBound.eval_add,TimeBound.eval_numeral]
        omega
      · simp only [Bool.false_eq_true,↓reduceIte]
        exact Eval.seq hs (Eval.branchFalse (ls:=[]) (by simp only [both_first hfp,boolCode,hb])
          (Eval.seq hd he))
    | true =>
      obtain ⟨t,ht,he⟩ := p'.correct a.2
      rw [hp.1,hp.2] at he
      refine ⟨1+17+(1+(1+1+t)),?_,?_⟩
      · have ht' := ht.trans (p'.bound.monotone hlen)
        simp only [TimeBound.eval_add,TimeBound.eval_numeral]
        omega
      · simp only [↓reduceIte]
        exact Eval.seq hs (Eval.branchTrue (ls:=[]) (by simp only [both_first hfp,boolCode,hb])
          (Eval.seq hd he))
  · intro a
    have hlen : (ca a.2).length+1≤(pairCode boolCode ca a).length+1 := by simp
    have h₁ := (p'.size a.2).trans (p'.bound.monotone hlen)
    have h₂ := (q'.size a.2).trans (q'.bound.monotone hlen)
    simp only [TimeBound.eval_add,TimeBound.eval_numeral]
    split <;> omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

/-- Unary loop count. These symbols are explicitly popped by the loop body. -/
def unaryCode (n : ℕ) : List Bool := List.replicate n true
@[simp] lemma unaryCode_length (n : ℕ) : (unaryCode n).length=n := by simp [unaryCode]
@[simp] lemma unaryCode_zero : unaryCode 0=[] := rfl
@[simp] lemma unaryCode_succ (n : ℕ) : unaryCode (n+1)=true::unaryCode n := rfl

namespace Procedure
variable {A : Type} {ca : A → List Bool} {f : A → A}

/-- Repeat a procedure using a separate unary counter register. -/
def iterateProgram (p : Procedure ca ca f) : Program (p.Registers ⊕ Unit) :=
  .loop (Sum.inr ()) (.seq (p.program.rename Sum.inl) (.drop (Sum.inr ())))

lemma eval_iterateProgram (p : Procedure ca ca f) (hport : p.output=p.input)
    (n : ℕ) (a : A) (B : ℕ) (hb : ∀ i≤n, (ca (f^[i] a)).length≤B) :
    ∃ t≤n*(p.bound.eval (B+1)+3)+1,
    Eval (iterateProgram p) (both (Sum.inl p.input) (Sum.inr ()) (ca a) (unaryCode n))
      (single (Sum.inl p.input) (ca (f^[n] a))) t := by
  induction n generalizing a with
  | zero =>
    refine ⟨1,by simp,?_⟩
    simpa only [unaryCode_zero,both_nil_right (by simp : (Sum.inl p.input : p.Registers ⊕
      Unit)≠Sum.inr ()),iterate_zero,id_eq,iterateProgram] using
      (Eval.whileNil (p:=.seq (p.program.rename Sum.inl) (.drop (Sum.inr ())))
        (show both (Sum.inl p.input) (Sum.inr ()) (ca a) [] (Sum.inr ())=[] by simp))
  | succ n ih =>
    obtain ⟨u,hu,he⟩ := p.correct a
    have hsize := hb 0 (by omega)
    simp only [iterate_zero,id_eq] at hsize
    have hu' := hu.trans (p.bound.monotone (Nat.add_le_add_right hsize 1))
    have hb' : ∀ i≤n, (ca (f^[i] (f a))).length≤B := by
      intro i hi
      simpa only [iterate_succ_apply] using hb (i+1) (by omega)
    obtain ⟨v,hv,hev⟩ := ih (f a) hb'
    rw [hport] at he
    have he' := he.rename_both (Sum.inl : p.Registers → p.Registers ⊕ Unit) Sum.inl_injective
      (Sum.inr ()) (unaryCode (n+1)) (by intro k; simp)
    have hd : Eval (.drop (Sum.inr ()))
        (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode (n+1)))
        (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode n)) 1 := by
      simpa only [both,both_second,unaryCode_succ,List.tail_cons,update_self,update_idem] using
        Eval.drop (Sum.inr ()) (both (Sum.inl p.input) (Sum.inr ()) (ca (f a)) (unaryCode (n+1)))
    refine ⟨1+(1+u+1)+v,?_,?_⟩
    · nlinarith only [hu',hv]
    · have hh := Eval.whileCons (by simp :
        both (Sum.inl p.input) (Sum.inr ()) (ca a) (unaryCode (n+1)) (Sum.inr ())≠[])
        (Eval.seq he' hd) hev
      simpa only [iterateProgram,iterate_succ_apply] using hh

/-- Bounded iteration is compiled to a real finite loop. The semantic size
invariant is a proof obligation, not a loop oracle or added main hypothesis. -/
def iterate (p : Procedure ca ca f) (Q : TimeBound)
    (hQ : ∀ (n : ℕ) (a : A) (i : ℕ), i≤n →
      (ca (f^[i] a)).length≤Q.eval ((pairCode unaryCode ca (n,a)).length+1)) :
    Procedure (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := by
  let q := p.toPort
  let r : Procedure (pairCode unaryCode ca) ca (fun a => f^[a.1] a.2) := {
    Registers := (q.Registers ⊕ Unit) ⊕ Unit
    finite := inferInstance
    decEq := inferInstance
    input := Sum.inl (Sum.inl q.input)
    output := Sum.inl (Sum.inl q.input)
    program := .seq (splitPair (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl q.input)) (Sum.inr ()))
      ((iterateProgram q).rename Sum.inl)
    bound := TimeBound.variable*(q.bound.comp (Q+1)+3)+7*TimeBound.variable+Q+12
    correct a := by
      obtain ⟨t,ht,he⟩ := eval_iterateProgram q rfl a.1 a.2
        (Q.eval ((pairCode unaryCode ca a).length+1)) (by simpa only [Prod.mk.eta] using hQ a.1 a.2)
      refine ⟨1+(7*a.1+10)+t,?_,?_⟩
      · have hn : a.1 ≤ (pairCode unaryCode ca a).length+1 := by simp; omega
        have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
        simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
          TimeBound.eval_variable,TimeBound.eval_comp]
        omega
      · have hs := eval_splitPair (tmp:=Sum.inr ()) (by simp : (Sum.inl (Sum.inr ()) :
        (q.Registers ⊕ Unit) ⊕ Unit)≠Sum.inl (Sum.inl q.input))
          (by simp) (by simp) (unaryCode a.1) (ca a.2)
        simp only [unaryCode_length] at hs
        rw [both_comm (by simp : (Sum.inl (Sum.inr ()) : (q.Registers ⊕ Unit) ⊕ Unit)≠Sum.inl
          (Sum.inl q.input))] at hs
        exact Eval.seq hs (by
          simpa only [extend_both Sum.inl Sum.inl_injective,
            extend_single Sum.inl Sum.inl_injective] using
            he.rename (Sum.inl : (q.Registers ⊕ Unit) → (q.Registers ⊕ Unit) ⊕ Unit)
              Sum.inl_injective (fun _ => []))
    size a := by
      have hs := hQ a.1 a.2 a.1 le_rfl
      simp only [Prod.mk.eta] at hs
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
          TimeBound.eval_variable,TimeBound.eval_comp]
      omega }
  exact r

end Procedure
end RationalHitting.StackLanguage

end Complexity
