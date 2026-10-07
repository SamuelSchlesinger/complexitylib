/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Procedures

/-!
# Rational hitting lists: procedure pairs

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/ProcedurePairs.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.StackLanguage
open Function
variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Serialization of a typed pair. Only the first field needs a delimiter. -/
def pairCode {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (p : A×B) : List Bool :=
  codeWord (ca p.1) ++ cb p.2
@[simp] lemma pairCode_length {A B : Type} (ca : A → List Bool) (cb : B → List Bool) (p : A×B) :
    (pairCode ca cb p).length=2*(ca p.1).length+1+(cb p.2).length := by
  simp [pairCode]

/-- A store with two specified registers and all other registers empty. -/
def both (a b : K) (x y : List Bool) : Store K := update (single a x) b y
@[simp] lemma both_first {a b : K} (hab : a≠b) (x y : List Bool) : both a b x y a=x := by
  simp [both,hab]
@[simp] lemma both_second (a b : K) (x y : List Bool) : both a b x y b=y := by simp [both]
lemma both_comm {a b : K} (hab : a≠b) (x y : List Bool) : both a b x y=both b a y x := by
  exact update_comm hab _ _ _
@[simp] lemma both_nil_left (a b : K) (y : List Bool) : both a b [] y=single b y := by
  simp [both,single]
@[simp] lemma both_nil_right {a b : K} (hab : a≠b) (x : List Bool) : both a b x []=single a x := by
  exact update_eq_self_iff.mpr (by simp [hab.symm])

lemma extend_single_both (f : K → L) (hf : Injective f) (i : K) (x : List Bool)
    (k : L) (y : List Bool) (hk : ∀ a, f a≠k) :
    extend f (single i x) (single k y)=both (f i) k x y := by
  funext l
  by_cases hl : ∃ a, f a=l
  · obtain ⟨a,rfl⟩ := hl
    by_cases ha : a=i
    · subst a; simp [hf.extend_apply,both,hk]
    · have hf' : f a≠f i := fun hh => ha (hf hh)
      simp [hf.extend_apply,single,both,ha,hf',hk]
  · have hli : l≠f i := fun hh => hl ⟨i,hh.symm⟩
    rw [extend_apply' _ _ _ hl]
    by_cases hlk : l=k <;> simp [both,single,hli,hlk]

lemma Eval.rename_both {p : Program K} {i o : K} {x y : List Bool} {t : ℕ}
    (h : Eval p (single i x) (single o y) t) (f : K → L) (hf : Injective f)
    (k : L) (z : List Bool) (hk : ∀ a, f a≠k) :
    Eval (p.rename f) (both (f i) k x z) (both (f o) k y z) t := by
  simpa only [extend_single_both f hf _ _ k z hk] using h.rename f hf (single k z)

lemma eval_copy_single {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp) (w : List Bool) :
    Eval (copy a b tmp) (single a w) (both a b w w) (7*w.length+7) := by
  have he : update (update (single a w) b w) tmp []=both a b w w := by
    apply update_eq_self_iff.mpr
    simp [single,hat.symm,hbt.symm]
  simpa only [single_self,single_other _ hab.symm,single_other _ hat.symm,List.length_nil,
    Nat.mul_zero,Nat.add_zero,he] using eval_copy hab hat hbt (single a w)

/-- The register map selecting three named registers. -/
def threeRegs (a b c : K) : Fin 3 → K := ![a,b,c]
lemma threeRegs_inj {K : Type}  {a b c : K} (hab : a ≠ b)
  (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (RationalHitting.StackLanguage.threeRegs a b
    c) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [threeRegs]

/-- Prefix a record in its original order, consuming the first stack. -/
def prependRecord (a b tmp : K) : Program K :=
  .seq (reverse a tmp) (packRecord.rename (threeRegs tmp b a))

lemma eval_prependRecord {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (s : Store K) (ht : s tmp=[]) :
    Eval (prependRecord a b tmp) s
      (update (update s a []) b (codeWord (s a)++s b)) (6*(s a).length+5) := by
  let f := threeRegs tmp b a
  have hf : Injective f := threeRegs_inj hbt.symm hat.symm hab.symm
  let u := update (update s a []) tmp (s a).reverse
  have h₁ : Eval (reverse a tmp) s u (2*(s a).length+1) := by
    simpa only [ht,List.append_nil] using eval_reverse hat s
  have h₂ := eval_rename_from f hf u (eval_packRecord (fun k => u (f k)))
  simp only [extend_update_store f hf,extend_pull_store f hf] at h₂
  have he : update (update u (f 0) []) (f 1) (codeWord (u (f 0)).reverse++u (f 1)) =
      update (update s a []) b (codeWord (s a)++s b) := by
    funext k
    by_cases hka : k=a <;> by_cases hkb : k=b <;> by_cases hkt : k=tmp <;>
      simp_all [u,f,threeRegs]
  rw [he] at h₂
  have hh := Eval.seq h₁ h₂
  convert hh using 1 <;> simp [prependRecord,u,f,threeRegs] ; omega

lemma eval_prependRecord_both {a b tmp : K} (hab : a≠b) (hat : a≠tmp) (hbt : b≠tmp)
    (x y : List Bool) :
    Eval (prependRecord a b tmp) (both a b x y) (single b (codeWord x++y)) (6*x.length+5) := by
  have ht : both a b x y tmp=[] := by simp [both,single,hat.symm,hbt.symm]
  have he : update (update (both a b x y) a []) b (codeWord x++y)=single b (codeWord x++y) := by
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,both_second,he] using eval_prependRecord hab hat hbt (both a b x y) ht

namespace Procedure
variable {A B C : Type} {ca : A → List Bool} {cb : B → List Bool} {cc : C → List Bool}
  {f : A → B} {g : A → C}

/-- Run two procedures on the same input and encode their pair of outputs. -/
def pair (p : Procedure ca cb f) (q : Procedure ca cc g) :
    Procedure ca (pairCode cb cc) (fun a => (f a,g a)) where
  Registers := p.Registers ⊕ (q.Registers ⊕ Unit)
  finite := inferInstance
  decEq := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (copy (Sum.inl p.input) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
    (.seq (p.program.rename Sum.inl)
      (.seq (q.program.rename (Sum.inr ∘ Sum.inl))
        (prependRecord (Sum.inl p.output) (Sum.inr (Sum.inl q.output)) (Sum.inr (Sum.inr ())))))
  bound := 7*TimeBound.variable + 7*p.bound + q.bound + 16
  correct a := by
    obtain ⟨t,ht,hp⟩ := p.correct a
    obtain ⟨u,hu,hq⟩ := q.correct a
    refine ⟨1+(7*(ca a).length+7)+(1+t+(1+u+(6*(cb (f a)).length+5))),?_,?_⟩
    · have hs := p.size a
      simp only [TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
        TimeBound.eval_variable]
      omega
    · have hp' := hp.rename_both (Sum.inl : p.Registers → p.Registers ⊕ (q.Registers ⊕ Unit))
        Sum.inl_injective (Sum.inr (Sum.inl q.input)) (ca a)
        (by intro k; simp)
      have hq' := hq.rename_both (Sum.inr ∘ Sum.inl : q.Registers → p.Registers ⊕ (q.Registers ⊕
        Unit)) (Sum.inr_injective.comp Sum.inl_injective)
        (Sum.inl p.output) (cb (f a)) (by intro k; simp)
      simp only [comp_apply] at hq'
      rw [both_comm (by simp : (Sum.inr (Sum.inl q.input) : p.Registers ⊕ (q.Registers ⊕
        Unit))≠Sum.inl p.output),
        both_comm (by simp : (Sum.inr (Sum.inl q.output) : p.Registers ⊕ (q.Registers ⊕
          Unit))≠Sum.inl p.output)] at hq'
      exact Eval.seq (eval_copy_single (by simp) (by simp) (by simp) _)
        (Eval.seq hp' (Eval.seq hq' (eval_prependRecord_both (by simp) (by simp) (by simp) _ _)))
  size a := by
    have hp := p.size a
    have hq := q.size a
    simp only [pairCode_length,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_variable]
    omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function
variable {K : Type} [DecidableEq K]

lemma eval_clear_both {a b : K} (hab : a≠b) (x y : List Bool) :
    Eval (clear a) (both a b x y) (single b y) (2*x.length+1) := by
  have he : update (both a b x y) a []=single b y := by
    funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,he] using eval_clear a (both a b x y)

lemma eval_reverse_both {a b : K} (hab : a≠b) (x y : List Bool) :
    Eval (reverse a b) (both a b x y) (single b (x.reverse++y)) (2*x.length+1) := by
  have he : update (update (both a b x y) a []) b (x.reverse++y)=single b (x.reverse++y) := by
    funext k; by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [both,single]
  simpa only [both_first hab,both_second,he] using eval_reverse hab (both a b x y)

lemma eval_reverse_single {a b : K} (hab : a≠b) (x : List Bool) :
    Eval (reverse a b) (single a x) (single b x.reverse) (2*x.length+1) := by
  simpa only [both_nil_right hab,List.append_nil] using eval_reverse_both hab x []

lemma eval_clear_single (a : K) (x : List Bool) :
    Eval (clear a) (single a x) (fun _ => []) (2*x.length+1) := by
  simpa [single,update_idem] using eval_clear a (single a x)

/-- A finite literal is written by a finite sequence; it is not a primitive
which can materialize a word of unbounded length in one step. -/
def pushWord (k : K) : List Bool → Program K
  | [] => .skip
  | b::w => .seq (pushWord k w) (.push k b)
lemma eval_pushWord (k : K) (w : List Bool) (s : Store K) :
    Eval (pushWord k w) s (update s k (w++s k)) (2*w.length+1) := by
  induction w with
  | nil => simpa [pushWord] using Eval.skip s
  | cons b w ih =>
    have hp := Eval.push k b (update s k (w++s k))
    have hh := Eval.seq ih hp
    convert hh using 1 <;> simp [pushWord]; omega

lemma eval_unpack_pair (x y : List Bool) :
    Eval unpackRecord (single (0 : Fin 3) (codeWord x++y))
      (both 0 1 y x.reverse) (5*x.length+8) := by
  have he := eval_unpackRecord x y (single (0 : Fin 3) (codeWord x++y)) (by simp) (by simp)
  have hs : update (update (update (single (0 : Fin 3) (codeWord x++y)) 0 y) 1 x.reverse) 2 [] =
      both 0 1 y x.reverse := by
    funext k; fin_cases k <;> simp [single,both]
  simpa only [single_other _ (by decide : (1 : Fin 3)≠0),List.append_nil,hs] using he

namespace Procedure
variable {A B : Type}

/-- A clean finite-stack procedure producing a constant output. -/
def const (ca : A → List Bool) (cb : B → List Bool) (b : B) : Procedure ca cb (fun _ => b) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .seq (clear ()) (pushWord () (cb b))
  bound := 2*TimeBound.variable + TimeBound.const (2*(cb b).length+3)
  correct a := by
    refine ⟨1+(2*(ca a).length+1)+(2*(cb b).length+1),?_,?_⟩
    · simp; omega
    · exact Eval.seq (eval_clear_single () _) (by
        simpa [single] using eval_pushWord () (cb b) (fun _ => []))
  size a := by simp; omega

/-- Extract the first component of an encoded pair. -/
def fst (ca : A → List Bool) (cb : B → List Bool) : Procedure (pairCode ca cb) ca Prod.fst where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 2
  program := .seq unpackRecord (.seq (clear 0) (reverse 1 2))
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*(ca a.1).length+8)+(1+(2*(cb a.2).length+1)+(2*(ca a.1).length+1)),?_,?_⟩
    · simp; omega
    · exact Eval.seq (eval_unpack_pair (ca a.1) (cb a.2))
        (Eval.seq (eval_clear_both (by decide) _ _)
          (by simpa only [List.reverse_reverse,List.length_reverse] using
            eval_reverse_single (by decide : (1 : Fin 3)≠2) (ca a.1).reverse))
  size a := by simp; omega

/-- Extract the second component of an encoded pair. -/
def snd (ca : A → List Bool) (cb : B → List Bool) : Procedure (pairCode ca cb) cb Prod.snd where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq unpackRecord (clear 1)
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*(ca a.1).length+8)+(2*(ca a.1).length+1),?_,?_⟩
    · simp; omega
    · apply Eval.seq (eval_unpack_pair (ca a.1) (cb a.2))
      rw [both_comm (by decide : (0 : Fin 3)≠1)]
      simpa only [List.length_reverse] using eval_clear_both (by decide : (1 : Fin 3)≠0) (ca
        a.1).reverse (cb a.2)
  size a := by simp; omega

/-- Concatenate the two words of an encoded pair. -/
def appendWord : Procedure (pairCode id id) id (fun p : List Bool×List Bool => p.1++p.2) where
  Registers := Fin 3
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 0
  program := .seq unpackRecord (reverse 1 0)
  bound := 12*TimeBound.variable+12
  correct a := by
    refine ⟨1+(5*a.1.length+8)+(2*a.1.length+1),?_,?_⟩
    · simp; omega
    · apply Eval.seq (eval_unpack_pair a.1 a.2)
      rw [both_comm (by decide : (0 : Fin 3)≠1)]
      simpa only [List.length_reverse,List.reverse_reverse,id_eq] using
        eval_reverse_both (by decide : (1 : Fin 3)≠0) a.1.reverse a.2
  size a := by simp; omega

/-- Reverse an input word using a clean temporary register. -/
def reverseWord : Procedure id id (List.reverse : List Bool → List Bool) where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := reverse 0 1
  bound := 2*TimeBound.variable+1
  correct a := ⟨2*a.length+1,by simp,eval_reverse_single (by decide) a⟩
  size a := by simp; omega

end Procedure
end RationalHitting.StackLanguage

end Complexity
