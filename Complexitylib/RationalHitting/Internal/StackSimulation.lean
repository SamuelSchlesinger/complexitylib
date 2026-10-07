/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.StackLanguage

/-!
# Rational hitting lists: stack simulation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/StackSimulation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.TMTime.StackToOne
open Turing Turing.TM2to1
open TM2to1.Λ'
open Function
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
variable [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ)

lemma go_time {k} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n ≤ S.length) :
    exec (TM1.step (tr M)) n ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩ =
      some ⟨some (go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply exec_trans (ih (by omega))
    simp only [exec,TM1.step,Option.bind_some,TM1.stepAux,tr,
      Tape.mk'_nth_nat,Tape.move_right_n_head,addBottom_nth_snd]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem (by simpa using H)]
    simp only [Option.isNone_some,Bool.cond_false]
    rw [iterate_succ_apply']

lemma return_time {q v} {L : ListBlank (∀ k, Option (Γ k))} (n : ℕ) :
    exec (TM1.step (tr M)) n
      ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hstep : TM1.step (tr M)
        ⟨some (ret q),v,(Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [TM1.step]
      congr 1
      rw [tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,TM1.stepAux,iterate_succ',Function.comp_apply,Tape.move_right_left]
      rfl
    rw [exec,hstep,Option.bind_some]
    exact ih

/-- Number of stack-access operations in a compiled statement. -/
def stackWeight : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q => stackWeight q+1
  | .load _ q => stackWeight q
  | .branch _ q r => max (stackWeight q) (stackWeight r)
  | .goto _ | .halt => 0

lemma stackWeight_run.{v_1, v_2, v_3, v_4} {K : Type v_1}
  {Γ : K → Type v_2} {Λ : Type v_3} {σ : Type v_4}  {k : K}
  (o : Turing.TM2to1.StAct K Γ σ k) (q : Turing.TM2.Stmt Γ Λ σ) :
  RationalHitting.TMTime.StackToOne.stackWeight (Turing.TM2to1.stRun o q) =
    RationalHitting.TMTime.StackToOne.stackWeight q + 1 := by cases o <;> rfl

lemma stWrite_length.{v_1, v_2, v_4} {K : Type v_1} {Γ : K → Type v_2}
  {σ : Type v_4}  {k : K} (o : Turing.TM2to1.StAct K Γ σ k) (v : σ)
  (l : List (Γ k)) : (Turing.TM2to1.stWrite v l o).length ≤ l.length + 1 := by
  cases o <;> simp [stWrite,List.length_tail] ; omega

lemma updated_length {k : K} (o : StAct K Γ σ k) (v : σ)
    (S : ∀ k, List (Γ k)) (L : ℕ) (hS : ∀ k, (S k).length ≤ L) :
    ∀ j, (update S k (stWrite v (S k) o) j).length ≤ L+1 := by
  intro j
  by_cases h : j = k
  · subst j
    rw [Function.update_self]
    exact (stWrite_length o v (S k)).trans (Nat.add_le_add_right (hS k) 1)
  · rw [Function.update_of_ne h]
    exact (hS j).trans (by omega)

/-- Real TM1 transition count for the compiled continuation of a TM2 statement.
The multipliers count sweeps to and from actual stack tops. -/
theorem continuation_time (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (T : ListBlank (∀ k, Option (Γ k))) (L : ℕ)
    (hT : ∀ k, T.map (proj k) = ListBlank.mk ((S k).map some).reverse)
    (hS : ∀ k, (S k).length ≤ L) :
    ∃ u b, u ≤ stackWeight q*(2*(L+stackWeight q)+3) ∧
      TrCfg (TM2.stepAux q v S) b ∧
      exec (TM1.step (tr M)) u (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) = some b
        := by
  induction q using stmtStRec generalizing v S T L with
  | run k o q ih =>
    have hg := go_time M o q v (hT k) (S k).length le_rfl
    obtain ⟨T',hT',hact⟩ := tr_respects_aux₂ (Λ := Λ) hT o
    have hactStep : exec (TM1.step (tr M)) 1
        ⟨some (go k o q),v,(Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom T))⟩ =
        some ⟨some (ret q),stVar v (S k) o,
          (Tape.move Dir.right)^[(stWrite v (S k) o).length] (Tape.mk' ∅ (addBottom T'))⟩ := by
      simp only [exec,TM1.step,Option.bind_some,tr,TM1.stepAux,
        Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
        stk_nth_val _ (hT k),List.getElem?_eq_none (le_of_eq List.length_reverse),
        Option.isNone_none,Bool.cond_true]
      rw [hact]
      simp only [TM1.stepAux,Function.update_self]
    have hr := return_time M (q := q) (v := stVar v (S k) o) (L := T') (stWrite v (S k) o).length
    obtain ⟨u,b,hu,hb,he⟩ := ih _ _ _ (L+1) hT' (updated_length o v S L hS)
    refine ⟨(S k).length+1+(stWrite v (S k) o).length+1+u,b,?_,?_,?_⟩
    · rw [stackWeight_run]
      have hl := hS k
      have hs := stWrite_length o v (S k)
      nlinarith
    · simpa only [step_run] using hb
    · simp only [trNormal_run,TM1.stepAux]
      rw [show (S k).length+1+(stWrite v (S k) o).length+1+u =
        (S k).length+1+(stWrite v (S k) o).length+(1+u) by omega]
      apply exec_trans (exec_trans (exec_trans hg hactStep) hr)
      change exec (TM1.step (tr M)) (1+u) _ = some b
      rw [exec_add]
      simpa only [exec,TM1.step,Option.bind_some,exec_zero,tr,TM1.stepAux,
        Tape.mk'_head,addBottom_head_fst,Bool.cond_true] using he
  | load f q ih =>
    simpa only [TM2.stepAux,trNormal,TM1.stepAux,stackWeight] using ih (f v) S T
      L hT hS
  | branch f q r iq ir =>
    cases hh : f v with
    | false =>
      obtain ⟨u,b,hu,hb,he⟩ := ir v S T L hT hS
      refine ⟨u,b,?_,?_,?_⟩
      · simp only [stackWeight]
        apply hu.trans
        exact Nat.mul_le_mul (Nat.le_max_right _ _) (by omega)
      · simpa [TM2.stepAux,hh] using hb
      · simpa [trNormal,TM1.stepAux,hh] using he
    | true =>
      obtain ⟨u,b,hu,hb,he⟩ := iq v S T L hT hS
      refine ⟨u,b,?_,?_,?_⟩
      · simp only [stackWeight]
        apply hu.trans
        exact Nat.mul_le_mul (Nat.le_max_left _ _) (by omega)
      · simpa [TM2.stepAux,hh] using hb
      · simpa [trNormal,TM1.stepAux,hh] using he
  | goto f => exact ⟨0,_,by simp [stackWeight],TrCfg.mk T hT,rfl⟩
  | halt => exact ⟨0,_,by simp [stackWeight],TrCfg.mk T hT,rfl⟩

lemma statement_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k))
    (L : ℕ) (hS : ∀ k, (S k).length ≤ L) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ L+stackWeight q := by
  induction q using stmtStRec generalizing v S L with
  | run k o q ih =>
    rw [step_run,stackWeight_run]
    intro j
    exact (ih _ _ (L+1) (updated_length o v S L hS) j).trans_eq (by omega)
  | load f q ih => exact ih (f v) S L hS
  | branch f q r iq ir =>
    cases hh : f v with
    | false =>
      simp only [TM2.stepAux,hh,Bool.cond_false,stackWeight]
      exact fun j => (ir v S L hS j).trans (by omega)
    | true =>
      simp only [TM2.stepAux,hh,Bool.cond_true,stackWeight]
      exact fun j => (iq v S L hS j).trans (by omega)
  | goto => simpa [TM2.stepAux,stackWeight] using hS
  | halt => simpa [TM2.stepAux,stackWeight] using hS

theorem step_time (l : Λ) (v : σ) (S : ∀ k, List (Γ k))
    (a : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (L C : ℕ)
    (ha : TrCfg ⟨some l,v,S⟩ a) (hS : ∀ k, (S k).length ≤ L)
    (hC : stackWeight (M l)+1 ≤ C) :
    ∃ u b, u ≤ C*(2*(L+C)+4) ∧ TrCfg (TM2.stepAux (M l) v S) b ∧
      exec (TM1.step (tr M)) u a = some b := by
  obtain ⟨T,hT⟩ := ha
  obtain ⟨u,b,hu,hb,he⟩ := continuation_time M (M l) v S T L hT hS
  refine ⟨u+1,b,?_,hb,?_⟩
  · have hm : 2*(L+stackWeight (M l))+3 ≤ 2*(L+C)+4 := by omega
    have hm' : stackWeight (M l)*(2*(L+stackWeight (M l))+3) ≤
        stackWeight (M l)*(2*(L+C)+4) := Nat.mul_le_mul_left _ hm
    calc u+1 ≤ (stackWeight (M l)+1)*(2*(L+C)+4) := by nlinarith
         _ ≤ _ := Nat.mul_le_mul_right _ hC
  · simpa only [exec,TM1.step,tr,Option.map_some,Option.bind_some] using he

/-- A bounded TM2 run on stacks of initial length <=L is simulated by Mathlib's
single tape TM1 interpreter in at most C*t*(2*(L+C*t)+4) macro-transitions.
C is a fixed syntactic maximum over the finite program, not input advice. -/
theorem execution_time [Inhabited Λ] (F : Finset Λ) (hF : TM2.Supports M F)
    (C : ℕ) (hC : ∀ l ∈ F, stackWeight (M l)+1 ≤ C)
    (t : ℕ) (a b : TM2.Cfg Γ Λ σ)
    (a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) (L : ℕ)
    (ha : a.l ∈ Finset.insertNone F) (hS : ∀ k, (a.stk k).length ≤ L)
    (htr : TrCfg a a') (hr : exec (TM2.step M) t a = some b) :
    ∃ u b', u ≤ C*t*(2*(L+C*t)+4) ∧ TrCfg b b' ∧
      exec (TM1.step (tr M)) u a' = some b' := by
  induction t generalizing L a a' with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0,a',by omega,htr,rfl⟩
  | succ t ih =>
    obtain ⟨l,v,S⟩ := a
    cases l with
    | none => simp [exec,TM2.step] at hr
    | some l =>
      have hl := Finset.some_mem_insertNone.mp ha
      obtain ⟨u₀,c',hu₀,hc',he₀⟩ := step_time M l v S a' L C htr hS (hC l hl)
      have hnext : (TM2.stepAux (M l) v S).l ∈ Finset.insertNone F :=
        TM2.step_supports M hF (by rfl) ha
      have hlen : ∀ k, ((TM2.stepAux (M l) v S).stk k).length ≤ L+C := by
        intro k
        exact (statement_length (M l) v S L hS k).trans (by have := hC l hl; omega)
      change exec (TM2.step M) t (TM2.stepAux (M l) v S) = some b at hr
      obtain ⟨u,b',hu,hb',he⟩ := ih _ _ (L+C) hnext hlen hc' hr
      refine ⟨u₀+u,b',?_,hb',exec_trans he₀ he⟩
      have hu₀' : u₀ ≤ C*(2*(L+C*(t+1))+4) := by
        apply hu₀.trans
        apply Nat.mul_le_mul_left
        have : C ≤ C*(t+1) := by simpa using Nat.mul_le_mul_left C (show 1 ≤ t+1 by omega)
        omega
      have hu' : u ≤ C*t*(2*(L+C*(t+1))+4) := by
        convert hu using 1 ; ring
      calc u₀+u ≤ C*(2*(L+C*(t+1))+4)+C*t*(2*(L+C*(t+1))+4) := Nat.add_le_add hu₀' hu'
           _ = _ := by ring

theorem halts (a : TM2.Cfg Γ Λ σ) (a' : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (htr : TrCfg a a') (ha : TM2.step M a = none) : TM1.step (tr M) a' = none := by
  obtain ⟨l,v,S⟩ := a
  cases l with
  | none => cases htr; rfl
  | some l => simp [TM2.step] at ha

end RationalHitting.TMTime.StackToOne

namespace RationalHitting.TMTime.FiniteStates
open Turing
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]

/-- Number the supported states, reserving zero for the default state. -/
noncomputable def stateEncode (S : Finset Λ) (q : Λ) : Fin (Fintype.card ↥S+1) :=
  if q=default then 0 else if h : q∈S then (Fintype.equivFin ↥S ⟨q,h⟩).succ else 0

/-- Decode a numbered state, with zero denoting the default state. -/
noncomputable def stateDecode (S : Finset Λ) : Fin (Fintype.card ↥S+1) → Λ :=
  Fin.cases default (fun i => ((Fintype.equivFin ↥S).symm i).val)

@[simp] lemma stateEncode_default (S : Finset Λ) : stateEncode S default=0 := by
  simp [stateEncode]

lemma stateDecode_encode (S : Finset Λ) (q : Λ) (hq : q∈S) :
    stateDecode S (stateEncode S q)=q := by
  by_cases h : q=default
  · simp [stateEncode,stateDecode,h]
  · simp [stateEncode,stateDecode,h,hq]

/-- Restrict a supported machine to an explicitly finite numbered state space. -/
noncomputable def machine (M : TM0.Machine Γ Λ) (S : Finset Λ) :
    TM0.Machine Γ (Fin (Fintype.card ↥S+1)) :=
  fun q a => (M (stateDecode S q) a).map (fun z => (stateEncode S z.1,z.2))

/-- Map a supported configuration to its numbered state representation. -/
noncomputable def cfg (S : Finset Λ) (a : TM0.Cfg Γ Λ) :
    TM0.Cfg Γ (Fin (Fintype.card ↥S+1)) := ⟨stateEncode S a.q,a.Tape⟩

lemma step_cfg (M : TM0.Machine Γ Λ) (S : Finset Λ) (a : TM0.Cfg Γ Λ) (ha : a.q∈S) :
    TM0.step (machine M S) (cfg S a) = (TM0.step M a).map (cfg S) := by
  rcases a with ⟨q,T⟩
  simp only [TM0.step,machine,cfg,stateDecode_encode S q ha,Option.map_map]
  rfl

@[simp] lemma cfg_init (S : Finset Λ) (l : List Γ) :
    cfg S (TM0.init l)=TM0.init l := by
  simp [cfg,TM0.init]

lemma execution (M : TM0.Machine Γ Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
    (t : ℕ) (a b : TM0.Cfg Γ Λ) (ha : a.q∈S)
    (hr : exec (TM0.step M) t a=some b) :
    exec (TM0.step (machine M S)) t (cfg S a)=some (cfg S b) := by
  induction t generalizing a with
  | zero => simpa [exec] using congrArg (Option.map (cfg S)) hr
  | succ t ih =>
    cases he : TM0.step M a with
    | none => simp [exec,he] at hr
    | some c =>
      have hc : c.q∈S := TM0.step_supports M hs he ha
      have hr' : exec (TM0.step M) t c=some b := by simpa [exec,he] using hr
      simp only [exec,step_cfg M S a ha,he,Option.map_some,Option.bind_some]
      exact ih c hc hr'

lemma run_support.{v_1, v_2} {Γ : Type v_1} {Λ : Type v_2}
  [Inhabited Γ] [Inhabited Λ]  (M : Turing.TM0.Machine Γ Λ) (S : Finset Λ)
  (hs : Turing.TM0.Supports M ↑S) (t : ℕ) (a b : Turing.TM0.Cfg Γ Λ) (ha : a.q ∈ S)
  (hr : RationalHitting.TMTime.exec (Turing.TM0.step M) t a = some b) : b.q ∈ S := by
  induction t generalizing a with
  | zero => simp only [exec,Option.some.injEq] at hr; subst b; exact ha
  | succ t ih =>
    cases he : TM0.step M a with
    | none => simp [exec,he] at hr
    | some c => exact ih c (TM0.step_supports M hs he ha) (by simpa [exec,he] using hr)

/-- Finite-support compression has no transition or tape overhead. -/
theorem finite_machine (M : TM0.Machine Γ Λ) (S : Finset Λ)
    (hs : TM0.Supports M (S : Set Λ)) :
    ∃ (m : ℕ) (G : TM0.Machine Γ (Fin (m+1))), ∀ (l : List Γ) (t : ℕ) (a : TM0.Cfg Γ Λ),
      exec (TM0.step M) t (TM0.init l)=some a → TM0.step M a=none →
      ∃ b : TM0.Cfg Γ (Fin (m+1)), exec (TM0.step G) t (TM0.init l)=some b ∧
        TM0.step G b=none ∧ b.Tape=a.Tape := by
  refine ⟨Fintype.card ↥S,machine M S,?_⟩
  intro l t a hr hh
  have hi : (TM0.init l).q∈S := hs.1
  refine ⟨cfg S a,?_,?_,rfl⟩
  · simpa only [cfg_init] using execution M S hs t (TM0.init l) a hi hr
  · rw [step_cfg M S a (run_support M S hs t _ _ hi hr),hh,Option.map_none]

end RationalHitting.TMTime.FiniteStates

/- Quantitative finite-control compilation of stack programs,
with an explicit tape encoding. -/

end Complexity
