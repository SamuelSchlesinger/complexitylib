/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.RationalHitting.Internal.Executable

/-!
# Rational hitting lists: stack language

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/StackLanguage.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical arguments are retained.
-/

@[expose] public section

namespace Complexity

namespace RationalHitting.TMTime
open Turing

/-- Execute a partial transition function for exactly the specified number of steps. -/
def exec {α : Type*} (step : α → Option α) : ℕ → α → Option α
  | 0,a => some a
  | t+1,a => (step a).bind (exec step t)

@[simp] lemma exec_zero {α : Type*} (step : α → Option α) (a : α) : exec step 0 a = some a := rfl

lemma exec_add {α : Type*} (step : α → Option α) (s t : ℕ) (a : α) :
    exec step (s+t) a = (exec step s a).bind (exec step t) := by
  induction s generalizing a with
  | zero => simp [exec]
  | succ s ih =>
    simp only [Nat.succ_add,exec,ih,Option.bind_assoc]

lemma exec_trans {α : Type*} {step : α → Option α} {s t : ℕ} {a b c : α}
    (h : exec step s a = some b) (h' : exec step t b = some c) :
    exec step (s+t) a = some c := by rw [exec_add,h,Option.bind_some,h']

lemma exec_positive_congr {α : Type*} {step : α → Option α} {t : ℕ} (ht : 0<t)
    {a b : α} (h : step a = step b) : exec step t a = exec step t b := by
  cases t with
  | zero => omega
  | succ t => simp only [exec,h]

namespace OneToZero
variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- Syntactic statement bound, fixed once the finite machine is fixed. -/
def weight : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q | .write _ q | .load _ q => weight q+1
  | .branch _ q r => max (weight q) (weight r)+1
  | .goto _ | .halt => 1

lemma weight_pos.{v_1, v_2, v_3} {Γ : Type v_1} {Λ : Type v_2}
  {σ : Type v_3}    (q : Turing.TM1.Stmt Γ Λ σ) :
  0 < RationalHitting.TMTime.OneToZero.weight q := by cases q <;> simp [weight]

/-- Each TM1 macro-step takes at most its statement size in real TM0 steps.
Load and branch are absorbed into the next primitive step by Mathlib's compiler. -/
theorem statement_time (M : Λ → TM1.Stmt Γ Λ σ) (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    ∃ t, 0<t ∧ t ≤ weight q ∧
      exec (TM0.step (TM1to0.tr M)) t ⟨(some q,v),T⟩ =
        some (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.move d)
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | write f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih v (T.write (f T.head v))
    refine ⟨t+1,by omega,by simpa [weight] using Nat.add_le_add_right hb 1,?_⟩
    simpa only [exec,TM0.step,TM1to0.tr,TM1to0.trAux,
      Option.map_some,Option.bind_some,TM1.stepAux] using he
  | load f q ih =>
    obtain ⟨t,ht,hb,he⟩ := ih (f T.head v) T
    refine ⟨t,ht,by simp only [weight]; omega,?_⟩
    rw [exec_positive_congr ht (by rfl : TM0.step (TM1to0.tr M)
      ⟨(some (.load f q),v),T⟩ = TM0.step (TM1to0.tr M) ⟨(some q,f T.head v),T⟩)]
    exact he
  | branch f q r ihq ihr =>
    cases hh : f T.head v with
    | false =>
      obtain ⟨t,ht,hb,he⟩ := ihr v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,
        Bool.cond_false] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some r,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
    | true =>
      obtain ⟨t,ht,hb,he⟩ := ihq v T
      refine ⟨t,ht,by simp only [weight]; omega,?_⟩
      rw [exec_positive_congr ht (by simp only [TM0.step,TM1to0.tr,TM1to0.trAux,hh,Bool.cond_true] :
        TM0.step (TM1to0.tr M) ⟨(some (.branch f q r),v),T⟩ =
        TM0.step (TM1to0.tr M) ⟨(some q,v),T⟩)]
      simpa [TM1.stepAux,hh] using he
  | goto f =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]
  | halt =>
    refine ⟨1,by omega,by simp [weight],?_⟩
    simp [exec,TM0.step,TM1to0.tr,TM1to0.trAux,TM1.stepAux,TM1to0.trCfg,Tape.write_self]

/-- Linear transition overhead for a finitely supported TM1 program. -/
theorem execution_time (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hs : TM1.Supports M S) (C : ℕ) (hC : ∀ l ∈ S, weight (M l) ≤ C)
    (t : ℕ) (a b : TM1.Cfg Γ Λ σ) (ha : a.l ∈ Finset.insertNone S)
    (hr : exec (TM1.step M) t a = some b) :
    ∃ u ≤ C*t, exec (TM0.step (TM1to0.tr M)) u (TM1to0.trCfg M a) =
      some (TM1to0.trCfg M b) := by
  induction t generalizing a with
  | zero =>
    simp only [exec,Option.some.injEq] at hr
    subst b
    exact ⟨0, by omega, rfl⟩
  | succ t ih =>
    obtain ⟨l,v,T⟩ := a
    cases l with
    | none => simp [exec,TM1.step] at hr
    | some l =>
      have hl : l ∈ S := Finset.some_mem_insertNone.mp ha
      have hnext : (TM1.stepAux (M l) v T).l ∈ Finset.insertNone S :=
        TM1.step_supports M hs (by rfl) ha
      change exec (TM1.step M) t (TM1.stepAux (M l) v T) = some b at hr
      obtain ⟨u,hu,he⟩ := ih _ hnext hr
      obtain ⟨v',_,hv',hv⟩ := statement_time M (M l) v T
      refine ⟨v'+u,?_,exec_trans hv he⟩
      have := hC l hl
      nlinarith

@[simp] theorem halts (M : Λ → TM1.Stmt Γ Λ σ) (a : TM1.Cfg Γ Λ σ)
    (h : TM1.step M a = none) : TM0.step (TM1to0.tr M) (TM1to0.trCfg M a) = none := by
  rcases a with ⟨l,v,T⟩
  cases l <;> simp_all [TM1.step,TM1to0.trCfg,TM0.step,TM1to0.tr]

end OneToZero
end RationalHitting.TMTime

/- A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/
namespace RationalHitting.StackLanguage
open Turing
open RationalHitting.TMTime
variable {K : Type} [DecidableEq K]

/-- Finite Boolean-stack programs with branching, composition, and while loops. -/
inductive Program (K : Type) where
  /-- Leave all registers unchanged. -/
  | skip : Program K
  /-- Push one Boolean symbol onto a register. -/
  | push : K → Bool → Program K
  /-- Discard the head of a register, if present. -/
  | drop : K → Program K
  /-- Move one head symbol between registers. -/
  | transfer : K → K → Program K
  /-- Execute two programs in sequence. -/
  | seq : Program K → Program K → Program K
  /-- Choose a program for an empty, false-headed, or true-headed register. -/
  | branch : K → Program K → Program K → Program K → Program K
  /-- Repeat a program while the specified register is nonempty. -/
  | loop : K → Program K → Program K
  deriving DecidableEq

/-- The Boolean word stored in each register. -/
abbrev Store (K : Type) := K → List Bool
/-- The initial label or a list of remaining program commands. -/
abbrev Labels (K : Type) := Option (List (Program K))

/-- Move one head symbol if present, popping the first register before
updating the second, including when both registers coincide. -/
def transfer (a b : K) (s : Store K) : Store K :=
  match (s a).head? with
  | none => s
  | some x => Function.update (Function.update s a (s a).tail) b
      (x :: (Function.update s a (s a).tail) b)

/-- Big-step execution with an exact count of stack-program transitions. -/
inductive Eval : Program K → Store K → Store K → ℕ → Prop where
  /-- Skipping costs one transition. -/
  | skip (s : Store K) : Eval .skip s s 1
  /-- Pushing a symbol costs one transition. -/
  | push (k : K) (b : Bool) (s : Store K) :
    Eval (.push k b) s (Function.update s k (b::s k)) 1
  /-- Dropping a symbol costs one transition. -/
  | drop (k : K) (s : Store K) : Eval (.drop k) s (Function.update s k (s k).tail) 1
  /-- A symbol transfer costs one transition. -/
  | transfer (a b : K) (s : Store K) : Eval (.transfer a b) s (transfer a b s) 1
  /-- Sequential composition adds both execution times and one control transition. -/
  | seq {p q : Program K} {s u v : Store K} {t w : ℕ} :
    Eval p s u t → Eval q u v w → Eval (.seq p q) s v (1+t+w)
  /-- Take the empty-register branch after one control transition. -/
  | branchNone {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} :
    s k = [] → Eval p s v t → Eval (.branch k p q r) s v (1+t)
  /-- Take the false-symbol branch after one control transition. -/
  | branchFalse {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} {ls : List Bool} :
    s k = false::ls → Eval q s v t → Eval (.branch k p q r) s v (1+t)
  /-- Take the true-symbol branch after one control transition. -/
  | branchTrue {k : K} {p q r : Program K} {s v : Store K} {t : ℕ} {ls : List Bool} :
    s k = true::ls → Eval r s v t → Eval (.branch k p q r) s v (1+t)
  /-- An empty loop register terminates the loop in one transition. -/
  | whileNil {k : K} {p : Program K} {s : Store K} :
    s k = [] → Eval (.loop k p) s s 1
  /-- A nonempty loop register executes the body and repeats. -/
  | whileCons {k : K} {p : Program K} {s u v : Store K} {t w : ℕ} :
    s k ≠ [] → Eval p s u t → Eval (.loop k p) u v w → Eval (.loop k p) s v (1+t+w)

variable (K) in
/-- Mathlib stack-machine statements used to compile the finite program. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Bool) (Labels K) (Option Bool)

/-- Reset the temporary symbol and continue with the remaining commands. -/
def jump (ps : List (Program K)) : Stmt K :=
  .load (fun _ => none) (.goto (fun _ => some ps))

/-- Compile the next program command into stack-machine instructions. -/
def instruction : List (Program K) → Stmt K
  | [] => .halt
  | .skip :: ps => jump ps
  | .push k b :: ps => .push k (fun _ => b) (jump ps)
  | .drop k :: ps => .pop k (fun _ _ => none) (jump ps)
  | .transfer a b :: ps => .peek a (fun _ x => x)
      (.branch (fun x => x.isSome)
        (.pop a (fun v _ => v) (.push b (fun v => v.getD false) (jump ps))) (jump ps))
  | .seq p q :: ps => jump (p::q::ps)
  | .branch k p q r :: ps => .peek k (fun _ x => x)
      (.branch (fun x => x.isNone) (jump (p::ps))
        (.branch (fun x => x.getD false) (jump (r::ps)) (jump (q::ps))))
  | .loop k p :: ps => .peek k (fun _ x => x)
      (.branch (fun x => x.isNone) (jump ps) (jump (p::.loop k p::ps)))

/-- The stack-machine transition map for a finite program. -/
def machine (p : Program K) : Labels K → Stmt K
  | none => jump [p]
  | some ps => instruction ps

/-- The stack-machine configuration for a continuation and register store. -/
def cfg (ps : List (Program K)) (s : Store K) : TM2.Cfg (fun _ : K => Bool) (Labels K) (Option
    Bool) :=
  ⟨some (some ps),none,s⟩

@[simp] theorem jump_eval (ps : List (Program K)) (v : Option Bool) (s : Store K) :
    TM2.stepAux (jump ps) v s = cfg ps s := rfl

/-- Exact big-step correctness in real TM2 steps, with no unbounded internal
state or alphabet. -/
theorem eval_compiles {p : Program K} {s v : Store K} {t : ℕ}
    (h : Eval p s v t) (main : Program K) (ps : List (Program K)) :
    exec (TM2.step (machine main)) t (cfg (p::ps) s) = some (cfg ps v) := by
  induction h generalizing ps with
  | skip s => rfl
  | push k b s => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump]
  | drop k s => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump]
  | transfer a b s =>
    cases hh : s a with
    | nil => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,transfer,hh]
    | cons x xs => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,transfer,hh]
  | @seq p q s u v t w hp hq ihp ihq =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.seq p q::ps) s) =
        some (cfg (p::q::ps) s) := by rfl
    simpa only [Nat.add_assoc] using exec_trans h₁ (exec_trans (ihp (q::ps)) (ihq ps))
  | @branchNone k p q r s v t hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (p::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @branchFalse k p q r s v t ls hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (q::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @branchTrue k p q r s v t ls hh h ih =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.branch k p q r::ps) s) =
        some (cfg (r::ps) s) := by simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
    exact exec_trans h₁ (ih ps)
  | @whileNil k p s hh =>
    simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hh]
  | @whileCons k p s u v t w hh hp hw ihp ihw =>
    have h₁ : exec (TM2.step (machine main)) 1 (cfg (.loop k p::ps) s) =
        some (cfg (p::.loop k p::ps) s) := by
      cases hv : s k with
      | nil => exact (hh hv).elim
      | cons x xs => simp [exec,cfg,machine,instruction,TM2.step,TM2.stepAux,jump,hv]
    simpa only [Nat.add_assoc] using exec_trans h₁ (exec_trans (ihp (.loop k p::ps)) (ihw ps))

/-- Possible jump targets; inspecting a head has only three finite cases. -/
def successors : List (Program K) → Finset (List (Program K))
  | [] => ∅
  | .skip :: ps => {ps}
  | .push _ _ :: ps | .drop _ :: ps | .transfer _ _ :: ps => {ps}
  | .seq p q :: ps => {p::q::ps}
  | .branch _ p q r :: ps => {p::ps,q::ps,r::ps}
  | .loop k p :: ps => {ps,p::.loop k p::ps}

/-- Finite control locations, computed structurally, despite unbounded loop
iteration counts. -/
def locations : Program K → List (Program K) → Finset (List (Program K))
  | p@(.skip),ps | p@(.push ..),ps | p@(.drop ..),ps | p@(.transfer ..),ps => {p::ps,ps}
  | p@(.seq a b),ps => insert (p::ps) (locations a (b::ps) ∪ locations b ps)
  | p@(.branch _ a b c),ps => insert (p::ps) (locations a ps ∪ locations b ps ∪ locations c ps)
  | p@(.loop _ a),ps => insert (p::ps) (insert ps (locations a (p::ps)))

@[simp] theorem entry_mem (p : Program K) (ps : List (Program K)) : p::ps ∈ locations p ps := by
  cases p <;> simp [locations]

@[simp] theorem exit_mem (p : Program K) (ps : List (Program K)) : ps ∈ locations p ps := by
  induction p generalizing ps <;> simp_all [locations]

lemma root_closed (p : Program K) (ps : List (Program K)) (S : Finset (List (Program K)))
    (hs : locations p ps ⊆ S) : successors (p::ps) ⊆ S := by
  cases p with
  | skip | push k b | drop k | transfer a b => simpa [successors] using hs (exit_mem _ _)
  | seq a b => simpa [successors] using hs (by simp [locations])
  | branch k a b c =>
    simp only [successors,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hs (by simp [locations]),hs (by simp [locations]),hs (by simp [locations])⟩
  | loop k a =>
    simp only [successors,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hs (by simp [locations]),hs (by simp [locations])⟩

lemma locations_closed (p : Program K) (ps : List (Program K)) (S : Finset (List (Program K)))
    (hs : locations p ps ⊆ S) (hk : successors ps ⊆ S) :
    ∀ l ∈ locations p ps, successors l ⊆ S := by
  induction p generalizing ps S with
  | skip | push k b | drop k | transfer a b =>
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl|rfl
    · exact root_closed _ _ _ hs
    · exact hk
  | seq a b iha ihb =>
    have hb : locations b ps ⊆ S := fun l hl => hs (by simp [locations,hl])
    have ha : locations a (b::ps) ⊆ S := fun l hl => hs (by simp [locations,hl])
    have hb' := ihb ps S hb hk
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_union] at hl
    rcases hl with rfl|hl|hl
    · exact root_closed _ _ _ hs
    · exact iha (b::ps) S ha (hb' _ (entry_mem b ps)) l hl
    · exact hb' l hl
  | branch k a b c iha ihb ihc =>
    intro l hl
    simp only [locations,Finset.mem_insert,Finset.mem_union] at hl
    rcases hl with rfl|(hl|hl)|hl
    · exact root_closed _ _ _ hs
    · exact iha ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
    · exact ihb ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
    · exact ihc ps S (fun x hx => hs (by simp [locations,hx])) hk l hl
  | loop k a ih =>
    intro l hl
    simp only [locations,Finset.mem_insert] at hl
    rcases hl with rfl|rfl|hl
    · exact root_closed _ _ _ hs
    · exact hk
    · exact ih _ S (fun x hx => hs (by simp [locations,hx])) (root_closed _ _ _ hs) l hl


/-- The finite set of control labels used by the compiled program. -/
def support (p : Program K) : Finset (Labels K) := insert none ((locations p []).image some)

lemma instruction_supported (S : Finset (Labels K)) (ps : List (Program K))
    (h : ∀ q ∈ successors ps, some q ∈ S) : TM2.SupportsStmt S (instruction ps) := by
  cases ps with
  | nil => trivial
  | cons p ps =>
    cases p <;> simp only [instruction,TM2.SupportsStmt,jump,successors,
      Finset.mem_insert,Finset.mem_singleton] at * <;> aesop

theorem machine_supported (p : Program K) : TM2.Supports (machine p) (support p) := by
  constructor
  · exact Finset.mem_insert_self _ _
  · intro q hq
    simp only [support,Finset.mem_insert,Finset.mem_image] at hq
    rcases hq with rfl|⟨ps,hps,rfl⟩
    · simp only [machine,jump,TM2.SupportsStmt]
      intro v
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨[p],entry_mem p [],rfl⟩)
    · apply instruction_supported
      intro qs hqs
      have hh := locations_closed p [] (locations p []) (fun _ h => h)
        (by simp [successors]) ps hps hqs
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨qs,hh,rfl⟩)

/-- Entry and halting are one actual macrostep apiece. -/
theorem complete_run {p : Program K} {s v : Store K} {t : ℕ} (h : Eval p s v t) :
    exec (TM2.step (machine p)) (t+2) ⟨some none,none,s⟩ = some ⟨none,none,v⟩ := by
  have he : exec (TM2.step (machine p)) 1 ⟨some none,none,s⟩ = some (cfg [p] s) := rfl
  have hf : exec (TM2.step (machine p)) 1 (cfg [] v) = some ⟨none,none,v⟩ := rfl
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    exec_trans he (exec_trans (eval_compiles h p []) hf)

end RationalHitting.StackLanguage

end Complexity
