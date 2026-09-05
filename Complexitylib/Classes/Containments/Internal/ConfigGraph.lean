/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.ConfigCount
public import Complexitylib.Classes.Containments.Defs
public import Complexitylib.Models.TuringMachine.Branch

/-!
# The configuration graph of a nondeterministic machine

⚠️ Unreviewed by Bolton

Space-bounded computation is graph reachability: a nondeterministic machine accepts exactly when
some accepting configuration is reachable from the initial one along the two-successor relation.
This file sets up that translation, which `NL ⊆ P`, `NL ⊆ coNL` and Savitch's theorem all rest
on — each then differs only in how it searches the graph.

The definitions themselves live in `Complexitylib.Classes.Containments.Defs`.

## Main results

- `NTM.reachesCfg_trace` — every configuration a trace passes through is reachable
- `NTM.exists_trace_of_reachesCfg` — every reachable configuration is the end of some trace
- `NTM.succ_iff` — an edge of the graph is a step of one of the two `NTM.branchTM`s
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {k : ℕ} {tm : NTM k}

/-- **The configuration graph is the union of the two deterministic steps.** Its edges are the
steps of `NTM.branchTM`, so the deterministic machinery for a single step applies to them. -/
theorem succ_iff (tm : NTM k) (c c' : Cfg k tm.Q) :
    tm.Succ c c' ↔ ∃ b, (tm.branchTM b).step c = some c' := by
  constructor
  · rintro ⟨hne, b, rfl⟩
    exact ⟨b, branchTM_step tm b hne⟩
  · rintro ⟨b, hb⟩
    have hne : c.state ≠ tm.qhalt := by
      intro h
      rw [branchTM_step_of_halted tm b h] at hb
      exact absurd hb.symm (Option.some_ne_none c')
    refine ⟨hne, b, ?_⟩
    rw [branchTM_step tm b hne] at hb
    exact (Option.some_injective _ hb).symm

theorem reachesCfg_refl (tm : NTM k) (c : Cfg k tm.Q) : tm.ReachesCfg c c :=
  Relation.ReflTransGen.refl

theorem reachesCfg_head {c c' c'' : Cfg k tm.Q} (h : tm.Succ c c'') (h' : tm.ReachesCfg c'' c') :
    tm.ReachesCfg c c' :=
  Relation.ReflTransGen.head h h'

/-- **A trace stays inside the configuration graph.** -/
theorem reachesCfg_trace (tm : NTM k) :
    ∀ (T : ℕ) (choices : Fin T → Bool) (c : Cfg k tm.Q),
      tm.ReachesCfg c (tm.trace T choices c)
  | 0, _, c => reachesCfg_refl tm c
  | T + 1, choices, c => by
      rw [NTM.trace]
      by_cases h : c.state = tm.qhalt
      · simp only [h, ite_eq_left]
        exact reachesCfg_refl tm c
      · simp only [h, ite_eq_right, not_false_iff]
        refine reachesCfg_head ⟨h, choices ⟨0, Nat.zero_lt_succ T⟩, rfl⟩ ?_
        exact reachesCfg_trace tm T _ _

/-- **Every reachable configuration ends some trace.** -/
theorem exists_trace_of_reachesCfg {c c' : Cfg k tm.Q} (h : tm.ReachesCfg c c') :
    ∃ (t : ℕ) (choices : Fin t → Bool), tm.trace t choices c = c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun i => i.elim0, rfl⟩
  | head hstep _ ih =>
      obtain ⟨hne, b, rfl⟩ := hstep
      obtain ⟨t, choices, hchoices⟩ := ih
      refine ⟨t + 1, Fin.cons b choices, ?_⟩
      have hcons : (fun i : Fin t => Fin.cons (α := fun _ => Bool) b choices
          ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = choices := by
        funext i
        exact Fin.cons_succ (α := fun _ => Bool) b choices i
      rw [NTM.trace, ite_eq_right hne, hcons]
      exact hchoices

end NTM

variable {k : ℕ} {tm : NTM k}

/-! ## The window invariant along the graph -/

/-- A nondeterministic step of a machine whose heads stay inside the window preserves the
window invariant. -/
theorem Windowed.stepCfg {x : List Bool} {S : ℕ} {c : Cfg k tm.Q} (b : Bool)
    (hw : Windowed x S c) (hspace : c.WithinDecisionSpace x.length S) :
    Windowed x S (tm.stepCfg b c) := by
  refine ⟨?_, ?_, ?_⟩
  · show (c.input.move _).cells = _
    cases (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1 <;>
      exact hw.input
  · intro i p hp
    have hhead : (c.work i).head ≤ S := hspace.1.1 i
    show ((c.work i).writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.work i p hp
  · intro p hp
    have hhead : c.output.head ≤ S + 1 := hspace.2
    show (c.output.writeAndMove _ _).cells p = Γ.blank
    rw [cells_writeAndMove_of_ne _ _ _ (by omega)]
    exact hw.output p hp

/-- Along the configuration graph, the window invariant is inherited as long as every
configuration met respects the space bound. -/
theorem windowed_of_reachesCfg {x : List Bool} {S : ℕ} {c₀ c : Cfg k tm.Q}
    (hspace : ∀ c', tm.ReachesCfg c₀ c' → c'.WithinDecisionSpace x.length S)
    (hw : Windowed x S c₀) (h : tm.ReachesCfg c₀ c) : Windowed x S c := by
  induction h with
  | refl => exact hw
  | tail hreach hstep ih =>
      obtain ⟨_, b, rfl⟩ := hstep
      exact ih.stepCfg b (hspace _ hreach)

/-! ## Acceptance is reachability -/

/-- **A space-bounded machine accepts exactly when an accepting configuration is reachable.**
This is the bridge every log-space graph argument starts from: membership in the language is a
property of the configuration graph alone, with no reference to time or choice sequences. -/
theorem mem_iff_exists_accepting_reachable {k : ℕ} {tm : NTM k} {L : Language} {f : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L f) (x : List Bool) :
    x ∈ L ↔ ∃ c, tm.ReachesCfg (tm.initCfg x) c ∧ tm.halted c ∧ c.output.cells 1 = Γ.one := by
  obtain ⟨T, hdt, _⟩ := hdec
  constructor
  · intro hx
    obtain ⟨choices, hhalt, hout⟩ := (hdt.2 x).mp hx
    exact ⟨_, NTM.reachesCfg_trace tm _ choices _, hhalt, hout⟩
  · rintro ⟨c, hreach, hhalt, hout⟩
    obtain ⟨t, choices, rfl⟩ := NTM.exists_trace_of_reachesCfg hreach
    refine (hdt.2 x).mpr ?_
    rcases Nat.lt_or_ge (T x.length) t with hlt | hge
    · -- the run already halted by `T`, so the longer trace adds nothing
      refine ⟨fun j => choices ⟨j.val, by omega⟩, ?_⟩
      have hfrozen :=
        tm.trace_mono (T := T x.length) (T' := t) hlt.le
          (choices := fun j => choices ⟨j.val, by omega⟩) (choices' := choices)
          (fun i => rfl) (hdt.1 x _)
      rw [hfrozen] at hhalt hout
      exact ⟨hhalt, hout⟩
    · -- pad the choice sequence out to `T`
      refine ⟨fun j => if h : j.val < t then choices ⟨j.val, h⟩ else false, ?_⟩
      have hfrozen :=
        tm.trace_mono (T := t) (T' := T x.length) hge
          (choices := choices)
          (choices' := fun j => if h : j.val < t then choices ⟨j.val, h⟩ else false)
          (fun i => by simp [i.isLt]) hhalt
      rw [hfrozen]
      exact ⟨hhalt, hout⟩

end Complexity
