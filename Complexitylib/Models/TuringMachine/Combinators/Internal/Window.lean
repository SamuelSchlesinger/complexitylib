/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.IdleHeads
public import Complexitylib.Models.TuringMachine.Combinators.Internal.SentinelStep
public import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Machines that respect a space window

A `TM.HoareSpace` contract bounds every configuration reachable from a *start* state, which makes
it awkward to compose: the body of a loop is entered again and again, never from its own start.
The step-local strengthening below composes freely. A machine *respects a window* when one step
from any configuration inside the window lands inside the window again — regardless of where in
its own execution it happens to be.

Respecting a window immediately gives a space contract, and the property is inherited by the loop
combinator from its body and test, because every phase `loopTM` interposes between them idles the
input and work tapes (`TM.loop_head_bound`). This is what lets a loop run for as long as it likes
without its space bound growing.

`TM.RespectsWindow` is the step-local form, convenient when it applies. It is too strong for a
machine that simulates another one, whose own space bound holds only along its own run, so the
weaker `TM.KeepsWindow` — *started anywhere inside the window, everything reached stays inside* —
is the notion the composition rules are stated for. Every entry into a loop body is at its start
state, so this is exactly as much as a loop needs.

A subroutine that simulates another machine is not robust even in that sense: run from a start
whose scratch tapes hold garbage, the simulated machine is not on any run its own space bound
covers. `TM.KeepsWindowOn` therefore carries a precondition on the starting tapes, which a
composition rule must re-establish at each entry from the previous stage's postcondition —
and `TM.halted_unique` is what makes such a postcondition usable, since it says the halted
configuration a stage reaches is the only one.

The two forms meet at `TM.seqTM_keepsWindow_of_post`: a stage that needs blank scratch, prefixed
by a stage that clears it, is robust again. So a loop body assembled that way satisfies the plain
`TM.KeepsWindow` hypothesis of `TM.loopTM_keepsWindow`, and no precondition-carrying loop rule is
needed.

## Main definitions

- `TM.RespectsWindow` — one step from inside the window stays inside it
- `TM.KeepsWindow` — from any windowed start, every reachable configuration is windowed
- `TM.KeepsWindowOn` — the same, restricted to starts satisfying a precondition

## Main results

- `TM.hoareSpace_of_respectsWindow` — respecting a window is a space contract
- `TM.decidesInSpace_of_respectsWindow`, `TM.decidesInSpace_of_keepsWindow` — a window turns a
  decider into a space-bounded decider
- `TM.halted_unique` — a deterministic run reaches at most one halted configuration
- `TM.keepsWindowOn_of_haltsIn`, `TM.keepsWindowOn_of_hoareTime`,
  `TM.keepsWindowOn_of_hoareTime_pinned` — **any time-bounded subroutine, and any `TM.HoareTime`
  contract, acquires a window contract**
- `TM.KeepsWindowOn.hoareSpace`, `TM.KeepsWindow.hoareSpace` — a window contract is a
  `TM.HoareSpace` contract, so the two styles interoperate
- `TM.seqTM_respectsWindow`, `TM.loopTM_respectsWindow` — the step-local form composes
- `TM.seqTM_keepsWindow`, `TM.ifTM_keepsWindow`, `TM.loopTM_keepsWindow` — **and so does the
  usable form**, for all three control-flow combinators
- `TM.seqTM_keepsWindowOn` — and the precondition-carrying form, for sequential composition
- `TM.seqTM_keepsWindow_of_post` — **the bridge**: prefixing a precondition-needing stage with a
  robust one yields a robust composite, which the unconditional loop rule accepts
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- The tapes of a configuration all carry their left-end markers. -/
def CfgStartInvariant {Q : Type} (c : Cfg n Q) : Prop :=
  c.input.StartInvariant ∧ (∀ i, (c.work i).StartInvariant) ∧ c.output.StartInvariant

/-- **The machine respects a space window**: one step from any configuration inside the window
lands inside the window again — including the output head, so the discipline is the one
`TM.DecidesInSpace` asks for. Unlike `TM.HoareSpace` this says nothing about where the machine
started, so it survives being re-entered, which is what a loop body needs. -/
def RespectsWindow (tm : TM n) (inputLength space : ℕ) : Prop :=
  ∀ c c' : Cfg n tm.Q, c.WithinDecisionSpace inputLength space → CfgStartInvariant c →
    tm.step c = some c' → c'.WithinDecisionSpace inputLength space

/-- The start-marker invariant is preserved by a step. -/
theorem CfgStartInvariant.step {tm : TM n} {c c' : Cfg n tm.Q}
    (h : CfgStartInvariant c) (hstep : tm.step c = some c') : CfgStartInvariant c' :=
  Tape.StartInvariant.step tm hstep h.1 h.2.1 h.2.2

/-- **Respecting a window is a space contract.** -/
theorem hoareSpace_of_respectsWindow (tm : TM n) {inputLength space : ℕ}
    (h : tm.RespectsWindow inputLength space) :
    tm.HoareSpace
      (fun inp work out =>
        ({ state := tm.qstart, input := inp, work := work, output := out } :
          Cfg n tm.Q).WithinDecisionSpace inputLength space ∧
        CfgStartInvariant { state := tm.qstart, input := inp, work := work, output := out })
      inputLength space :=
  hoareSpace_of_invariant
    (fun c => c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c)
    (fun _ _ _ hpre => hpre)
    (fun _ _ hP hstep => ⟨h _ _ hP.1 hP.2 hstep, hP.2.step hstep⟩)
    (fun _ hP => hP.1.1)

/-- **Sequential composition inherits the window.** The one step interposed between the two
machines idles every tape, so it cannot push a head outward. -/
theorem seqTM_respectsWindow (tm₁ tm₂ : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    (h₁ : tm₁.RespectsWindow inputLength space)
    (h₂ : tm₂.RespectsWindow inputLength space) :
    (seqTM tm₁ tm₂).RespectsWindow inputLength space := by
  intro c c' hwin hsi hstep
  have hne := state_ne_qhalt_of_step hstep
  rcases hstate : c.state with q | q
  · by_cases hq : q = tm₁.qhalt
    · subst hq
      obtain ⟨hi, hw, ho⟩ := seq_head_bound tm₁ tm₂ hstate hstep hsi.1 hsi.2.1 hsi.2.2
      refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
      · have h₃ := hw i
        have h₄ := hwin.1.1 i
        omega
      · have h₄ := hwin.1.2
        omega
      · have h₄ := hwin.2
        omega
    · have hc : c = phase1Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨c₀', hstep0⟩ :
          ∃ c₀', tm₁.step ⟨q, c.input, c.work, c.output⟩ = some c₀' := by
        rw [TM.step, ite_eq_right hq]
        exact ⟨_, rfl⟩
      have hsimstep := seqTM_phase1_step tm₁ tm₂ hstep0
      rw [hc] at hstep
      have hc'eq : c' = phase1Wrap tm₁ tm₂ c₀' :=
        Option.some_inj.mp (hstep.symm.trans hsimstep)
      subst hc'eq
      exact h₁ _ _ hwin hsi hstep0
  · have hq : q ≠ tm₂.qhalt := by
      intro h
      exact hne (by rw [hstate, h]; rfl)
    have hc : c = phase2Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
      Cfg.ext hstate rfl rfl rfl
    obtain ⟨c₀', hstep0⟩ :
        ∃ c₀', tm₂.step ⟨q, c.input, c.work, c.output⟩ = some c₀' := by
      rw [TM.step, ite_eq_right hq]
      exact ⟨_, rfl⟩
    have hsimstep := seqTM_phase2_step tm₁ tm₂ hstep0
    rw [hc] at hstep
    have hc'eq : c' = phase2Wrap tm₁ tm₂ c₀' :=
      Option.some_inj.mp (hstep.symm.trans hsimstep)
    subst hc'eq
    exact h₂ _ _ hwin hsi hstep0

/-- **The loop inherits its window from its body and test.** Every phase `loopTM` interposes
between the two idles the input and work tapes, so the interposed steps cannot push a head
outward; the simulated steps are covered by the parts' own contracts. The bound is therefore
independent of how many iterations run. -/
theorem loopTM_respectsWindow (tmBody tmTest : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    (hbody : tmBody.RespectsWindow inputLength space)
    (htest : tmTest.RespectsWindow inputLength space) :
    (loopTM tmBody tmTest).RespectsWindow inputLength space := by
  intro c c' hwin hsi hstep
  by_cases hb : ∀ q, c.state = Sum.inl q → q = tmBody.qhalt
  · by_cases ht : ∀ q, c.state = Sum.inr (Sum.inr q) → q = tmTest.qhalt
    · obtain ⟨hi, hw, ho⟩ := loop_head_bound tmBody tmTest hb ht hstep hsi.1 hsi.2.1 hsi.2.2
      refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
      · have h₁ := hw i
        have h₂ := hwin.1.1 i
        omega
      · have h₂ := hwin.1.2
        omega
      · have h₂ := hwin.2
        omega
    · push Not at ht
      obtain ⟨q, hstate, hq⟩ := ht
      have hc : c = loopTestWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨c₀', hstep0⟩ :
          ∃ c₀', tmTest.step ⟨q, c.input, c.work, c.output⟩ = some c₀' := by
        rw [TM.step, ite_eq_right hq]
        exact ⟨_, rfl⟩
      have hsimstep := loopTM_test_step tmBody tmTest hstep0
      rw [hc] at hstep
      have hc'eq : c' = loopTestWrap tmBody tmTest c₀' :=
        Option.some_inj.mp (hstep.symm.trans hsimstep)
      subst hc'eq
      exact htest _ _ hwin hsi hstep0
  · push Not at hb
    obtain ⟨q, hstate, hq⟩ := hb
    have hc : c = loopBodyWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
      Cfg.ext hstate rfl rfl rfl
    obtain ⟨c₀', hstep0⟩ :
        ∃ c₀', tmBody.step ⟨q, c.input, c.work, c.output⟩ = some c₀' := by
      rw [TM.step, ite_eq_right hq]
      exact ⟨_, rfl⟩
    have hsimstep := loopTM_body_step tmBody tmTest hstep0
    rw [hc] at hstep
    have hc'eq : c' = loopBodyWrap tmBody tmTest c₀' :=
      Option.some_inj.mp (hstep.symm.trans hsimstep)
    subst hc'eq
    exact hbody _ _ hwin hsi hstep0

/-! ## Determinism at the halt -/

/-- A deterministic run reaches at most one halted configuration: the halt is the run's endpoint,
whichever way it is reached. This is what lets a stage's postcondition be *used* — the
configuration a composition rule meets at the phase boundary is the one the stage's Hoare triple
describes. -/
theorem reachesIn_halted_unique {tm : TM n} :
    ∀ {s t : ℕ} {c a b : Cfg n tm.Q}, tm.reachesIn s c a → tm.reachesIn t c b →
      tm.halted a → tm.halted b → a = b := by
  intro s
  induction s with
  | zero =>
      intro t c a b ha hb hha hhb
      cases ha
      cases hb with
      | zero => rfl
      | step hstep _ =>
          rw [TM.step, ite_eq_left hha] at hstep
          exact absurd hstep (by nofun)
  | succ s ih =>
      intro t c a b ha hb hha hhb
      cases ha with
      | step hstepa hresta =>
          cases hb with
          | zero =>
              rw [TM.step, ite_eq_left hhb] at hstepa
              exact absurd hstepa (by nofun)
          | step hstepb hrestb =>
              rw [Option.some_inj.mp (hstepa.symm.trans hstepb)] at hresta
              exact ih hresta hrestb hha hhb

/-- The unbounded form of `TM.reachesIn_halted_unique`. -/
theorem halted_unique {tm : TM n} {c a b : Cfg n tm.Q}
    (ha : tm.reaches c a) (hb : tm.reaches c b)
    (hha : tm.halted a) (hhb : tm.halted b) : a = b := by
  obtain ⟨s, hs⟩ := TM.reaches_to_reachesIn tm ha
  obtain ⟨t, ht⟩ := TM.reaches_to_reachesIn tm hb
  exact reachesIn_halted_unique hs ht hha hhb

/-! ## Keeping a window along a run -/

/-- **The machine keeps its window**: started anywhere inside the window with its left markers
intact, every configuration it reaches is still inside the window. This is weaker than
`TM.RespectsWindow` — it says nothing about configurations the machine cannot reach from a
windowed start — and it is what a subroutine that simulates another machine can actually
satisfy. -/
def KeepsWindow (tm : TM n) (inputLength space : ℕ) : Prop :=
  ∀ c : Cfg n tm.Q, c.state = tm.qstart → c.WithinDecisionSpace inputLength space →
    CfgStartInvariant c → ∀ c', tm.reaches c c' → c'.WithinDecisionSpace inputLength space

/-- A machine that never steps out of the window certainly keeps it. -/
theorem RespectsWindow.keepsWindow {tm : TM n} {inputLength space : ℕ}
    (h : tm.RespectsWindow inputLength space) : tm.KeepsWindow inputLength space := by
  intro c _ hwin hsi c' hreach
  have key : ∀ d, tm.reaches c d →
      d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d := by
    intro d hd
    induction hd with
    | refl => exact ⟨hwin, hsi⟩
    | tail _ hs ih => exact ⟨h _ _ ih.1 ih.2 hs, ih.2.step hs⟩
  exact (key c' hreach).1

/-- **Sequential composition keeps the window.** Each phase is entered at its machine's start
state with windowed tapes, and the single interposed step idles every tape. -/
theorem seqTM_keepsWindow (tm₁ tm₂ : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    (h₁ : tm₁.KeepsWindow inputLength space)
    (h₂ : tm₂.KeepsWindow inputLength space) :
    (seqTM tm₁ tm₂).KeepsWindow inputLength space := by
  intro c₀ hstart hwin₀ hsi₀ cfin hreach
  set P : Cfg n (seqTM tm₁ tm₂).Q → Prop := fun c =>
    c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c ∧
    (∀ q, c.state = Sum.inl q → ∃ d : Cfg n tm₁.Q, d.state = tm₁.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tm₁.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr q → ∃ d : Cfg n tm₂.Q, d.state = tm₂.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tm₂.reaches d ⟨q, c.input, c.work, c.output⟩) with hPdef
  have hstep : ∀ c c', P c → (seqTM tm₁ tm₂).step c = some c' → P c' := by
    intro c c' ⟨hwin, hsi, hp1, hp2⟩ hst
    have hne := state_ne_qhalt_of_step hst
    have hsi' : CfgStartInvariant c' := hsi.step hst
    rcases hstate : c.state with q | q
    · by_cases hq : q = tm₁.qhalt
      · subst hq
        obtain ⟨hi, hw, ho⟩ := seq_head_bound tm₁ tm₂ hstate hst hsi.1 hsi.2.1 hsi.2.2
        have hwin' : c'.WithinDecisionSpace inputLength space := by
          refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
          · have := hw i; have := hwin.1.1 i; omega
          · have := hwin.1.2; omega
          · have := hwin.2; omega
        refine ⟨hwin', hsi', ?_, ?_⟩
        · intro q' hq'
          have hc : c = phase1Wrap tm₁ tm₂ ⟨tm₁.qhalt, c.input, c.work, c.output⟩ :=
            Cfg.ext hstate rfl rfl rfl
          rw [hc] at hst
          rw [seqTM_transition_step tm₁ tm₂ rfl] at hst
          rw [← Option.some_inj.mp hst] at hq'
          exact absurd hq' (by nofun)
        · intro q' hq'
          have hc : c = phase1Wrap tm₁ tm₂ ⟨tm₁.qhalt, c.input, c.work, c.output⟩ :=
            Cfg.ext hstate rfl rfl rfl
          rw [hc] at hst
          rw [seqTM_transition_step tm₁ tm₂ rfl] at hst
          have hc' := Option.some_inj.mp hst
          subst hc'
          have hq2 : q' = tm₂.qstart := by
            have : (Sum.inr tm₂.qstart : SeqQ tm₁.Q tm₂.Q) = Sum.inr q' := hq'
            exact (Sum.inr.injEq _ _ ▸ this).symm
          subst hq2
          exact ⟨_, rfl, hwin', hsi', Relation.ReflTransGen.refl⟩
      · obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hp1 q hstate
        have hc : c = phase1Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tm₁.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
        have hsim := seqTM_phase1_step tm₁ tm₂ hstep0
        rw [hc] at hst
        have hc'eq : c' = phase1Wrap tm₁ tm₂ e' := Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tm₁.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
        subst hc'eq
        exact ⟨h₁ d hd0 hd1 hd2 e' hre, hsi',
          fun q' hq' => ⟨d, hd0, hd1, hd2, by
            rw [show (⟨q', (phase1Wrap tm₁ tm₂ e').input, (phase1Wrap tm₁ tm₂ e').work,
              (phase1Wrap tm₁ tm₂ e').output⟩ : Cfg n tm₁.Q) = e' from
              Cfg.ext (Sum.inl.injEq _ _ ▸ hq').symm rfl rfl rfl]
            exact hre⟩,
          fun _ hq' => absurd hq' (by nofun)⟩
    · have hq : q ≠ tm₂.qhalt := fun h => hne (by rw [hstate, h]; rfl)
      obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hp2 q hstate
      have hc : c = phase2Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨e', hstep0⟩ :
          ∃ e', tm₂.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
        rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
      have hsim := seqTM_phase2_step tm₁ tm₂ hstep0
      rw [hc] at hst
      have hc'eq : c' = phase2Wrap tm₁ tm₂ e' := Option.some_inj.mp (hst.symm.trans hsim)
      have hre : tm₂.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
      subst hc'eq
      exact ⟨h₂ d hd0 hd1 hd2 e' hre, hsi',
        fun _ hq' => absurd hq' (by nofun),
        fun q' hq' => ⟨d, hd0, hd1, hd2, by
          rw [show (⟨q', (phase2Wrap tm₁ tm₂ e').input, (phase2Wrap tm₁ tm₂ e').work,
            (phase2Wrap tm₁ tm₂ e').output⟩ : Cfg n tm₂.Q) = e' from
            Cfg.ext (Sum.inr.injEq _ _ ▸ hq').symm rfl rfl rfl]
          exact hre⟩⟩
  have hinit : P c₀ := by
    refine ⟨hwin₀, hsi₀, ?_, ?_⟩
    · intro q hq
      have : q = tm₁.qstart := by
        have h := hstart.symm.trans hq
        exact (Sum.inl.injEq _ _ ▸ h).symm
      subst this
      exact ⟨_, rfl, hwin₀, hsi₀, Relation.ReflTransGen.refl⟩
    · intro q hq
      rw [hstart] at hq
      exact absurd hq (by nofun)
  have key : ∀ c, (seqTM tm₁ tm₂).reaches c₀ c → P c := by
    intro c h
    induction h with
    | refl => exact hinit
    | tail _ hs ih => exact hstep _ _ ih hs
  exact (key cfin hreach).1

/-- **The loop keeps the window, however many iterations it runs.** Body and test are each
entered at their own start state with windowed tapes, and every step the loop interposes between
them idles the input and work tapes, so nothing accumulates across iterations. -/
theorem loopTM_keepsWindow (tmBody tmTest : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    (hbody : tmBody.KeepsWindow inputLength space)
    (htest : tmTest.KeepsWindow inputLength space) :
    (loopTM tmBody tmTest).KeepsWindow inputLength space := by
  intro c₀ hstart hwin₀ hsi₀ cfin hreach
  set P : Cfg n (loopTM tmBody tmTest).Q → Prop := fun c =>
    c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c ∧
    (∀ q, c.state = Sum.inl q → ∃ d : Cfg n tmBody.Q, d.state = tmBody.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tmBody.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr (Sum.inr q) → ∃ d : Cfg n tmTest.Q, d.state = tmTest.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tmTest.reaches d ⟨q, c.input, c.work, c.output⟩) with hPdef
  have hstepP : ∀ c c', P c → (loopTM tmBody tmTest).step c = some c' → P c' := by
    intro c c' ⟨hwin, hsi, hp1, hp2⟩ hst
    have hne := state_ne_qhalt_of_step hst
    have hsi' : CfgStartInvariant c' := hsi.step hst
    by_cases hb : ∀ q, c.state = Sum.inl q → q = tmBody.qhalt
    · by_cases ht : ∀ q, c.state = Sum.inr (Sum.inr q) → q = tmTest.qhalt
      · obtain ⟨hi, hw, ho⟩ := loop_head_bound tmBody tmTest hb ht hst hsi.1 hsi.2.1 hsi.2.2
        have hwin' : c'.WithinDecisionSpace inputLength space := by
          refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
          · have := hw i; have := hwin.1.1 i; omega
          · have := hwin.1.2; omega
          · have := hwin.2; omega
        obtain ⟨hs1, hs2⟩ := loop_idle_step_state tmBody tmTest hb ht hst
        refine ⟨hwin', hsi', ?_, ?_⟩
        · intro q' hq'
          exact ⟨⟨q', c'.input, c'.work, c'.output⟩, hs1 q' hq', hwin', hsi',
            Relation.ReflTransGen.refl⟩
        · intro q' hq'
          exact ⟨⟨q', c'.input, c'.work, c'.output⟩, hs2 q' hq', hwin', hsi',
            Relation.ReflTransGen.refl⟩
      · push Not at ht
        obtain ⟨q, hstate, hq⟩ := ht
        obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hp2 q hstate
        have hc : c = loopTestWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tmTest.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
        have hsim := loopTM_test_step tmBody tmTest hstep0
        rw [hc] at hst
        have hc'eq : c' = loopTestWrap tmBody tmTest e' :=
          Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tmTest.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
        subst hc'eq
        exact ⟨htest d hd0 hd1 hd2 e' hre, hsi',
          fun _ hq' => absurd hq' (by nofun),
          fun q' hq' => ⟨d, hd0, hd1, hd2, by
            rw [show (⟨q', (loopTestWrap tmBody tmTest e').input,
              (loopTestWrap tmBody tmTest e').work,
              (loopTestWrap tmBody tmTest e').output⟩ : Cfg n tmTest.Q) = e' from
              Cfg.ext (by injection hq'.symm with h; injection h) rfl rfl rfl]
            exact hre⟩⟩
    · push Not at hb
      obtain ⟨q, hstate, hq⟩ := hb
      obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hp1 q hstate
      have hc : c = loopBodyWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨e', hstep0⟩ :
          ∃ e', tmBody.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
        rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
      have hsim := loopTM_body_step tmBody tmTest hstep0
      rw [hc] at hst
      have hc'eq : c' = loopBodyWrap tmBody tmTest e' :=
        Option.some_inj.mp (hst.symm.trans hsim)
      have hre : tmBody.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
      subst hc'eq
      exact ⟨hbody d hd0 hd1 hd2 e' hre, hsi',
        fun q' hq' => ⟨d, hd0, hd1, hd2, by
          rw [show (⟨q', (loopBodyWrap tmBody tmTest e').input,
            (loopBodyWrap tmBody tmTest e').work,
            (loopBodyWrap tmBody tmTest e').output⟩ : Cfg n tmBody.Q) = e' from
            Cfg.ext (by injection hq'.symm) rfl rfl rfl]
          exact hre⟩,
        fun _ hq' => absurd hq' (by nofun)⟩
  have hinit : P c₀ := by
    refine ⟨hwin₀, hsi₀, ?_, ?_⟩
    · intro q hq
      have hqs : q = tmBody.qstart := by
        have h := hstart.symm.trans hq
        exact (Sum.inl.injEq _ _ ▸ h).symm
      subst hqs
      exact ⟨_, rfl, hwin₀, hsi₀, Relation.ReflTransGen.refl⟩
    · intro q hq
      rw [hstart] at hq
      exact absurd hq (by nofun)
  have key : ∀ c, (loopTM tmBody tmTest).reaches c₀ c → P c := by
    intro c h
    induction h with
    | refl => exact hinit
    | tail _ hs ih => exact hstepP _ _ ih hs
  exact (key cfin hreach).1

/-- **The conditional keeps the window.** Test and branch are each entered at their own start
state with windowed tapes, and the steps between them idle every tape. -/
theorem ifTM_keepsWindow (tmTest tmThen tmElse : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    (htest : tmTest.KeepsWindow inputLength space)
    (hthen : tmThen.KeepsWindow inputLength space)
    (helse : tmElse.KeepsWindow inputLength space) :
    (ifTM tmTest tmThen tmElse).KeepsWindow inputLength space := by
  intro c₀ hstart hwin₀ hsi₀ cfin hreach
  set P : Cfg n (ifTM tmTest tmThen tmElse).Q → Prop := fun c =>
    c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c ∧
    (∀ q, c.state = Sum.inl q → ∃ d : Cfg n tmTest.Q, d.state = tmTest.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tmTest.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr (Sum.inr (Sum.inl q)) → ∃ d : Cfg n tmThen.Q,
        d.state = tmThen.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tmThen.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr (Sum.inr (Sum.inr q)) → ∃ d : Cfg n tmElse.Q,
        d.state = tmElse.qstart ∧
        d.WithinDecisionSpace inputLength space ∧ CfgStartInvariant d ∧
        tmElse.reaches d ⟨q, c.input, c.work, c.output⟩) with hPdef
  have hstepP : ∀ c c', P c → (ifTM tmTest tmThen tmElse).step c = some c' → P c' := by
    intro c c' hPc hst
    obtain ⟨hwin, hsi, hpt, hpth, hpel⟩ := hPc
    have hne := state_ne_qhalt_of_step hst
    have hsi' : CfgStartInvariant c' := hsi.step hst
    by_cases h1 : ∀ q, c.state = Sum.inl q → q = tmTest.qhalt
    · by_cases h2 : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inl q)) → q = tmThen.qhalt
      · by_cases h3 : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inr q)) → q = tmElse.qhalt
        · obtain ⟨hi, hw, ho⟩ :=
            if_head_bound tmTest tmThen tmElse h1 h2 h3 hst hsi.1 hsi.2.1 hsi.2.2
          have hwin' : c'.WithinDecisionSpace inputLength space := by
            refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
            · have := hw i
              have := hwin.1.1 i
              omega
            · have := hwin.1.2
              omega
            · have := hwin.2
              omega
          rcases if_idle_step_state tmTest tmThen tmElse h1 h2 h3 hst with
            ⟨ph, hph⟩ | hthq | helq
          · exact ⟨hwin', hsi',
              fun _ hq => absurd (hq.symm.trans hph) (by nofun),
              fun _ hq => absurd (hq.symm.trans hph) (by nofun),
              fun _ hq => absurd (hq.symm.trans hph) (by nofun)⟩
          · refine ⟨hwin', hsi', fun _ hq => absurd (hq.symm.trans hthq) (by nofun), ?_,
              fun _ hq => absurd (hq.symm.trans hthq) (by nofun)⟩
            intro q' hq'
            have hqq : q' = tmThen.qstart := by
              have hA := hthq.symm.trans hq'
              injection hA with hB
              injection hB with hC
              injection hC with hD
              exact hD.symm
            subst hqq
            exact ⟨_, rfl, hwin', hsi', Relation.ReflTransGen.refl⟩
          · refine ⟨hwin', hsi', fun _ hq => absurd (hq.symm.trans helq) (by nofun),
              fun _ hq => absurd (hq.symm.trans helq) (by nofun), ?_⟩
            intro q' hq'
            have hqq : q' = tmElse.qstart := by
              have hA := helq.symm.trans hq'
              injection hA with hB
              injection hB with hC
              injection hC with hD
              exact hD.symm
            subst hqq
            exact ⟨_, rfl, hwin', hsi', Relation.ReflTransGen.refl⟩
        · push Not at h3
          obtain ⟨q, hstate, hq⟩ := h3
          obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hpel q hstate
          have hc : c = ifElseWrap tmTest tmThen tmElse ⟨q, c.input, c.work, c.output⟩ :=
            Cfg.ext hstate rfl rfl rfl
          obtain ⟨e', hstep0⟩ :
              ∃ e', tmElse.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
            rw [TM.step, ite_eq_right hq]
            exact ⟨_, rfl⟩
          have hsim := ifTM_else_step tmTest tmThen tmElse hstep0
          rw [hc] at hst
          have hc'eq : c' = ifElseWrap tmTest tmThen tmElse e' :=
            Option.some_inj.mp (hst.symm.trans hsim)
          have hre : tmElse.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
          subst hc'eq
          refine ⟨helse d hd0 hd1 hd2 e' hre, hsi',
            fun _ hq' => absurd hq' (by nofun),
            fun _ hq' => absurd hq' (by nofun), ?_⟩
          intro q' hq'
          refine ⟨d, hd0, hd1, hd2, ?_⟩
          have hqq : q' = e'.state := by
            injection hq' with hB
            injection hB with hC
            injection hC with hD
            exact hD.symm
          subst hqq
          exact hre
      · push Not at h2
        obtain ⟨q, hstate, hq⟩ := h2
        obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hpth q hstate
        have hc : c = ifThenWrap tmTest tmThen tmElse ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tmThen.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]
          exact ⟨_, rfl⟩
        have hsim := ifTM_then_step tmTest tmThen tmElse hstep0
        rw [hc] at hst
        have hc'eq : c' = ifThenWrap tmTest tmThen tmElse e' :=
          Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tmThen.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
        subst hc'eq
        refine ⟨hthen d hd0 hd1 hd2 e' hre, hsi',
          fun _ hq' => absurd hq' (by nofun), ?_,
          fun _ hq' => absurd hq' (by nofun)⟩
        intro q' hq'
        refine ⟨d, hd0, hd1, hd2, ?_⟩
        have hqq : q' = e'.state := by
          injection hq' with hB
          injection hB with hC
          injection hC with hD
          exact hD.symm
        subst hqq
        exact hre
    · push Not at h1
      obtain ⟨q, hstate, hq⟩ := h1
      obtain ⟨d, hd0, hd1, hd2, hd3⟩ := hpt q hstate
      have hc : c = ifTestWrap tmTest tmThen tmElse ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨e', hstep0⟩ :
          ∃ e', tmTest.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
        rw [TM.step, ite_eq_right hq]
        exact ⟨_, rfl⟩
      have hsim := ifTM_test_step tmTest tmThen tmElse hstep0
      rw [hc] at hst
      have hc'eq : c' = ifTestWrap tmTest tmThen tmElse e' :=
        Option.some_inj.mp (hst.symm.trans hsim)
      have hre : tmTest.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
      subst hc'eq
      refine ⟨htest d hd0 hd1 hd2 e' hre, hsi', ?_,
        fun _ hq' => absurd hq' (by nofun),
        fun _ hq' => absurd hq' (by nofun)⟩
      intro q' hq'
      refine ⟨d, hd0, hd1, hd2, ?_⟩
      have hqq : q' = e'.state := by
        injection hq'.symm
      subst hqq
      exact hre
  have hinit : P c₀ := by
    refine ⟨hwin₀, hsi₀, ?_, ?_, ?_⟩
    · intro q hq
      have hqs : q = tmTest.qstart := by
        have hA := hstart.symm.trans hq
        injection hA with hB
        exact hB.symm
      subst hqs
      exact ⟨_, rfl, hwin₀, hsi₀, Relation.ReflTransGen.refl⟩
    · intro q hq
      rw [hstart] at hq
      exact absurd hq (by nofun)
    · intro q hq
      rw [hstart] at hq
      exact absurd hq (by nofun)
  have key : ∀ c, (ifTM tmTest tmThen tmElse).reaches c₀ c → P c := by
    intro c h
    induction h with
    | refl => exact hinit
    | tail _ hs ih => exact hstepP _ _ ih hs
  exact (key cfin hreach).1

/-- **The machine keeps its window on runs that start from a configuration satisfying `pre`.**
The precondition is what a subroutine simulating another machine needs: its space bound only
covers runs whose scratch tapes started blank, so a composition rule has to re-establish that at
every entry. -/
def KeepsWindowOn (tm : TM n) (pre : Cfg n tm.Q → Prop) (inputLength space : ℕ) : Prop :=
  ∀ c, pre c → ∀ c', tm.reaches c c' → c'.WithinDecisionSpace inputLength space

/-- Keeping the window unconditionally is keeping it on any precondition that pins the start
state and the window. -/
theorem KeepsWindow.keepsWindowOn {tm : TM n} {inputLength space : ℕ}
    (h : tm.KeepsWindow inputLength space) {pre : Cfg n tm.Q → Prop}
    (hpre : ∀ c, pre c → c.state = tm.qstart ∧ c.WithinDecisionSpace inputLength space ∧
      CfgStartInvariant c) :
    tm.KeepsWindowOn pre inputLength space := fun c hc c' hreach =>
  h c (hpre c hc).1 (hpre c hc).2.1 (hpre c hc).2.2 c' hreach

/-- Weakening the precondition of a windowed contract. -/
theorem KeepsWindowOn.mono {tm : TM n} {pre pre' : Cfg n tm.Q → Prop} {inputLength space : ℕ}
    (h : tm.KeepsWindowOn pre inputLength space) (hpre : ∀ c, pre' c → pre c) :
    tm.KeepsWindowOn pre' inputLength space := fun c hc => h c (hpre c hc)

/-- **Sequential composition keeps the window, with preconditions.** The second machine's
precondition is re-established from the first machine's postcondition: `TM.halted_unique` says the
configuration met at the phase boundary is the very one the first machine's Hoare triple
describes, and the interposed step transforms its tapes in the fixed way `transitionTape` records.
-/
theorem seqTM_keepsWindowOn (tm₁ tm₂ : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    {pre₁ : Cfg n tm₁.Q → Prop} {pre₂ : Cfg n tm₂.Q → Prop} {mid : TapePred n}
    (hpre₁ : ∀ c, pre₁ c → c.state = tm₁.qstart ∧ c.WithinDecisionSpace inputLength space ∧
      CfgStartInvariant c)
    (h₁ : tm₁.KeepsWindowOn pre₁ inputLength space)
    (h₁post : ∀ c, pre₁ c → ∃ e, tm₁.reaches c e ∧ tm₁.halted e ∧ mid e.input e.work e.output)
    (h₂ : tm₂.KeepsWindowOn pre₂ inputLength space)
    (htrans : ∀ inp work out, mid inp work out →
      pre₂ ⟨tm₂.qstart, transitionInput inp, fun i => transitionTape (work i),
        transitionTape out⟩) :
    (seqTM tm₁ tm₂).KeepsWindowOn
      (fun c => ∃ d, pre₁ d ∧ c = phase1Wrap tm₁ tm₂ d) inputLength space := by
  rintro c₀ ⟨d₀, hd₀, rfl⟩ cfin hreach
  obtain ⟨hd₀start, hd₀win, hd₀si⟩ := hpre₁ d₀ hd₀
  set P : Cfg n (seqTM tm₁ tm₂).Q → Prop := fun c =>
    c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c ∧
    (∀ q, c.state = Sum.inl q →
      ∃ d, pre₁ d ∧ tm₁.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr q →
      ∃ d, pre₂ d ∧ tm₂.reaches d ⟨q, c.input, c.work, c.output⟩) with hPdef
  have hstepP : ∀ c c', P c → (seqTM tm₁ tm₂).step c = some c' → P c' := by
    intro c c' hPc hst
    obtain ⟨hwin, hsi, hp1, hp2⟩ := hPc
    have hne := state_ne_qhalt_of_step hst
    have hsi' : CfgStartInvariant c' := hsi.step hst
    rcases hstate : c.state with q | q
    · obtain ⟨d, hd, hdreach⟩ := hp1 q hstate
      by_cases hq : q = tm₁.qhalt
      · subst hq
        obtain ⟨hi, hw, ho⟩ := seq_head_bound tm₁ tm₂ hstate hst hsi.1 hsi.2.1 hsi.2.2
        have hwin' : c'.WithinDecisionSpace inputLength space := by
          refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
          · have := hw i
            have := hwin.1.1 i
            omega
          · have := hwin.1.2
            omega
          · have := hwin.2
            omega
        obtain ⟨e, hereach, hehalt, hemid⟩ := h₁post d hd
        have heq : (⟨tm₁.qhalt, c.input, c.work, c.output⟩ : Cfg n tm₁.Q) = e :=
          halted_unique hdreach hereach rfl hehalt
        have hc : c = phase1Wrap tm₁ tm₂ ⟨tm₁.qhalt, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        rw [hc, seqTM_transition_step tm₁ tm₂ rfl] at hst
        have hc'eq := Option.some_inj.mp hst
        subst hc'eq
        refine ⟨hwin', hsi', fun _ hq' => absurd hq' (by nofun), ?_⟩
        intro q' hq'
        have hq2 : q' = tm₂.qstart := by
          injection hq'.symm with hB
        subst hq2
        refine ⟨_, htrans _ _ _ ?_, Relation.ReflTransGen.refl⟩
        rw [show c.input = e.input from congrArg Cfg.input heq,
          show c.work = e.work from congrArg Cfg.work heq,
          show c.output = e.output from congrArg Cfg.output heq]
        exact hemid
      · have hc : c = phase1Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tm₁.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]
          exact ⟨_, rfl⟩
        have hsim := seqTM_phase1_step tm₁ tm₂ hstep0
        rw [hc] at hst
        have hc'eq : c' = phase1Wrap tm₁ tm₂ e' := Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tm₁.reaches d e' := Relation.ReflTransGen.tail hdreach hstep0
        subst hc'eq
        refine ⟨h₁ d hd e' hre, hsi', ?_, fun _ hq' => absurd hq' (by nofun)⟩
        intro q' hq'
        refine ⟨d, hd, ?_⟩
        have hqq : q' = e'.state := by
          injection hq' with hB
          exact hB.symm
        subst hqq
        exact hre
    · have hq : q ≠ tm₂.qhalt := fun h => hne (by rw [hstate, h]; rfl)
      obtain ⟨d, hd, hdreach⟩ := hp2 q hstate
      have hc : c = phase2Wrap tm₁ tm₂ ⟨q, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      obtain ⟨e', hstep0⟩ :
          ∃ e', tm₂.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
        rw [TM.step, ite_eq_right hq]
        exact ⟨_, rfl⟩
      have hsim := seqTM_phase2_step tm₁ tm₂ hstep0
      rw [hc] at hst
      have hc'eq : c' = phase2Wrap tm₁ tm₂ e' := Option.some_inj.mp (hst.symm.trans hsim)
      have hre : tm₂.reaches d e' := Relation.ReflTransGen.tail hdreach hstep0
      subst hc'eq
      refine ⟨h₂ d hd e' hre, hsi', fun _ hq' => absurd hq' (by nofun), ?_⟩
      intro q' hq'
      refine ⟨d, hd, ?_⟩
      have hqq : q' = e'.state := by
        injection hq' with hB
        exact hB.symm
      subst hqq
      exact hre
  have hinit : P (phase1Wrap tm₁ tm₂ d₀) := by
    refine ⟨hd₀win, hd₀si, ?_, fun _ hq => absurd hq (by nofun)⟩
    intro q hq
    refine ⟨d₀, hd₀, ?_⟩
    have hqq : q = d₀.state := by
      injection hq.symm with hB
    subst hqq
    exact Relation.ReflTransGen.refl
  have key : ∀ c, (seqTM tm₁ tm₂).reaches (phase1Wrap tm₁ tm₂ d₀) c → P c := by
    intro c h
    induction h with
    | refl => exact hinit
    | tail _ hstp ih => exact hstepP _ _ ih hstp
  exact (key cfin hreach).1

/-- **A sequential composition is robust as soon as its first stage is.** This is what makes the
unconditional rules usable in practice. A subroutine that simulates another machine needs its
scratch tapes blank, so it only satisfies the precondition-carrying contract; but prefix it with a
stage that clears the scratch — one that *is* robust — and the composite is robust too, because
the first stage's postcondition supplies the second stage's precondition. The composite can then
be dropped straight into `TM.loopTM_keepsWindow`, whose body hypothesis is the unconditional one.
-/
theorem seqTM_keepsWindow_of_post (tm₁ tm₂ : TM n) {inputLength space : ℕ} (hs : 1 ≤ space)
    {pre₂ : Cfg n tm₂.Q → Prop} {mid : TapePred n}
    (h₁ : tm₁.KeepsWindow inputLength space)
    (h₁post : ∀ c : Cfg n tm₁.Q, c.state = tm₁.qstart →
      c.WithinDecisionSpace inputLength space → CfgStartInvariant c →
      ∃ e, tm₁.reaches c e ∧ tm₁.halted e ∧ mid e.input e.work e.output)
    (h₂ : tm₂.KeepsWindowOn pre₂ inputLength space)
    (htrans : ∀ inp work out, mid inp work out →
      pre₂ ⟨tm₂.qstart, transitionInput inp, fun i => transitionTape (work i),
        transitionTape out⟩) :
    (seqTM tm₁ tm₂).KeepsWindow inputLength space := by
  intro c₀ hstart hwin hsi cfin hreach
  have hkw := seqTM_keepsWindowOn tm₁ tm₂ hs
    (pre₁ := fun c => c.state = tm₁.qstart ∧ c.WithinDecisionSpace inputLength space ∧
      CfgStartInvariant c)
    (pre₂ := pre₂) (mid := mid)
    (fun _ h => h)
    (h₁.keepsWindowOn (fun _ h => h))
    (fun c h => h₁post c h.1 h.2.1 h.2.2)
    h₂ htrans
  have hc : c₀ = phase1Wrap tm₁ tm₂ ⟨tm₁.qstart, c₀.input, c₀.work, c₀.output⟩ :=
    Cfg.ext hstart rfl rfl rfl
  refine hkw c₀ ⟨⟨tm₁.qstart, c₀.input, c₀.work, c₀.output⟩, ⟨rfl, hwin, hsi⟩, hc⟩ cfin hreach

/-! ## Time-bounded subroutines keep a window -/

/-- **A subroutine that halts in `t` steps keeps a window `t` cells wider than its start.**
Every head moves at most one cell per step, and a deterministic run cannot outlast its halt, so a
configuration starting with its heads inside `h` can only have pushed them to `h + t`.

This is the bridge from the library's existing time contracts: any subroutine with a
`TM.HoareTime`-style halting bound acquires a window contract, with no new tape analysis. -/
theorem keepsWindowOn_of_haltsIn {tm : TM n} {pre : Cfg n tm.Q → Prop}
    {inputLength h t : ℕ}
    (hwork : ∀ c, pre c → ∀ i, (c.work i).head ≤ h)
    (hinput : ∀ c, pre c → c.input.head ≤ inputLength + h + 1)
    (houtput : ∀ c, pre c → c.output.head ≤ h + 1)
    (hhalt : ∀ c, pre c → ∃ e t', t' ≤ t ∧ tm.reachesIn t' c e ∧ tm.halted e) :
    tm.KeepsWindowOn pre inputLength (h + t) := by
  intro c hc c' hreach
  obtain ⟨s, hs⟩ := TM.reaches_to_reachesIn tm hreach
  obtain ⟨e, t', ht', hte, hhe⟩ := hhalt c hc
  have hle : s ≤ t := le_trans (TM.reachesIn_le_halt tm hs hte hhe) ht'
  obtain ⟨hi, ho, hw⟩ := head_le_start_add_of_reachesIn tm hs
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · have h₁ := hw i
    have h₂ := hwork c hc i
    omega
  · have h₂ := hinput c hc
    omega
  · have h₂ := houtput c hc
    omega

/-- **Every `TM.HoareTime` contract yields a window contract.** The library's subroutines are
specified by halting-time triples; this converts any of them, with no tape analysis, provided the
precondition pins where the heads start. The window is the starting bound plus the running time,
since a head moves at most one cell per step. -/
theorem keepsWindowOn_of_hoareTime {tm : TM n} {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) {inputLength h₀ : ℕ}
    (hwork : ∀ inp work out, pre inp work out → ∀ i, (work i).head ≤ h₀)
    (hinput : ∀ inp work out, pre inp work out → inp.head ≤ inputLength + h₀ + 1)
    (houtput : ∀ inp work out, pre inp work out → out.head ≤ h₀ + 1) :
    tm.KeepsWindowOn
      (fun c => c.state = tm.qstart ∧ pre c.input c.work c.output)
      inputLength (h₀ + b) := by
  refine keepsWindowOn_of_haltsIn (fun c hc i => hwork _ _ _ hc.2 i)
    (fun c hc => hinput _ _ _ hc.2) (fun c hc => houtput _ _ _ hc.2) (fun c hc => ?_)
  obtain ⟨c', t, hle, hreach, hhalt, -⟩ := h c.input c.work c.output hc.2
  refine ⟨c', t, hle, ?_, hhalt⟩
  have hceq : ({ state := tm.qstart, input := c.input, work := c.work, output := c.output } :
      Cfg n tm.Q) = c := Cfg.ext hc.1.symm rfl rfl rfl
  rwa [hceq] at hreach

/-- **The pinned form**, matching how the library states its framed subroutine contracts: the
precondition names the three tapes exactly, so the head bounds are three facts about literals. -/
theorem keepsWindowOn_of_hoareTime_pinned {tm : TM n} {post : TapePred n} {b : ℕ}
    {inp₀ : Tape} {work₀ : Fin n → Tape} {out₀ : Tape}
    (h : tm.HoareTime (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀) post b)
    {inputLength h₀ : ℕ}
    (hwork : ∀ i, (work₀ i).head ≤ h₀)
    (hinput : inp₀.head ≤ inputLength + h₀ + 1)
    (houtput : out₀.head ≤ h₀ + 1) :
    tm.KeepsWindowOn
      (fun c => c.state = tm.qstart ∧
        (c.input = inp₀ ∧ c.work = work₀ ∧ c.output = out₀))
      inputLength (h₀ + b) :=
  keepsWindowOn_of_hoareTime h
    (fun _ _ _ hpre i => by rw [hpre.2.1]; exact hwork i)
    (fun _ _ _ hpre => by rw [hpre.1]; exact hinput)
    (fun _ _ _ hpre => by rw [hpre.2.2]; exact houtput)

/-- The unconditional form: a machine that halts within `t` steps from *every* configuration
inside the window keeps the widened window. -/
theorem keepsWindow_of_haltsIn {tm : TM n} {inputLength h t : ℕ}
    (hhalt : ∀ c : Cfg n tm.Q, c.state = tm.qstart →
      c.WithinDecisionSpace inputLength h → CfgStartInvariant c →
      ∃ e t', t' ≤ t ∧ tm.reachesIn t' c e ∧ tm.halted e) :
    tm.KeepsWindowOn
      (fun c => c.state = tm.qstart ∧ c.WithinDecisionSpace inputLength h ∧
        CfgStartInvariant c) inputLength (h + t) :=
  keepsWindowOn_of_haltsIn
    (fun _ hc i => hc.2.1.1.1 i)
    (fun _ hc => hc.2.1.1.2)
    (fun _ hc => hc.2.1.2)
    (fun c hc => hhalt c hc.1 hc.2.1 hc.2.2)

/-! ## Interoperation with the library's space contracts -/

/-- **A window contract is a `TM.HoareSpace` contract.** `TM.HoareSpace` is the library's own
anchored space judgement; it bounds `Cfg.WithinAuxSpace`, which ignores the output tape, whereas
a window additionally bounds the output head as `TM.DecidesInSpace` requires. So a window is the
stronger statement, and anything established with the composition rules above can be handed to
`TM.seqTM_hoareTimeSpace` and `TM.computesInSpace_of_hoareTimeSpace`. -/
theorem KeepsWindowOn.hoareSpace {tm : TM n} {pre : TapePred n} {inputLength space : ℕ}
    (h : tm.KeepsWindowOn
      (fun c => c.state = tm.qstart ∧ pre c.input c.work c.output) inputLength space) :
    tm.HoareSpace pre inputLength space :=
  fun inp work out hpre c' hreach =>
    (h { state := tm.qstart, input := inp, work := work, output := out } ⟨rfl, hpre⟩ c' hreach).1

/-- The unconditional form likewise yields a `TM.HoareSpace` contract, on any precondition that
pins the window and the left markers. -/
theorem KeepsWindow.hoareSpace {tm : TM n} {inputLength space : ℕ}
    (h : tm.KeepsWindow inputLength space) {pre : TapePred n}
    (hpre : ∀ inp work out, pre inp work out →
      ({ state := tm.qstart, input := inp, work := work, output := out } :
        Cfg n tm.Q).WithinDecisionSpace inputLength space ∧
      CfgStartInvariant { state := tm.qstart, input := inp, work := work, output := out }) :
    tm.HoareSpace pre inputLength space :=
  fun inp work out hp c' hreach =>
    (h { state := tm.qstart, input := inp, work := work, output := out } rfl
      (hpre inp work out hp).1 (hpre inp work out hp).2 c' hreach).1

/-! ## From a window to a space-bounded decider -/

/-- The initial configuration parks every head at the left end, so it sits inside every window. -/
theorem initCfg_withinDecisionSpace (tm : TM n) (x : List Bool) (inputLength space : ℕ) :
    (tm.initCfg x).WithinDecisionSpace inputLength space := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩ <;> simp

/-- Every tape of the initial configuration carries its left-end marker. -/
theorem cfgStartInvariant_initCfg (tm : TM n) (x : List Bool) :
    CfgStartInvariant (tm.initCfg x) :=
  ⟨startInvariant_initOfBool x, fun _ => startInvariant_initNil, startInvariant_initNil⟩

/-- **A machine that respects its window and decides `L` decides `L` in that space.** This is the
landing gear: a construction assembled from `TM.seqTM_respectsWindow` and
`TM.loopTM_respectsWindow` needs only its correctness proof to become a `DSPACE` membership. -/
theorem decidesInSpace_of_respectsWindow {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hwin : ∀ x : List Bool, tm.RespectsWindow x.length (S x.length))
    (hdec : ∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)) :
    tm.DecidesInSpace L S := by
  refine ⟨fun x c' hreach => ?_, hdec⟩
  have key : ∀ c, tm.reaches (tm.initCfg x) c →
      c.WithinDecisionSpace x.length (S x.length) ∧ CfgStartInvariant c := by
    intro c h
    induction h with
    | refl => exact ⟨initCfg_withinDecisionSpace tm x _ _, cfgStartInvariant_initCfg tm x⟩
    | tail _ hs ih => exact ⟨hwin x _ _ ih.1 ih.2 hs, ih.2.step hs⟩
  exact (key c' hreach).1

/-- **A machine that keeps its window and decides `L` decides `L` in that space.** -/
theorem decidesInSpace_of_keepsWindow {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hwin : ∀ x : List Bool, tm.KeepsWindow x.length (S x.length))
    (hdec : ∀ x : List Bool, ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧ (x ∉ L → c'.output.cells 1 = Γ.zero)) :
    tm.DecidesInSpace L S :=
  ⟨fun x c' hreach =>
    hwin x (tm.initCfg x) rfl (initCfg_withinDecisionSpace tm x _ _)
      (cfgStartInvariant_initCfg tm x) c' hreach,
   hdec⟩


/-- **A loop keeps a window one iteration at a time.** The loop's *total* run is exponentially
long when the counter is, so no bound of the form "space ≤ time" can help. What is true is that
every configuration the loop passes through lies within one iteration of some indexed state, and
each iteration is short: `hiter` asks only that a single iteration stay inside the window.

Determinism is what makes the reduction work. A run that leaves the current iteration must pass
through the next iteration's start configuration, because two runs from the same configuration are
prefixes of one another. -/
theorem loopTM_keepsWindow_indexed (tmBody tmTest : TM n) {inputLength space : ℕ}
    (E : ℕ → TapePred n) (N b : ℕ)
    (hstep : ∀ j, j < N → ∀ inp work out, E j inp work out →
      ∃ inp' work' out' t, 1 ≤ t ∧ t ≤ b ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        E (j + 1) inp' work' out')
    (hstop : ∀ inp work out, E N inp work out →
      ∃ c' t, t ≤ b ∧ (loopTM tmBody tmTest).reachesIn t
        ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c')
    (hiter : ∀ j, j ≤ N → ∀ inp work out, E j inp work out →
      ∀ (c : Cfg n (loopTM tmBody tmTest).Q) (t : ℕ), t ≤ b →
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength space) :
    ∀ j, j ≤ N → ∀ inp work out, E j inp work out →
      ∀ c, (loopTM tmBody tmTest).reaches
        ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength space := by
  have key : ∀ t : ℕ, ∀ j, j ≤ N → ∀ inp work out, E j inp work out →
      ∀ c, (loopTM tmBody tmTest).reachesIn t
        ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength space := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro j hjN inp work out hE c hreach
      by_cases hb : t ≤ b
      · exact hiter j hjN inp work out hE c t hb hreach
      · rw [Nat.not_le] at hb
        rcases Nat.lt_or_ge j N with hj | hj
        · obtain ⟨inp', work', out', s, hs1, hs, hrun, hE'⟩ := hstep j hj inp work out hE
          have hprefix := reachesIn_prefix (loopTM tmBody tmTest) hrun hreach (by omega)
          refine ih (t - s) (by omega) (j + 1) (by omega) inp' work' out' hE' c hprefix
        · have hjeq : j = N := by omega
          subst hjeq
          obtain ⟨d, s, hs, hrun, hhalt⟩ := hstop inp work out hE
          have hprefix := reachesIn_prefix (loopTM tmBody tmTest) hrun hreach (by omega)
          obtain ⟨u, hu⟩ : ∃ u, t - s = u + 1 := ⟨t - s - 1, by omega⟩
          rw [hu] at hprefix
          cases hprefix with
          | step hstepd _ =>
              exact absurd hstepd (by
                simp only [TM.step, hhalt, ↓reduceIte]
                nofun)
  intro j hjN inp work out hE c hreach
  obtain ⟨t, ht⟩ := TM.reaches_to_reachesIn _ hreach
  exact key t j hjN inp work out hE c ht


/-- **A loop whose indexed states are parked keeps a window of one iteration's width.** Inside a
single iteration no head can travel further than the iteration is long, and each indexed state
has every head at cell one, so `1 + b` cells suffice — for the whole run, however many iterations
it takes. -/
theorem loopTM_keepsWindow_indexed_of_parked (tmBody tmTest : TM n) {inputLength : ℕ}
    (E : ℕ → TapePred n) (N b : ℕ)
    (hstep : ∀ j, j < N → ∀ inp work out, E j inp work out →
      ∃ inp' work' out' t, 1 ≤ t ∧ t ≤ b ∧
        (loopTM tmBody tmTest).reachesIn t
          ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩
          ⟨(loopTM tmBody tmTest).qstart, inp', work', out'⟩ ∧
        E (j + 1) inp' work' out')
    (hstop : ∀ inp work out, E N inp work out →
      ∃ c' t, t ≤ b ∧ (loopTM tmBody tmTest).reachesIn t
        ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c' ∧
        (loopTM tmBody tmTest).halted c')
    (hparked : ∀ j, j ≤ N → ∀ inp work out, E j inp work out →
      (∀ i, (work i).head ≤ 1) ∧ inp.head ≤ inputLength + 1 ∧ out.head ≤ 1) :
    ∀ j, j ≤ N → ∀ inp work out, E j inp work out →
      ∀ c, (loopTM tmBody tmTest).reaches
        ⟨(loopTM tmBody tmTest).qstart, inp, work, out⟩ c →
        c.WithinDecisionSpace inputLength (1 + b) := by
  refine loopTM_keepsWindow_indexed tmBody tmTest E N b hstep hstop ?_
  intro j hjN inp work out hE c t ht hreach
  obtain ⟨hw, hi, ho⟩ := hparked j hjN inp work out hE
  obtain ⟨hbi, hbo, hbw⟩ :=
    head_le_start_add_of_reachesIn (loopTM tmBody tmTest) hreach
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · have h1 : (c.work i).head ≤ (work i).head + t := hbw i
    have h2 := hw i
    omega
  · have h1 : c.input.head ≤ inp.head + t := hbi
    omega
  · have h1 : c.output.head ≤ out.head + t := hbo
    omega


/-- Widening the window of a conditional window contract. Composing stages of different widths
means widening each to their maximum first. -/
theorem KeepsWindowOn.mono_space {tm : TM n} {pre : Cfg n tm.Q → Prop}
    {inputLength s s' : ℕ} (h : tm.KeepsWindowOn pre inputLength s) (hs : s ≤ s') :
    tm.KeepsWindowOn pre inputLength s' :=
  fun c hc c' hreach =>
    ⟨⟨fun i => le_trans ((h c hc c' hreach).1.1 i) hs,
      by have := (h c hc c' hreach).1.2; omega⟩,
      by have := (h c hc c' hreach).2; omega⟩

/-- The tape conditions a loop configuration must satisfy for the phase-based window rule: the
body and the test are entered on tapes their own window rules accept, and the bookkeeping phases
between them on tapes that carry those conditions along. -/
def LoopTapeInv (tmBody tmTest : TM n) (PB PT : TapePred n) (PL : LoopPhase → TapePred n)
    (c : Cfg n (loopTM tmBody tmTest).Q) : Prop :=
  (c.state = Sum.inl tmBody.qstart → PB c.input c.work c.output) ∧
  (c.state = Sum.inr (Sum.inr tmTest.qstart) → PT c.input c.work c.output) ∧
  (∀ ph, c.state = Sum.inr (Sum.inl ph) → ph = LoopPhase.done ∨ PL ph c.input c.work c.output)

/-- **A loop keeps a window, given windows for its phases.** `TM.loopTM_keepsWindow` asks each
phase to keep the window from *any* windowed configuration, which a phase that simulates another
machine cannot promise: started anywhere, such a machine need not even halt. This rule asks
instead for a window on the states each phase is actually entered at, plus three obligations
saying that the loop's own steps between phases carry those states along.

`PB` and `PT` describe the tapes the body and the test are entered with, `PL` those of the
rewind-and-check phases between them. -/
theorem loopTM_keepsWindowOn_phases (tmBody tmTest : TM n) {inputLength space : ℕ}
    (hs : 1 ≤ space) (PB PT : TapePred n) (PL : LoopPhase → TapePred n)
    (hbodyW : tmBody.KeepsWindowOn
      (fun d => d.state = tmBody.qstart ∧ PB d.input d.work d.output) inputLength space)
    (htestW : tmTest.KeepsWindowOn
      (fun d => d.state = tmTest.qstart ∧ PT d.input d.work d.output) inputLength space)
    (hBT : ∀ (c c' : Cfg n (loopTM tmBody tmTest).Q), c.state = Sum.inl tmBody.qhalt →
      (∃ d : Cfg n tmBody.Q, d.state = tmBody.qstart ∧ PB d.input d.work d.output ∧
        tmBody.reaches d ⟨tmBody.qhalt, c.input, c.work, c.output⟩) →
      (loopTM tmBody tmTest).step c = some c' → LoopTapeInv tmBody tmTest PB PT PL c')
    (hTL : ∀ (c c' : Cfg n (loopTM tmBody tmTest).Q),
      c.state = Sum.inr (Sum.inr tmTest.qhalt) →
      (∃ d : Cfg n tmTest.Q, d.state = tmTest.qstart ∧ PT d.input d.work d.output ∧
        tmTest.reaches d ⟨tmTest.qhalt, c.input, c.work, c.output⟩) →
      (loopTM tmBody tmTest).step c = some c' → LoopTapeInv tmBody tmTest PB PT PL c')
    (hLL : ∀ (c c' : Cfg n (loopTM tmBody tmTest).Q) (ph : LoopPhase),
      c.state = Sum.inr (Sum.inl ph) → PL ph c.input c.work c.output →
      (loopTM tmBody tmTest).step c = some c' → LoopTapeInv tmBody tmTest PB PT PL c') :
    ∀ (c₀ : Cfg n (loopTM tmBody tmTest).Q), c₀.state = (loopTM tmBody tmTest).qstart →
      PB c₀.input c₀.work c₀.output →
      c₀.WithinDecisionSpace inputLength space → CfgStartInvariant c₀ →
      ∀ c, (loopTM tmBody tmTest).reaches c₀ c →
        c.WithinDecisionSpace inputLength space := by
  intro c₀ hstart hPB0 hwin₀ hsi₀ cfin hreach
  set P : Cfg n (loopTM tmBody tmTest).Q → Prop := fun c =>
    c.WithinDecisionSpace inputLength space ∧ CfgStartInvariant c ∧
    (∀ q, c.state = Sum.inl q → ∃ d : Cfg n tmBody.Q, d.state = tmBody.qstart ∧
        PB d.input d.work d.output ∧
        tmBody.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ q, c.state = Sum.inr (Sum.inr q) → ∃ d : Cfg n tmTest.Q, d.state = tmTest.qstart ∧
        PT d.input d.work d.output ∧
        tmTest.reaches d ⟨q, c.input, c.work, c.output⟩) ∧
    (∀ ph, c.state = Sum.inr (Sum.inl ph) → ph = LoopPhase.done ∨
        PL ph c.input c.work c.output) with hPdef
  -- An idle step: the tape conditions come from the caller's obligation.
  have hidle : ∀ (c c' : Cfg n (loopTM tmBody tmTest).Q), P c →
      (∀ q, c.state = Sum.inl q → q = tmBody.qhalt) →
      (∀ q, c.state = Sum.inr (Sum.inr q) → q = tmTest.qhalt) →
      (loopTM tmBody tmTest).step c = some c' →
      LoopTapeInv tmBody tmTest PB PT PL c' → P c' := by
    rintro c c' ⟨hwin, hsi, -, -, -⟩ hb ht hst hinv
    obtain ⟨hi, hw, ho⟩ := loop_head_bound tmBody tmTest hb ht hst hsi.1 hsi.2.1 hsi.2.2
    have hwin' : c'.WithinDecisionSpace inputLength space := by
      refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
      · have := hw i; have := hwin.1.1 i; omega
      · have := hwin.1.2; omega
      · have := hwin.2; omega
    obtain ⟨hs1, hs2⟩ := loop_idle_step_state tmBody tmTest hb ht hst
    refine ⟨hwin', hsi.step hst, ?_, ?_, hinv.2.2⟩
    · intro q' hq'
      have hq0 : q' = tmBody.qstart := hs1 q' hq'
      subst hq0
      exact ⟨⟨tmBody.qstart, c'.input, c'.work, c'.output⟩, rfl, hinv.1 hq',
        Relation.ReflTransGen.refl⟩
    · intro q' hq'
      have hq0 : q' = tmTest.qstart := hs2 q' hq'
      subst hq0
      exact ⟨⟨tmTest.qstart, c'.input, c'.work, c'.output⟩, rfl, hinv.2.1 hq',
        Relation.ReflTransGen.refl⟩
  have hstepP : ∀ c c', P c → (loopTM tmBody tmTest).step c = some c' → P c' := by
    intro c c' hP hst
    obtain ⟨hwin, hsi, hp1, hp2, hp3⟩ := hP
    have hsi' : CfgStartInvariant c' := hsi.step hst
    rcases hstate : c.state with q | ph | q
    · by_cases hq : q = tmBody.qhalt
      · subst hq
        refine hidle c c' ⟨hwin, hsi, hp1, hp2, hp3⟩ ?_ ?_ hst
          (hBT c c' hstate (hp1 _ hstate) hst)
        · intro q' hq'
          rw [hstate] at hq'
          exact (Sum.inl.injEq _ _ ▸ hq').symm
        · intro q' hq'
          rw [hstate] at hq'
          exact absurd hq' (by nofun)
      · obtain ⟨d, hd0, hd1, hd3⟩ := hp1 q hstate
        have hc : c = loopBodyWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tmBody.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
        have hsim := loopTM_body_step tmBody tmTest hstep0
        rw [hc] at hst
        have hc'eq : c' = loopBodyWrap tmBody tmTest e' :=
          Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tmBody.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
        subst hc'eq
        exact ⟨hbodyW d ⟨hd0, hd1⟩ e' hre, hsi',
          fun q' hq' => ⟨d, hd0, hd1, by
            rw [show (⟨q', (loopBodyWrap tmBody tmTest e').input,
              (loopBodyWrap tmBody tmTest e').work,
              (loopBodyWrap tmBody tmTest e').output⟩ : Cfg n tmBody.Q) = e' from
              Cfg.ext (by injection hq'.symm) rfl rfl rfl]
            exact hre⟩,
          fun _ hq' => absurd hq' (by nofun),
          fun _ hph' => absurd hph' (by nofun)⟩
    · have hb : ∀ q', c.state = Sum.inl q' → q' = tmBody.qhalt := by
        intro q' hq'
        rw [hstate] at hq'
        exact absurd hq' (by nofun)
      have ht : ∀ q', c.state = Sum.inr (Sum.inr q') → q' = tmTest.qhalt := by
        intro q' hq'
        rw [hstate] at hq'
        exact absurd hq' (by nofun)
      have hPLc : PL ph c.input c.work c.output := by
        rcases hp3 ph hstate with hdone | hPL
        · subst hdone
          exact absurd hst (by
            simp only [TM.step, show c.state = (loopTM tmBody tmTest).qhalt from hstate,
              ↓reduceIte]
            nofun)
        · exact hPL
      exact hidle c c' ⟨hwin, hsi, hp1, hp2, hp3⟩ hb ht hst (hLL c c' ph hstate hPLc hst)
    · by_cases hq : q = tmTest.qhalt
      · subst hq
        refine hidle c c' ⟨hwin, hsi, hp1, hp2, hp3⟩ ?_ ?_ hst
          (hTL c c' hstate (hp2 _ hstate) hst)
        · intro q' hq'
          rw [hstate] at hq'
          exact absurd hq' (by nofun)
        · intro q' hq'
          rw [hstate] at hq'
          exact (Sum.inr.injEq _ _ ▸ (Sum.inr.injEq _ _ ▸ hq')).symm
      · obtain ⟨d, hd0, hd1, hd3⟩ := hp2 q hstate
        have hc : c = loopTestWrap tmBody tmTest ⟨q, c.input, c.work, c.output⟩ :=
          Cfg.ext hstate rfl rfl rfl
        obtain ⟨e', hstep0⟩ :
            ∃ e', tmTest.step ⟨q, c.input, c.work, c.output⟩ = some e' := by
          rw [TM.step, ite_eq_right hq]; exact ⟨_, rfl⟩
        have hsim := loopTM_test_step tmBody tmTest hstep0
        rw [hc] at hst
        have hc'eq : c' = loopTestWrap tmBody tmTest e' :=
          Option.some_inj.mp (hst.symm.trans hsim)
        have hre : tmTest.reaches d e' := Relation.ReflTransGen.tail hd3 hstep0
        subst hc'eq
        exact ⟨htestW d ⟨hd0, hd1⟩ e' hre, hsi',
          fun _ hq' => absurd hq' (by nofun),
          fun q' hq' => ⟨d, hd0, hd1, by
            rw [show (⟨q', (loopTestWrap tmBody tmTest e').input,
              (loopTestWrap tmBody tmTest e').work,
              (loopTestWrap tmBody tmTest e').output⟩ : Cfg n tmTest.Q) = e' from
              Cfg.ext (by injection hq'.symm with h; injection h) rfl rfl rfl]
            exact hre⟩,
          fun _ hph' => absurd hph' (by nofun)⟩
  have hinit : P c₀ := by
    refine ⟨hwin₀, hsi₀, ?_, ?_, ?_⟩
    · intro q hq
      have hqs : q = tmBody.qstart := by
        have h := hstart.symm.trans hq
        exact (Sum.inl.injEq _ _ ▸ h).symm
      subst hqs
      exact ⟨_, rfl, hPB0, Relation.ReflTransGen.refl⟩
    · intro q hq
      rw [hstart] at hq
      exact absurd hq (by nofun)
    · intro ph hph
      rw [hstart] at hph
      exact absurd hph (by nofun)
  have key : ∀ c, (loopTM tmBody tmTest).reaches c₀ c → P c := by
    intro c h
    induction h with
    | refl => exact hinit
    | tail _ hs ih => exact hstepP _ _ ih hs
  exact (key cfin hreach).1


/-- **A bookkeeping step of a loop moves only the output head.** Between the test and the next
iteration the loop rewinds its output tape and reads one cell; the work tapes and the input are
idled, and the output's contents are written back unchanged. -/
theorem loop_phase_step_tapes (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    {ph : LoopPhase} (hstate : c.state = Sum.inr (Sum.inl ph)) (hph : ph ≠ LoopPhase.done)
    (hout : Tape.StartInvariant c.output)
    (hstep : (loopTM tmBody tmTest).step c = some c') :
    c'.input = transitionInput c.input ∧
    (∀ i, c'.work i = transitionTape (c.work i)) ∧
    c'.output.cells = c.output.cells ∧ c'.output.head ≤ max c.output.head 1 := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]
    intro hcon
    exact hph (by injection hcon with h; injection h)
  rw [TM.step, ite_eq_right hne] at hstep
  rw [← Option.some_inj.mp hstep, hstate]
  have hcells : ∀ (d : Dir3), d ≠ Dir3.right → c.output.read ≠ Γ.start →
      (c.output.writeAndMove (readBackWrite c.output.read).toΓ d).cells = c.output.cells ∧
      (c.output.writeAndMove (readBackWrite c.output.read).toΓ d).head
        ≤ max c.output.head 1 := by
    intro d hd hread
    have hw : c.output.write (readBackWrite c.output.read).toΓ = c.output :=
      write_readBack c.output hread
    show ((c.output.write (readBackWrite c.output.read).toΓ).move d).cells = _ ∧
      ((c.output.write (readBackWrite c.output.read).toΓ).move d).head ≤ _
    rw [hw, Tape.move_cells]
    refine ⟨rfl, ?_⟩
    cases d
    · show (c.output.head - 1) ≤ _
      omega
    · exact absurd rfl hd
    · show c.output.head ≤ _
      omega
  have hstart : c.output.read = Γ.start → c.output.head = 0 := by
    intro hread
    by_contra hc0
    exact absurd hread (hout.2 c.output.head (by omega))
  cases ph with
  | done => exact absurd rfl hph
  | rewindOut =>
      simp only [loopTM]
      by_cases hread : c.output.read = Γ.start
      · rw [ite_eq_left hread]
        refine ⟨rfl, fun i => rfl, ?_, ?_⟩
        · show ((c.output.write Γw.blank.toΓ).move Dir3.right).cells = _
          rw [Tape.move_cells, Tape.write, ite_eq_left (hstart hread)]
        · show ((c.output.write Γw.blank.toΓ).move Dir3.right).head ≤ _
          show (c.output.write Γw.blank.toΓ).head + 1 ≤ _
          rw [Tape.write_head, hstart hread]
          omega
      · rw [ite_eq_right hread]
        exact ⟨rfl, fun i => rfl, (hcells Dir3.left (by nofun) hread).1,
          (hcells Dir3.left (by nofun) hread).2⟩
  | check =>
      simp only [loopTM]
      by_cases hone : c.output.read = Γ.one
      · rw [ite_eq_left hone]
        have hread : c.output.read ≠ Γ.start := by rw [hone]; nofun
        have hd : idleDir c.output.read ≠ Dir3.right := by
          rw [idleDir, ite_eq_right hread]
          nofun
        exact ⟨rfl, fun i => rfl, (hcells (idleDir c.output.read) hd hread).1,
          (hcells (idleDir c.output.read) hd hread).2⟩
      · rw [ite_eq_right hone]
        by_cases hread : c.output.read = Γ.start
        · refine ⟨rfl, fun i => rfl, ?_, ?_⟩
          · show ((c.output.write (readBackWrite c.output.read).toΓ).move
              (idleDir c.output.read)).cells = _
            rw [Tape.move_cells, Tape.write, ite_eq_left (hstart hread)]
          · show ((c.output.write (readBackWrite c.output.read).toΓ).move
              (idleDir c.output.read)).head ≤ _
            rw [idleDir, ite_eq_left hread]
            show (c.output.write (readBackWrite c.output.read).toΓ).head + 1 ≤ _
            rw [Tape.write_head, hstart hread]
            omega
        · have hd : idleDir c.output.read ≠ Dir3.right := by
            rw [idleDir, ite_eq_right hread]
            nofun
          exact ⟨rfl, fun i => rfl, (hcells (idleDir c.output.read) hd hread).1,
            (hcells (idleDir c.output.read) hd hread).2⟩

/-- **Where a rewind step goes.** It keeps rewinding until the output head reads the marker, and
then moves on to the check. -/
theorem loop_rewind_step_state (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hstep : (loopTM tmBody tmTest).step c = some c') :
    (c.output.read = Γ.start → c'.state = Sum.inr (Sum.inl LoopPhase.check) ∧
      c'.output.head = c.output.head + 1) ∧
    (c.output.read ≠ Γ.start → c'.state = Sum.inr (Sum.inl LoopPhase.rewindOut)) := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]
    nofun
  rw [TM.step, ite_eq_right hne] at hstep
  rw [← Option.some_inj.mp hstep, hstate]
  simp only [loopTM]
  constructor
  · intro hread
    rw [ite_eq_left hread]
    refine ⟨rfl, ?_⟩
    show ((c.output.write Γw.blank.toΓ).move Dir3.right).head = _
    show (c.output.write Γw.blank.toΓ).head + 1 = _
    rw [Tape.write_head]
  · intro hread
    rw [ite_eq_right hread]

/-- **A check step leaves every tape exactly as it found it**, when the output head is off the
marker — which it is, since the rewind has just put it at cell one. -/
theorem loop_check_step_tapes (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.check)) (hread : c.output.read ≠ Γ.start)
    (hstep : (loopTM tmBody tmTest).step c = some c') :
    c'.input = transitionInput c.input ∧ (∀ i, c'.work i = transitionTape (c.work i)) ∧
    c'.output = c.output := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]
    nofun
  rw [TM.step, ite_eq_right hne] at hstep
  rw [← Option.some_inj.mp hstep, hstate]
  simp only [loopTM]
  have hout : c.output.writeAndMove (readBackWrite c.output.read).toΓ
      (idleDir c.output.read) = c.output := by
    rw [idleDir, ite_eq_right hread]
    show (c.output.write (readBackWrite c.output.read).toΓ).move Dir3.stay = c.output
    rw [write_readBack c.output hread]
    rfl
  split
  · exact ⟨rfl, fun i => rfl, hout⟩
  · exact ⟨rfl, fun i => rfl, hout⟩

end TM

end Complexity
