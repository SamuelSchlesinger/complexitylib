/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Complement
public import Complexitylib.Models.TuringMachine.Combinators.Internal.IdleHeads
public import Complexitylib.Models.TuringMachine.Frame
public import Complexitylib.Classes.P.Defs

/-!
# `PSPACE` is closed under complement

⚠️ Unreviewed by Bolton

`TM.complementTM` already flips a decider's verdict, and `TM.complementTM_decidesInTime` accounts
for its time. The space account is what `PH ⊆ PSPACE` needs, and it is not immediate: the space
predicate constrains *every reachable configuration*, so it is not enough to know where the
machine ends up — one has to know that no configuration along the way strays outside the window.

The complement machine has three phases. In the first it simulates the source machine, so every
configuration it meets is an embedded reachable configuration of that machine and inherits its
bound. In the other two it idles every tape except the output, whose head it walks left to the
marker and then one cell right. The one lemma that makes the accounting work is that an *idle*
move on a tape carrying its left marker sends the head to `max head 1` — it bounces off cell `0`
and otherwise stands still — so no head can drift outward however long the rewind takes. One
extra cell therefore covers the whole construction.

The head-bounce lemmas it uses are shared with the loop combinator and live in
`Complexitylib.Models.TuringMachine.Combinators.Internal.IdleHeads`.

## Main definitions

- `TM.CompInv` — the invariant carried along a run of the complement machine

## Main results

- `TM.complement_head_bound` — after the simulation, no head passes `max head 1`
- `TM.complementTM_withinDecisionSpace` — every reachable configuration stays in the window
- `TM.complementTM_decidesInSpace` — the complement is decided in space `S + 1`
- `DSPACE_compl` — a space class with room for one more cell is closed under complement
- `PSPACE_compl` — **`PSPACE` is closed under complement**
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **After the simulation, the complement machine never grows a head beyond `max head 1`.**
Every phase idles the input and work tapes, and moves the output head right only when it is
sitting on the left marker. -/
theorem complement_head_bound (tm : TM n) {c c' : Cfg n tm.complementTM.Q}
    (hnotsim : ∀ q, c.state = Sum.inl q → q = tm.qhalt)
    (hstep : tm.complementTM.step c = some c')
    (hinp : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.head ≤ max c.input.head 1 ∧
    (∀ i, (c'.work i).head ≤ max (c.work i).head 1) ∧
    c'.output.head ≤ max c.output.head 1 := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rcases hstate : c.state with q | ph
  · have hq : q = tm.qhalt := hnotsim q hstate
    subst hq
    refine ⟨?_, fun i => ?_, ?_⟩ <;>
      simp only [complementTM, ↓reduceIte]
    · exact head_move_idleDir_le_max hinp
    · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
    · exact head_writeAndMove_idleDir_le_max _ _ hout
  · cases ph with
    | rewind =>
        refine ⟨?_, fun i => ?_, ?_⟩ <;>
          simp only [complementTM]
        · split <;> exact head_move_idleDir_le_max hinp
        · split <;> exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
        · split
          · rename_i hread
            refine head_writeAndMove_le_max _ _ _ fun _ => ?_
            by_contra hh
            exact (hout.2 c.output.head (by omega)) hread
          · exact head_writeAndMove_le_max _ _ _ (by nofun)
    | flip =>
        refine ⟨?_, fun i => ?_, ?_⟩ <;>
          simp only [complementTM]
        · exact head_move_idleDir_le_max hinp
        · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
        · exact head_writeAndMove_idleDir_le_max _ _ hout
    | done => exact absurd hstate hne

/-- After the simulation phase the machine never returns to it. -/
theorem complement_state_of_step (tm : TM n) {c c' : Cfg n tm.complementTM.Q}
    (hnotsim : ∀ q, c.state = Sum.inl q → q = tm.qhalt)
    (hstep : tm.complementTM.step c = some c') :
    ∃ ph, c'.state = Sum.inr ph := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rcases hstate : c.state with q | ph
  · have hq : q = tm.qhalt := hnotsim q hstate
    subst hq
    exact ⟨ComplementPhase.rewind, by simp only [complementTM, ↓reduceIte]⟩
  · cases ph with
    | rewind =>
        by_cases hread : c.output.read = Γ.start
        · exact ⟨ComplementPhase.flip, by simp only [complementTM, hread, ↓reduceIte]⟩
        · exact ⟨ComplementPhase.rewind, by simp only [complementTM, hread, ↓reduceIte]⟩
    | flip => exact ⟨ComplementPhase.done, by simp only [complementTM]⟩
    | done => exact absurd hstate hne

/-- The invariant carried along a run of the complement machine: every tape keeps its left
marker, the simulation phase only ever holds an embedded reachable configuration of the source
machine, and every later phase respects the space bound with one cell to spare. -/
def CompInv (tm : TM n) (x : List Bool) (s : ℕ) (c : Cfg n tm.complementTM.Q) : Prop :=
  c.input.StartInvariant ∧ (∀ i, (c.work i).StartInvariant) ∧ c.output.StartInvariant ∧
  (∀ q, c.state = Sum.inl q → ∃ c₀, tm.reaches (tm.initCfg x) c₀ ∧ c = complementCfg tm c₀) ∧
  (∀ ph, c.state = Sum.inr ph → c.WithinDecisionSpace x.length (s + 1))

/-- **The invariant is preserved by a step.** -/
theorem CompInv.step {tm : TM n} {L : Language} {S : ℕ → ℕ} (hdec : tm.DecidesInSpace L S)
    (x : List Bool) {c c' : Cfg n tm.complementTM.Q}
    (hinv : CompInv tm x (S x.length) c)
    (hstep : tm.complementTM.step c = some c') :
    CompInv tm x (S x.length) c' := by
  obtain ⟨hinp, hwork, hout, hsim, hspace⟩ := hinv
  obtain ⟨hinp', hwork', hout'⟩ := Tape.StartInvariant.step tm.complementTM hstep hinp hwork hout
  by_cases hnotsim : ∀ q, c.state = Sum.inl q → q = tm.qhalt
  · obtain ⟨hi, hw, ho⟩ := complement_head_bound tm hnotsim hstep hinp hwork hout
    obtain ⟨ph', hph'⟩ := complement_state_of_step tm hnotsim hstep
    have hc : c.WithinDecisionSpace x.length (S x.length + 1) := by
      rcases hstate : c.state with q | ph
      · obtain ⟨c₀, hreach, rfl⟩ := hsim q hstate
        have h := hdec.1 x c₀ hreach
        refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
        · show (c₀.work i).head ≤ _
          have := h.1.1 i
          omega
        · show c₀.input.head ≤ _
          have := h.1.2
          omega
        · show c₀.output.head ≤ _
          have := h.2
          omega
      · exact hspace ph hstate
    refine ⟨hinp', hwork', hout', ?_, ?_⟩
    · intro q hq
      rw [hph'] at hq
      exact absurd hq (by nofun)
    · intro _ _
      refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
      · have h₁ := hw i
        have h₂ := hc.1.1 i
        omega
      · have h₂ := hc.1.2
        omega
      · have h₂ := hc.2
        omega
  · push Not at hnotsim
    obtain ⟨q, hstate, hq⟩ := hnotsim
    obtain ⟨c₀, hreach, rfl⟩ := hsim q hstate
    have hqc : q = c₀.state := (Sum.inl.injEq _ _ ▸ hstate).symm
    have hq0 : c₀.state ≠ tm.qhalt := by rw [← hqc]; exact hq
    obtain ⟨c₀', hstep0⟩ : ∃ c₀', tm.step c₀ = some c₀' := by
      rw [TM.step, ite_eq_right hq0]; exact ⟨_, rfl⟩
    have hsimstep : tm.complementTM.step (complementCfg tm c₀) = some (complementCfg tm c₀') := by
      have h := complementTM_simulation tm (TM.reachesIn.step hstep0 TM.reachesIn.zero)
      cases h with
      | step h₁ h₂ => cases h₂; exact h₁
    have hc'eq : c' = complementCfg tm c₀' :=
      Option.some_inj.mp (hstep.symm.trans hsimstep)
    subst hc'eq
    refine ⟨hinp', hwork', hout', ?_, ?_⟩
    · intro _ _
      exact ⟨c₀', Relation.ReflTransGen.tail hreach hstep0, rfl⟩
    · intro ph hph
      exact absurd hph (by nofun)

/-- The invariant holds at the start of the run. -/
theorem CompInv.init (tm : TM n) (x : List Bool) (s : ℕ) :
    CompInv tm x s (tm.complementTM.initCfg x) := by
  refine ⟨startInvariant_initOfBool x, fun _ => startInvariant_initNil,
    startInvariant_initNil, ?_, ?_⟩
  · intro _ _
    exact ⟨tm.initCfg x, Relation.ReflTransGen.refl, (compCfg_initCfg tm x).symm⟩
  · intro _ hph
    exact absurd hph (by nofun)

/-- The invariant holds at every reachable configuration. -/
theorem CompInv.reaches {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c : Cfg n tm.complementTM.Q}
    (h : tm.complementTM.reaches (tm.complementTM.initCfg x) c) :
    CompInv tm x (S x.length) c := by
  induction h with
  | refl => exact CompInv.init tm x (S x.length)
  | tail _ hstep ih => exact ih.step hdec x hstep

/-- **The complement machine respects the space bound with one cell to spare.** -/
theorem complementTM_withinDecisionSpace {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) (x : List Bool) {c : Cfg n tm.complementTM.Q}
    (h : tm.complementTM.reaches (tm.complementTM.initCfg x) c) :
    c.WithinDecisionSpace x.length (S x.length + 1) := by
  obtain ⟨-, -, -, hsim, hspace⟩ := CompInv.reaches hdec x h
  rcases hstate : c.state with q | ph
  · obtain ⟨c₀, hreach, rfl⟩ := hsim q hstate
    have hb := hdec.1 x c₀ hreach
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · show (c₀.work i).head ≤ _
      have := hb.1.1 i
      omega
    · show c₀.input.head ≤ _
      have := hb.1.2
      omega
    · show c₀.output.head ≤ _
      have := hb.2
      omega
  · exact hspace ph hstate

/-- **The complement machine decides the complement, in one more cell of space.** -/
theorem complementTM_decidesInSpace {tm : TM n} {L : Language} {S : ℕ → ℕ}
    (hdec : tm.DecidesInSpace L S) :
    tm.complementTM.DecidesInSpace Lᶜ (fun m => S m + 1) := by
  refine ⟨fun x c' h => complementTM_withinDecisionSpace hdec x h, fun x => ?_⟩
  obtain ⟨c', hreach, hhalt, hyes, hno⟩ := hdec.2 x
  obtain ⟨t, hreachIn⟩ := TM.reaches_to_reachesIn tm hreach
  have hsim := complementTM_simulation tm hreachIn
  rw [compCfg_initCfg] at hsim
  have hcell0 := output_cells_zero_eq_start_of_reachesIn hreachIn (by simp [Tape.init])
  have hnostart := output_cells_ne_start_of_reachesIn hreachIn (by
    intro i hi; simp [Tape.init]; omega)
  obtain ⟨c_done, t_rw, hreach_rw, hhalt_done, hflip, -⟩ :=
    complementTM_rewind_and_flip tm c' hhalt hcell0 hnostart
  have htotal := reachesIn_trans tm.complementTM hsim hreach_rw
  refine ⟨c_done, ?_, hhalt_done, ?_, ?_⟩
  · exact TM.reachesIn.rec Relation.ReflTransGen.refl
      (fun hs _ ih => Relation.ReflTransGen.head hs ih) htotal
  · intro hxc
    rw [hflip, hno hxc]
    simp [flipBit]
  · intro hxc
    simp only [Set.mem_compl_iff, not_not] at hxc
    rw [hflip, hyes hxc]
    simp [flipBit]

end TM

/-- **A space class with room for one more cell is closed under complement.** The one extra cell
is what the rewind to the verdict cell costs. -/
theorem DSPACE_compl {L : Language} {S : ℕ → ℕ} (hone : (fun _ => 1) =O S)
    (h : L ∈ DSPACE S) : Lᶜ ∈ DSPACE S := by
  obtain ⟨m, tm, f, hdec, hf⟩ := h
  exact ⟨m, tm.complementTM, fun j => f j + 1,
    TM.complementTM_decidesInSpace hdec, BigO.add hf hone⟩

/-- **`PSPACE` is closed under complement.** The same machine runs, then rewinds its output head
to the verdict cell and flips the bit; the rewind only moves heads leftward or off the left
marker, so it costs one extra cell of space and no more. -/
theorem PSPACE_compl {L : Language} (h : L ∈ PSPACE) : Lᶜ ∈ PSPACE := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
  exact Set.mem_iUnion.mpr ⟨k, DSPACE_compl (BigO.const_le_pow 1 k) hk⟩

end Complexity
