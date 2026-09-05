/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Subroutines.ParkAll
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Loop
public import Complexitylib.Models.TuringMachine.Combinators.Internal.Seq
public import Complexitylib.Models.TuringMachine.Combinators.Internal.If

/-!
# Heads that idle never drift outward

Space accounting for the phase machinery of the combinators rests on one fact. Between phases,
and throughout the rewind and check phases, every tape is moved by `idleDir` — and on a tape
carrying its left marker that sends the head to exactly `max head 1`: it bounces off cell `0`
and otherwise stands still. So however many steps a rewind takes, no head drifts outward, and a
space bound established before the phase survives it with no additive slack.

The output tape is the exception: it is walked left to the marker and then one cell right, which
is still within `max head 1`.

## Main results

- `TM.head_writeAndMove_idleDir_le_max` — an idle write-and-move stays within `max head 1`
- `TM.seq_head_bound` — the step `seqTM` interposes between its two simulations idles every tape
- `TM.loop_head_bound` — every phase of `loopTM` outside the two simulations keeps every head
  within `max head 1`
- `TM.if_head_bound` — the same for `ifTM`
- `TM.loop_idle_step_state`, `TM.if_idle_step_state` — an interposed step lands only at
  another interposed phase or at a start state
- `TM.loopTM_rewind_loop_frame` — the rewind phase of `loopTM` leaves the input and work
  tapes identical, heads included
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- A head that only ever moves right off the left marker stays within `max head 1`. -/
theorem head_move_le_max (t : Tape) (d : Dir3) (hd : d = Dir3.right → t.head = 0) :
    (t.move d).head ≤ max t.head 1 := by
  cases d
  · show t.head - 1 ≤ _
    omega
  · show t.head + 1 ≤ _
    rw [hd rfl]
    omega
  · show t.head ≤ _
    omega

/-- The same for a write followed by a move: writing does not move the head. -/
theorem head_writeAndMove_le_max (t : Tape) (w : Γw) (d : Dir3)
    (hd : d = Dir3.right → t.head = 0) :
    (t.writeAndMove w d).head ≤ max t.head 1 := by
  show ((t.write w.toΓ).move d).head ≤ _
  have h : (t.write w.toΓ).head = t.head := Tape.write_head _ _
  have := head_move_le_max (t.write w.toΓ) d (by rw [h]; exact hd)
  rw [h] at this
  exact this

/-- An idle move never leaves `max head 1`. -/
theorem head_move_idleDir_le_max {t : Tape} (h : t.StartInvariant) :
    (t.move (idleDir t.read)).head ≤ max t.head 1 := by
  rw [move_idleDir_eq_of_startInvariant h]

/-- An idle write-and-move never leaves `max head 1`. -/
theorem head_writeAndMove_idleDir_le_max (t : Tape) (w : Γw) (h : t.StartInvariant) :
    (t.writeAndMove w (idleDir t.read)).head ≤ max t.head 1 := by
  refine head_writeAndMove_le_max t w _ fun hd => ?_
  by_contra hne
  exact absurd hd (by rw [idleDir, ite_eq_right (h.read_ne_start (by omega))]; nofun)

/-- **The single step `seqTM` interposes between its two simulations idles every tape.** -/
theorem seq_head_bound (tm₁ tm₂ : TM n) {c c' : Cfg n (seqTM tm₁ tm₂).Q}
    (hstate : c.state = Sum.inl tm₁.qhalt)
    (hstep : (seqTM tm₁ tm₂).step c = some c')
    (hinp : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.head ≤ max c.input.head 1 ∧
    (∀ i, (c'.work i).head ≤ max (c.work i).head 1) ∧
    c'.output.head ≤ max c.output.head 1 := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [seqTM, hstate, ↓reduceIte]
  · exact head_move_idleDir_le_max hinp
  · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
  · exact head_writeAndMove_idleDir_le_max _ _ hout

/-- **Outside its two simulation phases, `loopTM` never grows a head beyond `max head 1`.**
The phase transitions and the rewind and check phases all idle the input and work tapes, and
move the output head right only off the left marker. -/
theorem loop_head_bound (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    (hbody : ∀ q, c.state = Sum.inl q → q = tmBody.qhalt)
    (htest : ∀ q, c.state = Sum.inr (Sum.inr q) → q = tmTest.qhalt)
    (hstep : (loopTM tmBody tmTest).step c = some c')
    (hinp : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.head ≤ max c.input.head 1 ∧
    (∀ i, (c'.work i).head ≤ max (c.work i).head 1) ∧
    c'.output.head ≤ max c.output.head 1 := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rcases hstate : c.state with q | phq
  · have hq : q = tmBody.qhalt := hbody q hstate
    subst hq
    refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [loopTM, ↓reduceIte]
    · exact head_move_idleDir_le_max hinp
    · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
    · exact head_writeAndMove_idleDir_le_max _ _ hout
  · rcases phq with ph | q
    · cases ph with
      | rewindOut =>
          refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [loopTM]
          · split <;> exact head_move_idleDir_le_max hinp
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
          · split
            · rename_i hread
              refine head_writeAndMove_le_max _ _ _ fun _ => ?_
              by_contra hh
              exact (hout.2 c.output.head (by omega)) hread
            · exact head_writeAndMove_le_max _ _ _ (by nofun)
      | check =>
          refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [loopTM]
          · split <;> exact head_move_idleDir_le_max hinp
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ hout
      | done => exact absurd hstate hne
    · have hq : q = tmTest.qhalt := htest q hstate
      subst hq
      refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [loopTM, ↓reduceIte]
      · exact head_move_idleDir_le_max hinp
      · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
      · exact head_writeAndMove_idleDir_le_max _ _ hout

/-- **Outside its three simulation phases, `ifTM` never grows a head beyond `max head 1`.** -/
theorem if_head_bound (tmTest tmThen tmElse : TM n)
    {c c' : Cfg n (ifTM tmTest tmThen tmElse).Q}
    (ht : ∀ q, c.state = Sum.inl q → q = tmTest.qhalt)
    (hthen : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inl q)) → q = tmThen.qhalt)
    (helse : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inr q)) → q = tmElse.qhalt)
    (hstep : (ifTM tmTest tmThen tmElse).step c = some c')
    (hinp : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.head ≤ max c.input.head 1 ∧
    (∀ i, (c'.work i).head ≤ max (c.work i).head 1) ∧
    c'.output.head ≤ max c.output.head 1 := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rcases hstate : c.state with q | phq
  · have hq : q = tmTest.qhalt := ht q hstate
    subst hq
    refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [ifTM, ↓reduceIte]
    · exact head_move_idleDir_le_max hinp
    · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
    · exact head_writeAndMove_idleDir_le_max _ _ hout
  · rcases phq with ph | bq
    · cases ph with
      | rewindOut =>
          refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [ifTM]
          · split <;> exact head_move_idleDir_le_max hinp
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
          · split
            · rename_i hread
              refine head_writeAndMove_le_max _ _ _ fun _ => ?_
              by_contra hh
              exact (hout.2 c.output.head (by omega)) hread
            · exact head_writeAndMove_le_max _ _ _ (by nofun)
      | check =>
          refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [ifTM]
          · split <;> exact head_move_idleDir_le_max hinp
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
          · split <;> exact head_writeAndMove_idleDir_le_max _ _ hout
      | done => exact absurd hstate hne
    · rcases bq with q | q
      · have hq : q = tmThen.qhalt := hthen q hstate
        subst hq
        refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [ifTM, ↓reduceIte]
        · exact head_move_idleDir_le_max hinp
        · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
        · exact head_writeAndMove_idleDir_le_max _ _ hout
      · have hq : q = tmElse.qhalt := helse q hstate
        subst hq
        refine ⟨?_, fun i => ?_, ?_⟩ <;> simp only [ifTM, ↓reduceIte]
        · exact head_move_idleDir_le_max hinp
        · exact head_writeAndMove_idleDir_le_max _ _ (hwork i)
        · exact head_writeAndMove_idleDir_le_max _ _ hout

/-- **Outside its three simulations, `ifTM` steps only to an interposed phase or to a branch's
start state.** -/
theorem if_idle_step_state (tmTest tmThen tmElse : TM n)
    {c c' : Cfg n (ifTM tmTest tmThen tmElse).Q}
    (ht : ∀ q, c.state = Sum.inl q → q = tmTest.qhalt)
    (hthen : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inl q)) → q = tmThen.qhalt)
    (helse : ∀ q, c.state = Sum.inr (Sum.inr (Sum.inr q)) → q = tmElse.qhalt)
    (hstep : (ifTM tmTest tmThen tmElse).step c = some c') :
    (∃ ph, c'.state = Sum.inr (Sum.inl ph)) ∨
      c'.state = Sum.inr (Sum.inr (Sum.inl tmThen.qstart)) ∨
      c'.state = Sum.inr (Sum.inr (Sum.inr tmElse.qstart)) := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rcases hstate : c.state with q | phq
  · have hq : q = tmTest.qhalt := ht q hstate
    subst hq
    exact Or.inl ⟨IfPhase.rewindOut, by simp only [ifTM, ↓reduceIte]⟩
  · rcases phq with ph | bq
    · cases ph with
      | rewindOut =>
          by_cases hread : c.output.read = Γ.start
          · exact Or.inl ⟨IfPhase.check, by simp only [ifTM, hread, ↓reduceIte]⟩
          · exact Or.inl ⟨IfPhase.rewindOut, by simp only [ifTM, hread, ↓reduceIte]⟩
      | check =>
          by_cases hread : c.output.read = Γ.one
          · exact Or.inr (Or.inl (by simp only [ifTM, hread, ↓reduceIte]))
          · exact Or.inr (Or.inr (by simp only [ifTM, hread, ↓reduceIte]))
      | done => exact absurd hstate hne
    · rcases bq with q | q
      · have hq : q = tmThen.qhalt := hthen q hstate
        subst hq
        exact Or.inl ⟨IfPhase.done, by simp only [ifTM, ↓reduceIte]⟩
      · have hq : q = tmElse.qhalt := helse q hstate
        subst hq
        exact Or.inl ⟨IfPhase.done, by simp only [ifTM, ↓reduceIte]⟩

/-- From one of the interposed phases, `loopTM` moves either to another such phase or back to the
body's start state. -/
theorem loop_phase_step_state (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    {ph : LoopPhase} (hstate : c.state = Sum.inr (Sum.inl ph))
    (hstep : (loopTM tmBody tmTest).step c = some c') :
    (∃ ph', c'.state = Sum.inr (Sum.inl ph')) ∨ c'.state = Sum.inl tmBody.qstart := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  cases ph with
  | rewindOut =>
      by_cases hread : c.output.read = Γ.start
      · exact Or.inl ⟨LoopPhase.check, by simp only [loopTM, hstate, hread, ↓reduceIte]⟩
      · exact Or.inl ⟨LoopPhase.rewindOut, by simp only [loopTM, hstate, hread, ↓reduceIte]⟩
  | check =>
      by_cases hread : c.output.read = Γ.one
      · exact Or.inl ⟨LoopPhase.done, by simp only [loopTM, hstate, hread, ↓reduceIte]⟩
      · exact Or.inr (by simp only [loopTM, hstate, hread, ↓reduceIte])
  | done => exact absurd hstate hne

/-- **An interposed step lands at a start state or at another interposed phase.** So the only way
back into the body or the test is through their start states — which is what lets a loop invariant
be re-established once per iteration. -/
theorem loop_idle_step_state (tmBody tmTest : TM n) {c c' : Cfg n (loopTM tmBody tmTest).Q}
    (hb : ∀ q, c.state = Sum.inl q → q = tmBody.qhalt)
    (ht : ∀ q, c.state = Sum.inr (Sum.inr q) → q = tmTest.qhalt)
    (hstep : (loopTM tmBody tmTest).step c = some c') :
    (∀ q, c'.state = Sum.inl q → q = tmBody.qstart) ∧
    (∀ q, c'.state = Sum.inr (Sum.inr q) → q = tmTest.qstart) := by
  have hne := state_ne_qhalt_of_step hstep
  rcases hstate : c.state with q | phq
  · have hq : q = tmBody.qhalt := hb q hstate
    subst hq
    have hc : c = loopBodyWrap tmBody tmTest ⟨tmBody.qhalt, c.input, c.work, c.output⟩ :=
      Cfg.ext hstate rfl rfl rfl
    rw [hc, loopTM_body_to_test tmBody tmTest rfl] at hstep
    rw [← Option.some_inj.mp hstep]
    exact ⟨fun _ h => absurd h (by nofun), fun _ h => by injection h.symm with h'; injection h'⟩
  · rcases phq with ph | q
    · rcases loop_phase_step_state tmBody tmTest hstate hstep with ⟨ph', hph'⟩ | hqs
      · exact ⟨fun _ h => absurd (h.symm.trans hph') (by nofun),
          fun _ h => absurd (h.symm.trans hph') (by nofun)⟩
      · exact ⟨fun _ h => by injection h.symm.trans hqs,
          fun _ h => absurd (h.symm.trans hqs) (by nofun)⟩
    · have hq : q = tmTest.qhalt := ht q hstate
      subst hq
      have hc : c = loopTestWrap tmBody tmTest ⟨tmTest.qhalt, c.input, c.work, c.output⟩ :=
        Cfg.ext hstate rfl rfl rfl
      rw [hc, loopTM_test_to_rewind tmBody tmTest rfl] at hstep
      rw [← Option.some_inj.mp hstep]
      exact ⟨fun _ h => absurd h (by nofun), fun _ h => by injection h.symm with h'; injection h'⟩

/-! ## The rewind phase leaves the input and work tapes alone -/

/-- One leftward rewind step of `loopTM`, framed: the input and work tapes are untouched. -/
theorem loop_rewind_step_left_frame (tmBody tmTest : TM n)
    (c : Cfg n (loopTM tmBody tmTest).Q)
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hread_ne : c.output.read ≠ Γ.start)
    (_hc0 : c.output.cells 0 = Γ.start) (_hns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head ≥ 1) (hwns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl LoopPhase.rewindOut) ∧
      c'.output.head = c.output.head - 1 ∧
      c'.output.cells = c.output.cells ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread_ne]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [Tape.writeAndMove, Tape.move]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]
    split
    · omega
    · simp
  · simp only [Tape.writeAndMove, Tape.move_cells]
    rw [toΓ_readBackWrite_of_ne_start hread_ne]
    simp only [Tape.write, Tape.read]
    split
    · rfl
    · exact Function.update_eq_self _ _
  · exact tape_move_idleDir_stable c.input hih hins
  · funext i
    exact tape_writeAndMove_stable (c.work i) (hwh i) (hwns i)

/-- The final rewind step of `loopTM`, framed. -/
theorem loop_rewind_step_base_frame (tmBody tmTest : TM n)
    (c : Cfg n (loopTM tmBody tmTest).Q)
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hread : c.output.read = Γ.start)
    (_hc0 : c.output.cells 0 = Γ.start) (hnostart : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head ≥ 1) (hwns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c', (loopTM tmBody tmTest).step c = some c' ∧
      c'.state = Sum.inr (Sum.inl LoopPhase.check) ∧
      c'.output.head = 1 ∧
      c'.output.cells = c.output.cells ∧
      c'.input = c.input ∧ c'.work = c.work := by
  have hne : c.state ≠ (loopTM tmBody tmTest).qhalt := by
    rw [hstate]; nofun
  have hhead : c.output.head = 0 := by
    by_contra hcon
    have hge : c.output.head ≥ 1 := by omega
    exact hnostart c.output.head hge (by simp only [Tape.read] at hread; exact hread)
  simp only [TM.step, ↓reduceIte, hstate, loopTM, hread]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.move, Tape.write, hhead]
  · simp [Tape.writeAndMove, Tape.move_cells, Tape.write, hhead]
  · exact tape_move_idleDir_stable c.input hih hins
  · funext i
    exact tape_writeAndMove_stable (c.work i) (hwh i) (hwns i)

/-- **The rewind phase of `loopTM`, framed.** From `rewindOut` with the output head at `p`, the
machine reaches `check` in `p + 1` steps with the output head at cell 1, the output cells
unchanged, and the input and work tapes *identical* — heads included. This is what lets a loop
invariant on the work tapes survive the phase and be re-established for the next iteration. -/
theorem loopTM_rewind_loop_frame (tmBody tmTest : TM n) (p : ℕ)
    (c : Cfg n (loopTM tmBody tmTest).Q)
    (hstate : c.state = Sum.inr (Sum.inl LoopPhase.rewindOut))
    (hc0 : c.output.cells 0 = Γ.start) (hns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hp : c.output.head = p)
    (hih : c.input.head ≥ 1) (hins : ∀ j, j ≥ 1 → c.input.cells j ≠ Γ.start)
    (hwh : ∀ i, (c.work i).head ≥ 1) (hwns : ∀ i j, j ≥ 1 → (c.work i).cells j ≠ Γ.start) :
    ∃ c_check,
      (loopTM tmBody tmTest).reachesIn (p + 1) c c_check ∧
      c_check.state = Sum.inr (Sum.inl LoopPhase.check) ∧
      c_check.output.head = 1 ∧
      c_check.output.cells = c.output.cells ∧
      c_check.input = c.input ∧
      c_check.work = c.work :=
  exists_reachesIn_of_rewindStep_frame (loopTM tmBody tmTest)
    (fun d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
      loop_rewind_step_left_frame tmBody tmTest d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈)
    (fun d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ =>
      loop_rewind_step_base_frame tmBody tmTest d h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈)
    p c hstate hc0 hns hp hih hins hwh hwns

end TM

end Complexity
