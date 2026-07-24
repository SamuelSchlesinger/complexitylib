/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Registers
import Complexitylib.Models.TuringMachine.Subroutines.Internal

/-!
# Space-exact input rewind -- proof internals
-/

namespace Complexity

namespace TM

private theorem input_head_eq_zero_of_read_start {tape : Tape}
    (hinvariant : tape.StartInvariant) (hread : tape.read = Γ.start) :
    tape.head = 0 := by
  by_contra hne
  have hpositive : 1 ≤ tape.head := by omega
  exact hinvariant.2 tape.head hpositive (by simpa [Tape.read] using hread)

private theorem rewindInputTM_step_frame {n : ℕ}
    {before after : Cfg n (rewindInputTM (n := n)).Q}
    (hinput : before.input.StartInvariant)
    (hwork : ∀ i, Parked (before.work i))
    (houtput : Parked before.output)
    (hstep : (rewindInputTM (n := n)).step before = some after) :
    after.input.cells = before.input.cells ∧
      after.input.head ≤ max 1 before.input.head ∧
      after.work = before.work ∧ after.output = before.output := by
  have hne := state_ne_qhalt_of_step hstep
  cases hstate : before.state with
  | moveLeft =>
      by_cases hread : before.input.read = Γ.start
      · have hhead := input_head_eq_zero_of_read_start hinput hread
        simp [TM.step, hstate, rewindInputTM, hread] at hstep
        subst after
        refine ⟨by simp only [Tape.move_cells], ?_, ?_, ?_⟩
        · simp [Tape.move, hhead]
        · funext i
          exact (hwork i).writeAndMove_readBack_idle
        · exact houtput.writeAndMove_readBack_idle
      · simp [TM.step, hstate, rewindInputTM, hread] at hstep
        subst after
        refine ⟨by simp only [Tape.move_cells], ?_, ?_, ?_⟩
        · simp [Tape.move, moveLeftDir, hread]
        · funext i
          exact (hwork i).writeAndMove_readBack_idle
        · exact houtput.writeAndMove_readBack_idle
  | moveRight =>
      simp [TM.step, hstate, rewindInputTM] at hstep
      subst after
      refine ⟨by simp only [Tape.move_cells], ?_, ?_, ?_⟩
      · by_cases hread : before.input.read = Γ.start
        · have hhead := input_head_eq_zero_of_read_start hinput hread
          simp [Tape.move, idleDir, hread, hhead]
        · simp [Tape.move, idleDir, hread]
      · funext i
        exact (hwork i).writeAndMove_readBack_idle
      · exact houtput.writeAndMove_readBack_idle
  | done =>
      exact (hne (by simpa [rewindInputTM] using hstate)).elim

private theorem rewindInputTM_reachesIn_frame {n : ℕ}
    {time : ℕ} {start done : Cfg n (rewindInputTM (n := n)).Q}
    (hinput : start.input.StartInvariant)
    (hwork : ∀ i, Parked (start.work i))
    (houtput : Parked start.output)
    (hreach : (rewindInputTM (n := n)).reachesIn time start done) :
    done.input.cells = start.input.cells ∧
      done.input.head ≤ max 1 start.input.head ∧
      done.work = start.work ∧ done.output = start.output := by
  induction hreach with
  | zero => exact ⟨rfl, le_max_right 1 _, rfl, rfl⟩
  | @step before middle restTime final hstep hrest ih =>
      obtain ⟨hinputCells, hinputHead, hworkEq, houtputEq⟩ :=
        rewindInputTM_step_frame hinput hwork houtput hstep
      have hmiddleInput : middle.input.StartInvariant := by
        constructor
        · rw [hinputCells]
          exact hinput.1
        · intro index hindex
          rw [hinputCells]
          exact hinput.2 index hindex
      have hmiddleWork : ∀ i, Parked (middle.work i) := by
        intro i
        rw [hworkEq]
        exact hwork i
      have hmiddleOutput : Parked middle.output := by
        rw [houtputEq]
        exact houtput
      obtain ⟨hfinalCells, hfinalHead, hfinalWork, hfinalOutput⟩ :=
        ih hmiddleInput hmiddleWork hmiddleOutput
      refine ⟨hfinalCells.trans hinputCells, ?_, hfinalWork.trans hworkEq,
        hfinalOutput.trans houtputEq⟩
      exact le_trans hfinalHead (max_le (le_max_left 1 _) hinputHead)

theorem rewindInputTM_hoareTimeSpace_frame_internal {n : ℕ}
    (inputHeadBound inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinputInvariant : inp₀.StartInvariant) (hinput : Parked inp₀)
    (hinputHead : inp₀.head ≤ inputHeadBound)
    (hwork : ∀ i, Parked (work₀ i)) (houtput : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (rewindInputTM (n := n)).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.head = 1 ∧ inp.cells = inp₀.cells ∧
        work = work₀ ∧ out = out₀)
      (inputHeadBound + 2) inputLength initialSpace := by
  have htime := rewindInputTM_hoareTime_frame inputHeadBound
    (P := fun inp work out =>
      inp.cells = inp₀.cells ∧ work = work₀ ∧ out = out₀) (by
        intro inp work out inp' work' out' hframe hcells _hhead
          hworkEq houtputEq
        exact ⟨hcells.trans hframe.1, hworkEq.trans hframe.2.1,
          houtputEq.trans hframe.2.2⟩)
  have htime' : (rewindInputTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp.head = 1 ∧ inp.cells = inp₀.cells ∧
        work = work₀ ∧ out = out₀)
      (inputHeadBound + 2) :=
    htime.consequence
      (by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact ⟨hinputInvariant.1, hinputInvariant.2, hinputHead,
          houtput.read_ne_start, houtput.1,
          fun i => ⟨(hwork i).read_ne_start, (hwork i).1⟩, rfl, rfl, rfl⟩)
      (by
        rintro inp work out ⟨hhead, hcells, hworkEq, houtputEq⟩
        exact ⟨hhead, hcells, hworkEq, houtputEq⟩) le_rfl
  refine htime'.and_hoareSpace ?_
  intro inp work out hpre cfg hreach
  rcases hpre with ⟨hinputEq, hwork₀Eq, houtputEq⟩
  subst inp
  subst work
  subst out
  obtain ⟨time, hreachIn⟩ :=
    (rewindInputTM (n := n)).reaches_to_reachesIn hreach
  obtain ⟨hcells, hhead, hworkEq, _houtputEq⟩ :=
    rewindInputTM_reachesIn_frame hinputInvariant hwork houtput hreachIn
  constructor
  · intro i
    rw [hworkEq]
    exact hworkSpace i
  · have hone : 1 ≤ inp₀.head := hinput.1
    rw [max_eq_right hone] at hhead
    exact le_trans hhead hinputSpace

theorem rewindInputTM_isTransducer_internal {n : ℕ} :
    (rewindInputTM (n := n)).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase with
  | moveLeft =>
      simp only [rewindInputTM]
      split <;> simp [idleDir] <;> split <;> decide
  | moveRight =>
      simp [rewindInputTM, idleDir]
      split <;> decide
  | done =>
      simp [rewindInputTM, allIdle, idleDir]
      split <;> decide

end TM

end Complexity
