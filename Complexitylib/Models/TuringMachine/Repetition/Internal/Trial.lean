/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Parked

/-!
# Complete trials for fixed-time repetition

This internal module composes one fixed-width source simulation with the
administrative rewind. It handles both positive simulation widths and the
zero-time path, and packages the finish-state facts needed by the vote step.

## Main results

- `NTM.RepeatTrialComplete` — finish-state simulation, parking, and frame facts
- `NTM.repeatAtTime_trace_rewind_trial` — common rewind-to-finish composition
- `NTM.repeatAtTime_trace_trial_pos` — a complete positive-time trial
- `NTM.repeatAtTime_trace_trial_zero` — a complete zero-time trial
- `NTM.repeatAtTime_trace_trial` — the combined trial theorem for every `T`
-/


@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- Facts established when one repetition trial has completed its fixed
rewind and reached `.finish`. -/
def RepeatTrialComplete (tm : NTM n) (x : List Bool) (j : Fin k)
    (votes : Fin k → Bool) (c : Cfg n tm.Q)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T)) : Prop :=
  C.state = .finish j c.state votes ∧
    RepeatSimulates tm j c.state c C ∧
    C.input = parkedInput x ∧
    (∀ i, (C.work (repeatTapeIdx j i)).head = 1 ∧
      (C.work (repeatTapeIdx j i)).StartInvariant) ∧
    RepeatFrame x j C ∧ RepeatOtherParked j C

/-- Every proper prefix of a positive-time run preserves the fresh-bank frame. -/
theorem RepeatFrame.trace_run_prefix (tm : NTM n) (hT : 0 < T)
    (x : List Bool) (j : Fin k) (votes : Fin k → Bool)
    (g : ℕ → Bool) (c₀ : Cfg n tm.Q)
    (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = .run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hframe : RepeatFrame x j C₀)
    (m : ℕ) (hm : m < T) :
    RepeatFrame x j
      ((repeatAtTime tm k T).trace m (fun i => g i.val) C₀) := by
  induction m with
  | zero => simpa [trace] using hframe
  | succ m ih =>
    have hm' : m < T := by omega
    let C := (repeatAtTime tm k T).trace m
      (fun i => g i.val) C₀
    have hprefix := repeatAtTime_trace_run_prefix tm hT j votes g c₀ C₀
      hstate hsim hinp hwork hout m hm'
    have hCstate : C.state = .run j ⟨m, hm'⟩
        (tm.trace m (fun i => g i.val) c₀).state votes := by
      simpa [C] using hprefix.1
    erw [(repeatAtTime tm k T).trace_add m 1]
    apply RepeatFrame.run tm
    · exact ih hm'
    · exact hCstate

/-- A complete positive-time run preserves the fresh-bank frame. -/
theorem RepeatFrame.trace_run (tm : NTM n) (hT : 0 < T)
    (x : List Bool) (j : Fin k) (votes : Fin k → Bool)
    (choices : Fin T → Bool) (c₀ : Cfg n tm.Q)
    (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = .run j ⟨0, hT⟩ c₀.state votes)
    (hsim : RepeatSimulates tm j c₀.state c₀ C₀)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hframe : RepeatFrame x j C₀) :
    RepeatFrame x j ((repeatAtTime tm k T).trace T choices C₀) := by
  let g : ℕ → Bool := fun a => if ha : a < T then choices ⟨a, ha⟩ else false
  have hg : (fun i : Fin T => g i.val) = choices := by
    funext i
    simp [g, i.isLt]
  rw [← hg]
  let m := T - 1
  have hm : m < T := by omega
  let C := (repeatAtTime tm k T).trace m
    (fun i => g i.val) C₀
  have hprefix := repeatAtTime_trace_run_prefix tm hT j votes g c₀ C₀ hstate hsim
    hinp hwork hout m hm
  have hCstate : C.state = .run j ⟨m, hm⟩
      (tm.trace m (fun i => g i.val) c₀).state votes := by
    simpa [C] using hprefix.1
  have hprefixFrame := RepeatFrame.trace_run_prefix tm hT x j votes g c₀ C₀
    hstate hsim hinp hwork hout hframe m hm
  let C' := (repeatAtTime tm k T).trace 1 (fun _ => g m) C
  have hsplit :
      (repeatAtTime tm k T).trace T (fun i => g i.val) C₀ = C' := by
    calc
      _ = (repeatAtTime tm k T).trace (m + 1) (fun i => g i.val) C₀ := by
        simpa using (repeatAtTime tm k T).trace_cast
          (show T = m + 1 by omega) (fun i => g i.val) C₀
      _ = C' := by
        simpa [C, C'] using
          (repeatAtTime tm k T).trace_snoc m (fun i => g i.val) C₀
  rw [hsplit]
  exact RepeatFrame.run tm hprefixFrame hCstate _

/-- Fixed rewind turns a halted source simulation into the complete trial
facts consumed by a finish transition. -/
theorem repeatAtTime_trace_rewind_trial (tm : NTM n) (x : List Bool)
    (j : Fin k) (votes : Fin k → Bool) (c : Cfg n tm.Q)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C.state = .rewind j ⟨0, by omega⟩ c.state votes false (fun _ => false))
    (hsim : RepeatSimulates tm j c.state c C) (hhalt : c.state = tm.qhalt)
    (hinp : C.input.StartInvariant) (hwork : ∀ i, (C.work i).StartInvariant)
    (hout : C.output.StartInvariant) (hinputHead : C.input.head ≤ T)
    (hactiveHead : ∀ i, (C.work (repeatTapeIdx j i)).head ≤ T)
    (hframe : RepeatFrame x j C) (hparked : RepeatOtherParked j C)
    (choices : Fin (T + 1) → Bool) :
    RepeatTrialComplete tm x j votes c
      ((repeatAtTime tm k T).trace (T + 1) choices C) := by
  let C' := (repeatAtTime tm k T).trace (T + 1) choices C
  have hrewind := repeatAtTime_trace_rewind_bound tm j c.state votes C hstate hinp
    (fun i => hwork (repeatTapeIdx j i)) hinputHead hactiveHead hparked.1 hparked.2
    choices
  dsimp only at hrewind
  have hparked' := RepeatOtherParked.trace_rewind tm j c.state votes C hstate hinp
    (fun i => hwork (repeatTapeIdx j i)) hinputHead hactiveHead hparked choices
  have hinv' := (repeatAtTime tm k T).trace_startInvariant (T + 1) choices C hinp
    hwork hout
  have hsim' : RepeatSimulates tm j c.state c C' := by
    refine ⟨hsim.1, ?_, ?_, ?_, ?_⟩
    · exact hrewind.2.2.1.trans hsim.2.1
    · intro i
      exact (hrewind.2.2.2.1 i.castSucc).2.trans (hsim.2.2.1 i)
    · exact (hrewind.2.2.2.1 (Fin.last n)).2.trans hsim.2.2.2.1
    · intro hc
      exact (hc hhalt).elim
  have hinput : C'.input = parkedInput x := by
    apply Tape.ext
    · exact hrewind.2.1
    · rw [hrewind.2.2.1, hframe.1]
      exact (Tape.move_cells _ _).symm
  have hframe' : RepeatFrame x j C' := by
    refine ⟨hrewind.2.2.1.trans hframe.1, ?_, ?_⟩
    · intro l hjl i
      have hne : (repeatTapeCoord (repeatTapeIdx l i)).1 ≠ j := by
        simp only [repeatTapeCoord_repeatTapeIdx]
        intro h
        subst l
        omega
      rw [hrewind.2.2.2.2.1 (repeatTapeIdx l i) hne]
      exact hframe.2.1 l hjl i
    · rw [hrewind.2.2.2.2.2]
      exact hframe.2.2
  dsimp only [RepeatTrialComplete]
  refine ⟨hrewind.1, hsim', hinput, ?_, hframe', hparked'⟩
  intro i
  exact ⟨(hrewind.2.2.2.1 i).1, hinv'.2.1 (repeatTapeIdx j i)⟩

/-- One positive-time trial simulates exactly `T` source steps and then
rewinds to a complete finish configuration. -/
theorem repeatAtTime_trace_trial_pos (tm : NTM n) (x : List Bool)
    (hT : 0 < T) (j : Fin k) (votes : Fin k → Bool)
    (runChoices : Fin T → Bool) (rewindChoices : Fin (T + 1) → Bool)
    (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = .run j ⟨0, hT⟩ tm.qstart votes)
    (hproject : repeatProjectCfg tm j tm.qstart C₀ = tm.initCfg x)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hinputHead : C₀.input.head = 0)
    (hactiveHead : ∀ i, (C₀.work (repeatTapeIdx j i)).head = 0)
    (hframe : RepeatFrame x j C₀) (hparked : RepeatOtherParked j C₀)
    (hhalt : (tm.trace T runChoices (tm.initCfg x)).state = tm.qhalt) :
    RepeatTrialComplete tm x j votes
      (tm.trace T runChoices (tm.initCfg x))
      ((repeatAtTime tm k T).trace (T + 1) rewindChoices
        ((repeatAtTime tm k T).trace T runChoices C₀)) := by
  let c := tm.trace T runChoices (tm.initCfg x)
  let C := (repeatAtTime tm k T).trace T runChoices C₀
  have hsim₀ := RepeatSimulates.of_project_eq tm j tm.qstart (tm.initCfg x) C₀ hproject
  have hrun := repeatAtTime_trace_run tm hT j votes runChoices (tm.initCfg x) C₀
    hstate hsim₀ hinp hwork hout
  dsimp only at hrun
  have hframeRun := RepeatFrame.trace_run tm hT x j votes runChoices (tm.initCfg x) C₀
    hstate hsim₀ hinp hwork hout hframe
  have hparkedRun := RepeatOtherParked.trace_run tm hT j votes runChoices
    (tm.initCfg x) C₀ hstate hsim₀ hinp hwork hout hparked
  have hinputBound : C.input.head ≤ T := by
    have hbound := (repeatAtTime tm k T).input_head_trace_le T runChoices C₀
    simpa [C, hinputHead] using hbound
  have hactiveBound : ∀ i, (C.work (repeatTapeIdx j i)).head ≤ T := by
    intro i
    have hbound := (repeatAtTime tm k T).work_head_trace_le T runChoices C₀
      (repeatTapeIdx j i)
    simpa [C, hactiveHead i] using hbound
  have hcomplete := repeatAtTime_trace_rewind_trial tm x j votes c C hrun.1
    hrun.2.1 hhalt hrun.2.2.1 hrun.2.2.2.1 hrun.2.2.2.2 hinputBound
    hactiveBound hframeRun hparkedRun rewindChoices
  simpa [c, C] using hcomplete

/-- A zero-time trial starts directly in rewind and reaches the same complete
finish configuration as a positive-time trial. -/
theorem repeatAtTime_trace_trial_zero (tm : NTM n) (x : List Bool)
    (j : Fin k) (votes : Fin k → Bool) (rewindChoices : Fin 1 → Bool)
    (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k 0))
    (hstate : C₀.state = .rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false))
    (hproject : repeatProjectCfg tm j tm.qstart C₀ = tm.initCfg x)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hinputHead : C₀.input.head = 0)
    (hactiveHead : ∀ i, (C₀.work (repeatTapeIdx j i)).head = 0)
    (hframe : RepeatFrame x j C₀) (hparked : RepeatOtherParked j C₀)
    (hhalt : tm.qstart = tm.qhalt) :
    RepeatTrialComplete tm x j votes (tm.initCfg x)
      ((repeatAtTime tm k 0).trace 1 rewindChoices C₀) := by
  have hsim₀ := RepeatSimulates.of_project_eq tm j tm.qstart (tm.initCfg x) C₀ hproject
  have hhalt' : (tm.initCfg x).state = tm.qhalt := by
    simpa using hhalt
  have hinputBound : C₀.input.head ≤ 0 := by omega
  have hactiveBound : ∀ i, (C₀.work (repeatTapeIdx j i)).head ≤ 0 := by
    intro i
    have hi := hactiveHead i
    omega
  simpa using repeatAtTime_trace_rewind_trial tm x j votes (tm.initCfg x) C₀
    hstate hsim₀ hhalt' hinp hwork hout hinputBound hactiveBound hframe hparked
    rewindChoices

/-- A complete trial theorem uniform in the simulation width: positive widths
run the source for `T` slots before rewind, while width zero starts in rewind. -/
theorem repeatAtTime_trace_trial (tm : NTM n) (x : List Bool)
    (j : Fin k) (votes : Fin k → Bool) (runChoices : Fin T → Bool)
    (rewindChoices : Fin (T + 1) → Bool)
    (C₀ : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hstate : C₀.state = if hT : 0 < T then
      RepeatQ.run j ⟨0, hT⟩ tm.qstart votes
    else RepeatQ.rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false))
    (hproject : repeatProjectCfg tm j tm.qstart C₀ = tm.initCfg x)
    (hinp : C₀.input.StartInvariant)
    (hwork : ∀ i, (C₀.work i).StartInvariant)
    (hout : C₀.output.StartInvariant) (hinputHead : C₀.input.head = 0)
    (hactiveHead : ∀ i, (C₀.work (repeatTapeIdx j i)).head = 0)
    (hframe : RepeatFrame x j C₀) (hparked : RepeatOtherParked j C₀)
    (hhalt : (tm.trace T runChoices (tm.initCfg x)).state = tm.qhalt) :
    RepeatTrialComplete tm x j votes
      (tm.trace T runChoices (tm.initCfg x))
      ((repeatAtTime tm k T).trace (T + 1) rewindChoices
        ((repeatAtTime tm k T).trace T runChoices C₀)) := by
  by_cases hT : 0 < T
  · have hstate' : C₀.state = .run j ⟨0, hT⟩ tm.qstart votes := by
      simpa [hT] using hstate
    exact repeatAtTime_trace_trial_pos tm x hT j votes runChoices rewindChoices C₀
      hstate' hproject hinp hwork hout hinputHead hactiveHead hframe hparked hhalt
  · have hzero : T = 0 := Nat.eq_zero_of_not_pos hT
    subst T
    have hstate' :
        C₀.state = .rewind j ⟨0, by omega⟩ tm.qstart votes false (fun _ => false) := by
      simpa using hstate
    have hhalt' : tm.qstart = tm.qhalt := by
      simpa [trace] using hhalt
    simp [trace]
    exact repeatAtTime_trace_trial_zero tm x j votes rewindChoices C₀ hstate' hproject hinp hwork
      hout hinputHead hactiveHead hframe hparked hhalt'

end NTM

end Complexity
