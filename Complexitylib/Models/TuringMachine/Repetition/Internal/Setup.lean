/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Schedule
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Finish

/-!
# Setup boundary for fixed-time repetition

This internal module packages the complete two-transition setup as the base
case of the repetition schedule. It also handles the degenerate zero-trial
machine, whose setup immediately halts with the empty majority verdict.

## Main results

- `NTM.repeatAtTime_trace_setup_ready` — all first-trial boundary ingredients
- `NTM.repeatAtTime_trace_setup_boundary` — the initial `RepeatBoundary`
- `NTM.repeatAtTime_trace_zero_repetitions` — the `k = 0` endpoint
-/


public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- The second setup transition preserves the fresh-bank frame while
positioning bank zero, uniformly for positive and zero simulation time. -/
theorem RepeatFrame.begin (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (choice : Fin 1 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    RepeatFrame x j
      ((repeatAtTime tm k T).trace 1 choice (repeatParkedCfg tm k T x)) := by
  dsimp only
  let j : Fin k := ⟨0, hk⟩
  let C := (repeatAtTime tm k T).trace 1 choice (repeatParkedCfg tm k T x)
  have hproject : repeatProjectCfg tm j tm.qstart C = tm.initCfg x := by
    by_cases hT : 0 < T
    · exact repeatAtTime_begin_project tm x hk hT choice
    · have hzero : T = 0 := Nat.eq_zero_of_not_pos hT
      subst T
      exact (repeatAtTime_begin_zero_simulates tm x hk choice).2.1
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun c : Cfg n tm.Q => c.input.cells) hproject
    simpa [C, j, repeatProjectCfg] using h
  · intro l hjl i
    have hlj : l ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp only [j] at this
      omega
    have hp := repeatParked_parkedBlank
    have hstable := hp.writeAndMove_idle
    by_cases hT : 0 < T
    · simp [j, trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition, repeatPositionBankDirs,
      hk, hT, hlj]
      exact hstable
    · simp [j, trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition, repeatPositionBankDirs,
      hk, hT, hlj]
      exact hstable
  · have hp := repeatParked_parkedBlank
    have hstable := hp.writeAndMove_idle
    by_cases hT : 0 < T
    · simp [trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition, hk, hT]
      exact hstable
    · simp [trace, repeatAtTime, repeatParkedCfg, repeatGuardTransition, hk, hT]
      exact hstable

/-- With at least one trial, the full two-step setup establishes every fact
needed to start the first trial and its outer-induction boundary. -/
theorem repeatAtTime_trace_setup_ready (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (seed : Fin (k * T) → Bool) (choices : Fin 2 → Bool) :
    let j : Fin k := ⟨0, hk⟩
    let votes : Fin k → Bool := fun _ => false
    let C := (repeatAtTime tm k T).trace 2 choices ((repeatAtTime tm k T).initCfg x)
    RepeatCompletedVotes tm x seed votes 0 ∧
      C.state = repeatTrialStartState tm j votes ∧
      repeatProjectCfg tm j tm.qstart C = tm.initCfg x ∧
      C.input.StartInvariant ∧ (∀ i, (C.work i).StartInvariant) ∧
      C.output.StartInvariant ∧ C.input.head = 0 ∧
      (∀ i, (C.work (repeatTapeIdx j i)).head = 0) ∧
      RepeatFrame x j C ∧ RepeatOtherParked j C := by
  dsimp only
  let j : Fin k := ⟨0, hk⟩
  let votes : Fin k → Bool := fun _ => false
  let C := (repeatAtTime tm k T).trace 2 choices ((repeatAtTime tm k T).initCfg x)
  have hstate : C.state = repeatTrialStartState tm j votes := by
    by_cases hT : 0 < T
    · have h := (repeatAtTime_trace_setup_simulates tm x hk hT choices).1
      simpa [C, j, votes, repeatTrialStartState, hT] using h
    · have hzero : T = 0 := Nat.eq_zero_of_not_pos hT
      subst T
      simp only [C]
      rw [(repeatAtTime tm k 0).trace_two, repeatAtTime_trace_setup]
      have h := (repeatAtTime_begin_zero_simulates tm x hk
        (fun _ => choices ⟨1, by omega⟩)).1
      simpa [j, votes, repeatTrialStartState] using h
  have hproject : repeatProjectCfg tm j tm.qstart C = tm.initCfg x := by
    by_cases hT : 0 < T
    · simpa [C, j] using repeatAtTime_trace_setup_project tm x hk hT choices
    · have hzero : T = 0 := Nat.eq_zero_of_not_pos hT
      subst T
      simp only [C]
      rw [(repeatAtTime tm k 0).trace_two, repeatAtTime_trace_setup]
      exact (repeatAtTime_begin_zero_simulates tm x hk
        (fun _ => choices ⟨1, by omega⟩)).2.1
  have hinv := (repeatAtTime tm k T).trace_startInvariant 2 choices
    ((repeatAtTime tm k T).initCfg x) (Tape.StartInvariant.init_ofBool x)
    (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
  have hinputHead : C.input.head = 0 := by
    have h := congrArg (fun c : Cfg n tm.Q => c.input.head) hproject
    simpa [repeatProjectCfg] using h
  have hactiveHead : ∀ i, (C.work (repeatTapeIdx j i)).head = 0 := by
    intro i
    cases i using Fin.lastCases with
    | last =>
      have h := congrArg (fun c : Cfg n tm.Q => c.output.head) hproject
      simpa [repeatProjectCfg, repeatOutputIdx] using h
    | cast i =>
      have h := congrArg (fun c : Cfg n tm.Q => (c.work i).head) hproject
      simpa [repeatProjectCfg, repeatWorkIdx] using h
  have hframe : RepeatFrame x j C := by
    simp only [C]
    rw [(repeatAtTime tm k T).trace_two, repeatAtTime_trace_setup]
    exact RepeatFrame.begin tm x hk (fun _ => choices ⟨1, by omega⟩)
  have hparked : RepeatOtherParked j C := by
    simp only [C]
    rw [(repeatAtTime tm k T).trace_two, repeatAtTime_trace_setup]
    exact RepeatOtherParked.begin tm x hk (fun _ => choices ⟨1, by omega⟩)
  exact ⟨RepeatCompletedVotes.zero tm x seed, hstate, hproject, hinv.1,
    hinv.2.1, hinv.2.2, hinputHead, hactiveHead, hframe, hparked⟩

/-- The complete setup trace is the initial outer boundary before trial zero. -/
theorem repeatAtTime_trace_setup_boundary (tm : NTM n) (x : List Bool)
    (hk : 0 < k) (seed : Fin (k * T) → Bool) (choices : Fin 2 → Bool) :
    RepeatBoundary tm x seed 0
      ((repeatAtTime tm k T).trace 2 choices ((repeatAtTime tm k T).initCfg x)) := by
  have h := repeatAtTime_trace_setup_ready tm x hk seed choices
  dsimp only at h
  rcases h with ⟨hvotes, hstate, hproject, _, _, _, _, _, hframe, hparked⟩
  simp only [RepeatBoundary, dite_eq_left hk]
  refine ⟨fun _ => false, hvotes, hstate, hproject, ?_, ?_⟩
  · exact hframe
  · exact hparked

/-- With no trials, the two setup transitions halt and write the strict
majority of the empty vote vector, namely zero, to output cell one. -/
theorem repeatAtTime_trace_zero_repetitions (tm : NTM n) (x : List Bool)
    (seed : Fin (0 * T) → Bool)
    (choices : Fin (repeatAtTimeSteps 0 T) → Bool) :
    let C := (repeatAtTime tm 0 T).trace (repeatAtTimeSteps 0 T) choices
      ((repeatAtTime tm 0 T).initCfg x)
    C.state = RepeatQ.halt ∧ C.output.head = 1 ∧ C.output.cells 1 = Γ.zero ∧
      C.output.cells 1 = Γ.ofBool (majority (repeatVotes tm x 0 T seed)) := by
  dsimp only
  rw [(repeatAtTime tm 0 T).trace_cast (repeatAtTimeSteps_zero_internal T)]
  rw [(repeatAtTime tm 0 T).trace_two, repeatAtTime_trace_setup]
  simp [trace, repeatAtTime, repeatGuardTransition, repeatParkedCfg,
    Tape.writeAndMove, Tape.write, Tape.move, Tape.read, Tape.init,
    repeatSafeDir, TM.idleDir, majority, popCount, repeatVotes, Γ.ofBool]

end NTM

end Complexity
