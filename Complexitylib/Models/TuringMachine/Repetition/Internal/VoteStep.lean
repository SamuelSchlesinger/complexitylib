/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Repetition.Internal.Finish
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Frame
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Votes
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Finish-step vote semantics for fixed-time repetition

This module identifies the bit recorded by a repetition finish transition with
the corresponding source-machine trial verdict. It combines that control-state
step with the fresh-bank frame layer to hand the outer induction an exact next
source configuration, and specializes the final finish theorem to `repeatVotes`.

## Main results

- `NTM.repeatTrialVote_eq_decide_trace` — source trace predicate for one trial
- `NTM.repeatAtTime_trace_finish_next_vote` — exact nonfinal control-state update
- `NTM.repeatAtTime_trace_finish_next` — control, projection, and frame handoff
- `NTM.repeatAtTime_trace_finish_last_votes` — final majority in source-vote form
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- A compact-seed trial vote is exactly the halted-with-one predicate of the
corresponding `T`-step source trace. -/
theorem repeatTrialVote_eq_decide_trace (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) :
    repeatTrialVote tm x k T seed j =
      decide (let c := tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)
        c.state = tm.qhalt ∧ c.output.cells 1 = Γ.one) := by
  simp [repeatTrialVote, repeatAcceptEvent]

/-- The accepting bit computed by `.finish` agrees with the corresponding
entry of the source-machine vote vector. -/
theorem repeatFinishAccepted_eq_repeatVotes (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) (q : tm.Q)
    (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (hsim : RepeatSimulates tm j q
      (tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)) C)
    (hactiveHead : (C.work (repeatOutputIdx j)).head = 1) :
    decide (q = tm.qhalt ∧ (C.work (repeatOutputIdx j)).read = Γ.one) =
      repeatVotes tm x k T seed j := by
  let c := tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)
  have hread : (C.work (repeatOutputIdx j)).read = c.output.cells 1 := by
    simp only [Tape.read, hactiveHead]
    exact congrFun hsim.2.2.2.1 1
  rw [repeatVotes, repeatTrialVote_eq_decide_trace]
  simp only
  rw [hsim.1, hread]

/-- A nonfinal finish transition records the exact source trial vote and enters
the next trial's run state, or its rewind state when `T = 0`. -/
theorem repeatAtTime_trace_finish_next_vote (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (choice : Fin 1 → Bool) (hstate : C.state = .finish j q votes)
    (hj : j.val + 1 < k)
    (hsim : RepeatSimulates tm j q
      (tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)) C)
    (hactiveHead : (C.work (repeatOutputIdx j)).head = 1) :
    let j' : Fin k := ⟨j.val + 1, hj⟩
    let votes' := Function.update votes j (repeatVotes tm x k T seed j)
    let C' := (repeatAtTime tm k T).trace 1 choice C
    C'.state = if hT : 0 < T then
      RepeatQ.run j' ⟨0, hT⟩ tm.qstart votes'
    else RepeatQ.rewind j' ⟨0, by omega⟩ tm.qstart votes' false (fun _ => false) := by
  dsimp only
  have hvote := repeatFinishAccepted_eq_repeatVotes tm x seed j q C hsim hactiveHead
  have hvote' :
      (decide (q = tm.qhalt) && decide ((C.work (repeatOutputIdx j)).read = Γ.one)) =
        repeatVotes tm x k T seed j := by
    calc
      _ = decide (q = tm.qhalt ∧ (C.work (repeatOutputIdx j)).read = Γ.one) := by
        by_cases hq : q = tm.qhalt <;>
          by_cases ho : (C.work (repeatOutputIdx j)).read = Γ.one <;>
          simp [hq, ho]
      _ = repeatVotes tm x k T seed j := hvote
  simp [trace, repeatAtTime, hstate, hj, hvote', repeatGuardTransition]

/-- A nonfinal finish simultaneously records the source vote, initializes the
next source projection, and advances the fresh-bank frame. -/
theorem repeatAtTime_trace_finish_next (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (choice : Fin 1 → Bool) (hstate : C.state = .finish j q votes)
    (hj : j.val + 1 < k)
    (hsim : RepeatSimulates tm j q
      (tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)) C)
    (hactiveHead : (C.work (repeatOutputIdx j)).head = 1)
    (hframe : RepeatFrame x j C) (hin : C.input = parkedInput x) :
    let j' : Fin k := ⟨j.val + 1, hj⟩
    let votes' := Function.update votes j (repeatVotes tm x k T seed j)
    let C' := (repeatAtTime tm k T).trace 1 choice C
    (C'.state = if hT : 0 < T then
      RepeatQ.run j' ⟨0, hT⟩ tm.qstart votes'
    else RepeatQ.rewind j' ⟨0, by omega⟩ tm.qstart votes' false (fun _ => false)) ∧
      repeatProjectCfg tm j' tm.qstart C' = tm.initCfg x ∧ RepeatFrame x j' C' := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact repeatAtTime_trace_finish_next_vote tm x seed j q votes C choice hstate hj
      hsim hactiveHead
  · exact RepeatFrame.finish_next_project tm hframe hstate hj hin choice
  · exact RepeatFrame.finish tm hframe hstate hj choice

/-- On the last trial, the wrapper writes the strict majority of the source
trial-vote vector with the current trial updated at `j`. -/
theorem repeatAtTime_trace_finish_last_votes (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) (q : tm.Q)
    (votes : Fin k → Bool) (C : Cfg (k * (n + 1)) (RepeatQ tm k T))
    (choice : Fin 1 → Bool) (hstate : C.state = .finish j q votes)
    (hlast : ¬j.val + 1 < k)
    (hsim : RepeatSimulates tm j q
      (tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)) C)
    (hactiveHead : (C.work (repeatOutputIdx j)).head = 1)
    (hframe : RepeatFrame x j C) :
    let C' := (repeatAtTime tm k T).trace 1 choice C
    C'.state = RepeatQ.halt ∧ C'.output.head = 1 ∧
      C'.output.cells 1 = Γ.ofBool
        (majority (Function.update votes j (repeatVotes tm x k T seed j))) := by
  let c := tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)
  have hout : C.output.StartInvariant := by
    have h := Tape.StartInvariant.init_nil.move Dir3.right
    simpa [hframe.2.2, parkedBlank] using h
  have houtHead : C.output.head = 1 := by
    rw [hframe.2.2]
    rfl
  have h := repeatAtTime_trace_finish_last tm j q votes c C choice hstate hlast hsim
    hactiveHead hout houtHead
  simpa only [repeatVotes, repeatTrialVote_eq_decide_trace] using h

end NTM

end Complexity
