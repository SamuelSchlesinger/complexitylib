/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Boundary
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Setup
public import Complexitylib.Models.TuringMachine.Repetition.Internal.Trial
public import Complexitylib.Models.TuringMachine.Repetition.Internal.VoteStep

/-!
# Pathwise correctness of fixed-time repetition

This module performs the outer induction over the exact repetition schedule.
When every `T`-choice source trace on the fixed input halts, each wrapper trial
records the corresponding compact-seed vote, transfers the fresh-bank boundary,
and the final trial writes their strict majority.

## Main results

- `NTM.repeatAtTime_outer_correct` — every exact trial boundary is correct
- `NTM.repeatAtTime_trace_correct_internal` — final full-trace majority theorem
-/


public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- Under fixed-input all-paths halting at time `T`, every exact wrapper trial
boundary satisfies `RepeatBoundary`. -/
theorem repeatAtTime_outer_correct (tm : NTM n) (x : List Bool)
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (hhalt : ∀ runChoices : Fin T → Bool,
      (tm.trace T runChoices (tm.initCfg x)).state = tm.qhalt) :
    RepeatOuterClaim tm x choices := by
  let seed := repeatRandomSeed k T choices
  by_cases hk : 0 < k
  · intro m
    induction m with
    | zero =>
        intro hm0
        change RepeatBoundary tm x seed 0 _
        rw [repeatBoundaryCfg]
        rw [(repeatAtTime tm k T).trace_cast (repeatAtTimeSteps_zero_internal T)]
        exact repeatAtTime_trace_setup_boundary tm x hk seed
          (fun i => repeatPrefixChoices choices 0 hm0
            (Fin.cast (repeatAtTimeSteps_zero_internal T).symm i))
    | succ m ih =>
        intro hmk
        have hm : m < k := by omega
        let j : Fin k := ⟨m, hm⟩
        let C₀ := repeatBoundaryCfg tm x choices m (Nat.le_of_lt hm)
        have hboundary := ih (Nat.le_of_lt hm)
        rw [RepeatBoundary, dite_eq_left hm] at hboundary
        obtain ⟨votes, hvotes, hstate, hproject, hframe, hparked⟩ := hboundary
        have hinv := (repeatAtTime tm k T).trace_initCfg_startInvariant x
          (repeatAtTimeSteps m T) (repeatPrefixChoices choices m (Nat.le_of_lt hm))
        have hinputHead : C₀.input.head = 0 := by
          have h := congrArg (fun c : Cfg n tm.Q => c.input.head) hproject
          simpa [C₀, repeatProjectCfg] using h
        have hactiveHead : ∀ i, (C₀.work (repeatTapeIdx j i)).head = 0 := by
          intro i
          cases i using Fin.lastCases with
          | last =>
              have h := congrArg (fun c : Cfg n tm.Q => c.output.head) hproject
              simpa [C₀, repeatProjectCfg, repeatOutputIdx] using h
          | cast i =>
              have h := congrArg (fun c : Cfg n tm.Q => (c.work i).head) hproject
              simpa [C₀, repeatProjectCfg, repeatWorkIdx] using h
        let runChoices := repeatSimulationChoices choices j
        let rewindChoices := repeatRewindChoices choices j
        let finishChoices : Fin 1 → Bool := fun _ => repeatFinishChoice choices j
        let c := tm.trace T (blocksEquiv k T seed j) (tm.initCfg x)
        let Cfinish := (repeatAtTime tm k T).trace (T + 1) rewindChoices
          ((repeatAtTime tm k T).trace T runChoices C₀)
        have htrial : RepeatTrialComplete tm x j votes c Cfinish := by
          have htrialRaw := repeatAtTime_trace_trial tm x j votes runChoices
            rewindChoices C₀ (by simpa [C₀, repeatTrialStartState] using hstate)
            hproject hinv.1 hinv.2.1 hinv.2.2 hinputHead hactiveHead hframe hparked
            (hhalt runChoices)
          simpa [Cfinish, c, runChoices, seed] using htrialRaw
        have hactiveOutput : (Cfinish.work (repeatOutputIdx j)).head = 1 := by
          simpa [repeatOutputIdx] using (htrial.2.2.2.1 (Fin.last n)).1
        have hstride :
            repeatBoundaryCfg tm x choices (m + 1) (Nat.succ_le_iff.mpr hm) =
              (repeatAtTime tm k T).trace 1 finishChoices Cfinish := by
          rw [repeatBoundaryCfg_succ tm x choices m hm]
          rw [repeatStrideChoices_trace_split_three]
        rw [hstride]
        by_cases hnext : m + 1 < k
        · simp only [RepeatBoundary, dite_eq_left hnext]
          let votes' := Function.update votes j (repeatVotes tm x k T seed j)
          have hfinish := repeatAtTime_trace_finish_next tm x seed j c.state votes Cfinish
            finishChoices htrial.1 hnext htrial.2.1 hactiveOutput htrial.2.2.2.2.1
            htrial.2.2.1
          have hactiveParked : ∀ i, RepeatParked (Cfinish.work (repeatTapeIdx j i)) := by
            intro i
            refine ⟨(htrial.2.2.2.1 i).2, ?_⟩
            rw [(htrial.2.2.2.1 i).1]
          have hparked' := RepeatOtherParked.finish tm htrial.2.2.2.2.2
            hactiveParked htrial.1 hnext finishChoices
          refine ⟨votes', ?_, ?_, ?_, ?_, ?_⟩
          · exact RepeatCompletedVotes.update tm x seed votes j hvotes
          · exact hfinish.1
          · exact hfinish.2.1
          · exact hfinish.2.2
          · exact hparked'
        · have hlast : ¬j.val + 1 < k := by simpa [j] using hnext
          have hfinish := repeatAtTime_trace_finish_last_votes tm x seed j c.state votes
            Cfinish finishChoices htrial.1 hlast htrial.2.1 hactiveOutput
            htrial.2.2.2.2.1
          have heq : m + 1 = k := by omega
          have hvotes' := RepeatCompletedVotes.update tm x seed votes j hvotes
          have hvotesFull : Function.update votes j (repeatVotes tm x k T seed j) =
              repeatVotes tm x k T seed := by
            apply RepeatCompletedVotes.eq_expected tm x seed
            simpa [j, heq] using hvotes'
          simp only [RepeatBoundary]
          rw [dite_eq_right]
          · simp only [hvotesFull] at hfinish
            exact hfinish
          · omega
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    intro m hm
    have hm0 : m = 0 := by omega
    subst m
    rw [RepeatBoundary, dite_eq_right (by omega)]
    have hzero := repeatAtTime_trace_zero_repetitions tm x seed choices
    simpa [repeatBoundaryCfg, repeatPrefixChoices_self] using
      ⟨hzero.1, hzero.2.1, hzero.2.2.2⟩

/-- Final pathwise correctness: the full wrapper trace halts and writes the
strict majority of the source accepting-event blocks selected by the compact
simulation seed. -/
theorem repeatAtTime_trace_correct_internal (tm : NTM n) (x : List Bool)
    (choices : Fin (repeatAtTimeSteps k T) → Bool)
    (hhalt : ∀ runChoices : Fin T → Bool,
      (tm.trace T runChoices (tm.initCfg x)).state = tm.qhalt) :
    let C := (repeatAtTime tm k T).trace (repeatAtTimeSteps k T) choices
      ((repeatAtTime tm k T).initCfg x)
    C.state = RepeatQ.halt ∧ C.output.head = 1 ∧
      C.output.cells 1 = Γ.ofBool
        (blockMajority (repeatAcceptEvent tm x T) (repeatRandomSeed k T choices)) := by
  have houter := repeatAtTime_outer_correct tm x choices hhalt
  have hfinal := houter.final
  simp only [repeatBoundaryCfg, repeatPrefixChoices_self, majority_repeatVotes]
    at hfinal
  exact hfinal

end NTM

end Complexity
