/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.BufferSpecs
public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerLift

/-!
# Completed child calls of the Tseitin streaming controller

This module combines the tape-level Hoare contracts for register operations
with the controller's child-trace embeddings. Each theorem starts at a
scheduled child call, runs that child to completion, takes the single return
step, and exposes the resulting first-bit read state together with the exact
buffer/output postcondition.
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-- A controller configuration is ready to read the next token in `mode`, and
its tapes satisfy `pred`. -/
def ControllerReadPred (mode : StreamMode) (pred : TapePred workTapeCount)
    (c : Cfg workTapeCount validEmitterTM.Q) : Prop :=
  c.state = controllerRead (.first mode) ∧ pred c.input c.work c.output

/-- Run a scheduled current-register increment and return to the saved literal
mode. -/
theorem validEmitterTM_increment_call_internal
    (mode : StreamMode) (v : BufferValues) (inp : Tape) (ys : List Bool)
    (hinp : TM.Parked inp) {actualInput out : Tape}
    {work : Fin workTapeCount → Tape}
    (hpre : BufferPred inp v ys actualInput work out) :
    ∃ c' t, t ≤ unaryUpdateTime v.current + 1 ∧
      validEmitterTM.reachesIn t
        (controllerIncrementCfg mode
          { state := (TM.incRegTM currentReg).qstart
            input := actualInput
            work
            output := out }) c' ∧
      ControllerReadPred mode
        (BufferPred inp { v with current := v.current + 1 } ys) c' := by
  have hchild := TM.incRegTM_hoareTime currentReg v.current inp v.work ys hinp
    (fun i _ => v.work_parked i) v.work_current
  obtain ⟨cChild, t, ht, hreach, hhalt, hpost⟩ :=
    hchild actualInput work out (by simpa only [BufferPred] using hpre)
  have hpost' :
      BufferPred inp { v with current := v.current + 1 } ys
        cChild.input cChild.work cChild.output := by
    simpa only [BufferPred, BufferValues.update_current] using hpost
  have ht' : t ≤ unaryUpdateTime v.current := by
    simpa only [unaryUpdateTime] using ht
  have hlift := validEmitterTM_increment_reachesIn_internal mode hreach
  have hreturn := validEmitterTM_increment_return_parked_step_internal mode
    cChild hhalt (by rw [hpost'.1]; exact hinp)
      (fun i => by rw [hpost'.2.1]; exact BufferValues.work_parked _ i)
      hpost'.2.2.parked
  refine ⟨controllerReadCfg mode cChild, t + 1, by omega, ?_, rfl, ?_⟩
  · exact TM.reachesIn_trans validEmitterTM hlift (.step hreturn .zero)
  · exact hpost'

/-- Run a scheduled literal commit and return to the updated boundary mode. -/
theorem validEmitterTM_commit_call_internal
    (pending : PendingSigns) (sign : Bool) (v : BufferValues)
    (inp : Tape) (ys : List Bool) (hinp : TM.Parked inp)
    {actualInput out : Tape} {work : Fin workTapeCount → Tape}
    (hpre : BufferPred inp v ys actualInput work out) :
    ∃ c' t, t ≤ commitLiteralTime pending v + 1 ∧
      validEmitterTM.reachesIn t
        (controllerCommitCfg pending sign
          { state := (commitLiteralTM pending).qstart
            input := actualInput
            work
            output := out }) c' ∧
      ControllerReadPred (.boundary (pending.push sign))
        (BufferPred inp (v.committed pending)
          (ys ++ commitBits pending v)) c' := by
  have hchild := commitLiteralTM_hoareTime_internal pending v inp ys hinp
  obtain ⟨cChild, t, ht, hreach, hhalt, hpost⟩ :=
    hchild actualInput work out hpre
  have hlift := validEmitterTM_commit_reachesIn_internal pending sign hreach
  have hreturn := validEmitterTM_commit_return_parked_step_internal pending sign
    cChild hhalt (by rw [hpost.1]; exact hinp)
      (fun i => by rw [hpost.2.1]; exact BufferValues.work_parked _ i)
      hpost.2.2.parked
  refine ⟨controllerReadCfg (.boundary (pending.push sign)) cChild,
    t + 1, by omega, ?_, rfl, hpost⟩
  exact TM.reachesIn_trans validEmitterTM hlift (.step hreturn .zero)

/-- Run a scheduled clause close and return to the empty boundary mode. -/
theorem validEmitterTM_close_call_internal
    (pending : PendingSigns) (v : BufferValues) (inp : Tape)
    (ys : List Bool) (hinp : TM.Parked inp)
    {actualInput out : Tape} {work : Fin workTapeCount → Tape}
    (hpre : BufferPred inp v ys actualInput work out) :
    ∃ c' t, t ≤ closeClauseTime pending v + 1 ∧
      validEmitterTM.reachesIn t
        (controllerCloseCfg pending
          { state := (closeClauseTM pending).qstart
            input := actualInput
            work
            output := out }) c' ∧
      ControllerReadPred (.boundary .zero)
        (BufferPred inp (v.closed pending)
          (ys ++ pendingBits pending v)) c' := by
  have hchild := closeClauseTM_hoareTime_internal pending v inp ys hinp
  obtain ⟨cChild, t, ht, hreach, hhalt, hpost⟩ :=
    hchild actualInput work out hpre
  have hlift := validEmitterTM_close_reachesIn_internal pending hreach
  have hreturn := validEmitterTM_close_return_parked_step_internal pending
    cChild hhalt (by rw [hpost.1]; exact hinp)
      (fun i => by rw [hpost.2.1]; exact BufferValues.work_parked _ i)
      hpost.2.2.parked
  refine ⟨controllerReadCfg (.boundary .zero) cChild,
    t + 1, by omega, ?_, rfl, hpost⟩
  exact TM.reachesIn_trans validEmitterTM hlift (.step hreturn .zero)

end Machine

end ThreeSAT

end SAT

end Complexity
