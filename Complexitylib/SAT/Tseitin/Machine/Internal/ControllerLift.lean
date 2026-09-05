/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.Tseitin.Machine.Controller

/-!
# Child-execution lifting for the Tseitin streaming controller

The concrete streaming controller runs three families of child machines:
unary increments, literal commits, and clause closes. This file proves only
the control-flow plumbing for those calls. A child step and hence an exact
`reachesIn` trace lift into `validEmitterTM` while all tapes are shared
literally. Once a child reaches its halt state, one controller step returns to
the appropriate first-bit read mode.

The generic return lemmas expose the standard phase-boundary tape operations
`TM.transitionInput` and `TM.transitionTape`. Parked specializations show that
these operations are identities in the register invariants used later.

No token semantics are proved here.

## Main results

- `validEmitterTM_increment_reachesIn_internal`
- `validEmitterTM_commit_reachesIn_internal`
- `validEmitterTM_close_reachesIn_internal`
- `validEmitterTM_increment_return_step_internal`
- `validEmitterTM_commit_return_step_internal`
- `validEmitterTM_close_return_step_internal`
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Configuration embeddings -/

/-- Embed arbitrary tapes into the controller at the first bit of `mode`. -/
def controllerReadCfg {Q : Type} (mode : StreamMode)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerRead (.first mode)
  input := c.input
  work := c.work
  output := c.output

/-- The read continuation after the controller's standard boundary tape
transition. -/
def controllerReadTransitionCfg {Q : Type} (mode : StreamMode)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerRead (.first mode)
  input := TM.transitionInput c.input
  work := fun i => TM.transitionTape (c.work i)
  output := TM.transitionTape c.output

/-- Embed an increment-child configuration in the controller state space. -/
def controllerIncrementCfg (mode : StreamMode)
    (c : Cfg workTapeCount (TM.incRegTM currentReg).Q) :
    Cfg workTapeCount validEmitterTM.Q where
  state := controllerIncrement mode c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a pending-dependent commit-child configuration in the controller. -/
def controllerCommitCfg (pending : PendingSigns) (sign : Bool)
    (c : Cfg workTapeCount (commitLiteralTM pending).Q) :
    Cfg workTapeCount validEmitterTM.Q where
  state := controllerCommit pending sign c.state
  input := c.input
  work := c.work
  output := c.output

/-- Embed a pending-dependent close-child configuration in the controller. -/
def controllerCloseCfg (pending : PendingSigns)
    (c : Cfg workTapeCount (closeClauseTM pending).Q) :
    Cfg workTapeCount validEmitterTM.Q where
  state := controllerClose pending c.state
  input := c.input
  work := c.work
  output := c.output

/-- A standard boundary transition is the identity on parked tapes. -/
theorem controllerReadTransitionCfg_eq_readCfg_internal {Q : Type}
    (mode : StreamMode) (c : Cfg workTapeCount Q)
    (hinp : TM.Parked c.input) (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked c.output) :
    controllerReadTransitionCfg mode c = controllerReadCfg mode c := by
  apply Cfg.ext
  · rfl
  · exact TM.Parked.transitionInput_eq_self hinp
  · funext i
    exact TM.Parked.transitionTape_eq_self (hwork i)
  · exact TM.Parked.transitionTape_eq_self hout

/-! ## Increment child -/

/-- One step of the unary increment child is one controller increment-call
step with literally identical tapes. -/
theorem validEmitterTM_increment_step_internal (mode : StreamMode)
    {c c' : Cfg workTapeCount (TM.incRegTM currentReg).Q}
    (hstep : (TM.incRegTM currentReg).step c = some c') :
    validEmitterTM.step (controllerIncrementCfg mode c) =
      some (controllerIncrementCfg mode c') := by
  have hne := TM.state_ne_qhalt_of_step hstep
  have hnotDone :
      (controllerIncrementCfg mode c).state ≠ validEmitterTM.qhalt := by
    simp [controllerIncrementCfg, validEmitterTM, controllerIncrement, controllerDone]
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rw [TM.step, ite_eq_right hnotDone]
  simp only [controllerIncrementCfg, validEmitterTM, controllerIncrement,
    controllerDone, hne, ↓reduceIte]

/-- An exact unary-increment trace lifts point-for-point into the controller. -/
theorem validEmitterTM_increment_reachesIn_internal (mode : StreamMode)
    {t : ℕ} {c c' : Cfg workTapeCount (TM.incRegTM currentReg).Q}
    (hreach : (TM.incRegTM currentReg).reachesIn t c c') :
    validEmitterTM.reachesIn t (controllerIncrementCfg mode c)
      (controllerIncrementCfg mode c') :=
  TM.reachesIn_map (tm' := validEmitterTM) (controllerIncrementCfg mode)
    (fun _ _ => validEmitterTM_increment_step_internal mode) hreach

/-- A halted increment child returns to the saved parser mode after one
standard boundary transition. -/
theorem validEmitterTM_increment_return_step_internal (mode : StreamMode)
    (c : Cfg workTapeCount (TM.incRegTM currentReg).Q)
    (hhalt : c.state = (TM.incRegTM currentReg).qhalt) :
    validEmitterTM.step (controllerIncrementCfg mode c) =
      some (controllerReadTransitionCfg mode c) := by
  show (if (controllerIncrementCfg mode c).state = validEmitterTM.qhalt then none
        else some _) = some _
  simp only [controllerIncrementCfg, controllerReadTransitionCfg, validEmitterTM,
    controllerIncrement, controllerDone, hhalt, ↓reduceIte]
  congr 1

/-- Parked-tape specialization of the increment-child return step. -/
theorem validEmitterTM_increment_return_parked_step_internal (mode : StreamMode)
    (c : Cfg workTapeCount (TM.incRegTM currentReg).Q)
    (hhalt : c.state = (TM.incRegTM currentReg).qhalt)
    (hinp : TM.Parked c.input) (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerIncrementCfg mode c) =
      some (controllerReadCfg mode c) := by
  rw [validEmitterTM_increment_return_step_internal mode c hhalt,
    controllerReadTransitionCfg_eq_readCfg_internal mode c hinp hwork hout]

/-! ## Commit child -/

/-- One step of a pending-dependent commit child is one controller call step
with literally identical tapes. -/
theorem validEmitterTM_commit_step_internal (pending : PendingSigns) (sign : Bool)
    {c c' : Cfg workTapeCount (commitLiteralTM pending).Q}
    (hstep : (commitLiteralTM pending).step c = some c') :
    validEmitterTM.step (controllerCommitCfg pending sign c) =
      some (controllerCommitCfg pending sign c') := by
  have hne := TM.state_ne_qhalt_of_step hstep
  have hnotDone :
      (controllerCommitCfg pending sign c).state ≠ validEmitterTM.qhalt := by
    simp [controllerCommitCfg, validEmitterTM, controllerCommit, controllerDone]
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rw [TM.step, ite_eq_right hnotDone]
  simp only [controllerCommitCfg, validEmitterTM, controllerCommit,
    controllerDone, hne, ↓reduceIte]

/-- An exact commit-child trace lifts point-for-point into the controller. -/
theorem validEmitterTM_commit_reachesIn_internal (pending : PendingSigns) (sign : Bool)
    {t : ℕ} {c c' : Cfg workTapeCount (commitLiteralTM pending).Q}
    (hreach : (commitLiteralTM pending).reachesIn t c c') :
    validEmitterTM.reachesIn t (controllerCommitCfg pending sign c)
      (controllerCommitCfg pending sign c') :=
  TM.reachesIn_map (tm' := validEmitterTM) (controllerCommitCfg pending sign)
    (fun _ _ => validEmitterTM_commit_step_internal pending sign) hreach

/-- A halted commit child returns to the boundary mode containing its pushed
sign after one standard boundary transition. -/
theorem validEmitterTM_commit_return_step_internal (pending : PendingSigns)
    (sign : Bool) (c : Cfg workTapeCount (commitLiteralTM pending).Q)
    (hhalt : c.state = (commitLiteralTM pending).qhalt) :
    validEmitterTM.step (controllerCommitCfg pending sign c) =
      some (controllerReadTransitionCfg (.boundary (pending.push sign)) c) := by
  show (if (controllerCommitCfg pending sign c).state = validEmitterTM.qhalt then none
        else some _) = some _
  simp only [controllerCommitCfg, controllerReadTransitionCfg, validEmitterTM,
    controllerCommit, controllerDone, hhalt, ↓reduceIte]
  congr 1

/-- Parked-tape specialization of the commit-child return step. -/
theorem validEmitterTM_commit_return_parked_step_internal (pending : PendingSigns)
    (sign : Bool) (c : Cfg workTapeCount (commitLiteralTM pending).Q)
    (hhalt : c.state = (commitLiteralTM pending).qhalt)
    (hinp : TM.Parked c.input) (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerCommitCfg pending sign c) =
      some (controllerReadCfg (.boundary (pending.push sign)) c) := by
  rw [validEmitterTM_commit_return_step_internal pending sign c hhalt,
    controllerReadTransitionCfg_eq_readCfg_internal
      (.boundary (pending.push sign)) c hinp hwork hout]

/-! ## Close child -/

/-- One step of a pending-dependent close child is one controller call step
with literally identical tapes. -/
theorem validEmitterTM_close_step_internal (pending : PendingSigns)
    {c c' : Cfg workTapeCount (closeClauseTM pending).Q}
    (hstep : (closeClauseTM pending).step c = some c') :
    validEmitterTM.step (controllerCloseCfg pending c) =
      some (controllerCloseCfg pending c') := by
  have hne := TM.state_ne_qhalt_of_step hstep
  have hnotDone :
      (controllerCloseCfg pending c).state ≠ validEmitterTM.qhalt := by
    simp [controllerCloseCfg, validEmitterTM, controllerClose, controllerDone]
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hstep
  subst hstep
  rw [TM.step, ite_eq_right hnotDone]
  simp only [controllerCloseCfg, validEmitterTM, controllerClose,
    controllerDone, hne, ↓reduceIte]

/-- An exact close-child trace lifts point-for-point into the controller. -/
theorem validEmitterTM_close_reachesIn_internal (pending : PendingSigns)
    {t : ℕ} {c c' : Cfg workTapeCount (closeClauseTM pending).Q}
    (hreach : (closeClauseTM pending).reachesIn t c c') :
    validEmitterTM.reachesIn t (controllerCloseCfg pending c)
      (controllerCloseCfg pending c') :=
  TM.reachesIn_map (tm' := validEmitterTM) (controllerCloseCfg pending)
    (fun _ _ => validEmitterTM_close_step_internal pending) hreach

/-- A halted close child returns to the empty boundary mode after one
standard boundary transition. -/
theorem validEmitterTM_close_return_step_internal (pending : PendingSigns)
    (c : Cfg workTapeCount (closeClauseTM pending).Q)
    (hhalt : c.state = (closeClauseTM pending).qhalt) :
    validEmitterTM.step (controllerCloseCfg pending c) =
      some (controllerReadTransitionCfg (.boundary .zero) c) := by
  show (if (controllerCloseCfg pending c).state = validEmitterTM.qhalt then none
        else some _) = some _
  simp only [controllerCloseCfg, controllerReadTransitionCfg, validEmitterTM,
    controllerClose, controllerDone, hhalt, ↓reduceIte]
  congr 1

/-- Parked-tape specialization of the close-child return step. -/
theorem validEmitterTM_close_return_parked_step_internal (pending : PendingSigns)
    (c : Cfg workTapeCount (closeClauseTM pending).Q)
    (hhalt : c.state = (closeClauseTM pending).qhalt)
    (hinp : TM.Parked c.input) (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerCloseCfg pending c) =
      some (controllerReadCfg (.boundary .zero) c) := by
  rw [validEmitterTM_close_return_step_internal pending c hhalt,
    controllerReadTransitionCfg_eq_readCfg_internal
      (.boundary .zero) c hinp hwork hout]

end Machine

end ThreeSAT

end SAT

end Complexity
