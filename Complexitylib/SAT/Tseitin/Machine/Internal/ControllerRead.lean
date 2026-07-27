/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.SAT.Tseitin.Machine.Internal.ControllerLift
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Concrete read paths for the Tseitin streaming controller

This file proves the input-reader plumbing of `validEmitterTM`. Every SAT
token occupies two input bits. Starting in a first-bit read state, the
controller reads those bits in exactly two steps, advances the input head
twice, and reaches the state selected by `scheduleToken`; parked work and
output tapes are unchanged. A first-bit read of the trailing blank reaches
`controllerDone` in one step with all tapes unchanged.

The scheduled state is not interpreted here. Child execution and pure token
semantics remain separate layers.

## Main results

- `validEmitterTM_read_token_reachesIn_internal`
- `validEmitterTM_read_blank_step_internal`
- `validEmitterTM_read_blank_reachesIn_internal`
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Token-bit framing -/

/-- First concrete bit of a SAT encoding token. -/
@[simp] def tokenFirstBit : EncToken → Bool
  | .bit b => b
  | .litSep => false
  | .clauseSep => true

/-- Second concrete bit of a SAT encoding token. -/
@[simp] def tokenSecondBit : EncToken → Bool
  | .bit b => b
  | .litSep => true
  | .clauseSep => false

/-- The named token bits are exactly the existing concrete token encoding. -/
@[simp] theorem token_encode_eq_bits (tok : EncToken) :
    tok.encode = [tokenFirstBit tok, tokenSecondBit tok] := by
  cases tok with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- Decoding the two named encoding bits recovers the token. -/
theorem tokenOfPair_token_bits (tok : EncToken) :
    tokenOfPair (tokenFirstBit tok) (tokenSecondBit tok) = tok := by
  cases tok with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- The input head and its right neighbor contain the encoding of `tok`. -/
def InputTokenAt (input : Tape) (tok : EncToken) : Prop :=
  input.read = Γ.ofBool (tokenFirstBit tok) ∧
    (input.move .right).read = Γ.ofBool (tokenSecondBit tok)

/-! ## Read configurations -/

/-- Controller configuration after reading the first bit of a token. -/
def controllerSecondCfg {Q : Type} (mode : StreamMode) (first : Bool)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerRead (.second mode first)
  input := c.input.move .right
  work := c.work
  output := c.output

/-- Controller configuration after reading a complete token. -/
def controllerScheduledCfg {Q : Type} (mode : StreamMode) (tok : EncToken)
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := scheduleToken mode tok
  input := (c.input.move .right).move .right
  work := c.work
  output := c.output

/-- Halting controller configuration that shares all tapes with `c`. -/
def controllerDoneCfg {Q : Type}
    (c : Cfg workTapeCount Q) : Cfg workTapeCount validEmitterTM.Q where
  state := controllerDone
  input := c.input
  work := c.work
  output := c.output

@[simp] theorem controllerScheduledCfg_input_head {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).input.head = c.input.head + 2 := by
  simp [controllerScheduledCfg, Tape.move]

@[simp] theorem controllerScheduledCfg_input_cells {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).input.cells = c.input.cells := by
  simp [controllerScheduledCfg, Tape.move]

@[simp] theorem controllerScheduledCfg_work {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).work = c.work := rfl

@[simp] theorem controllerScheduledCfg_output {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q) :
    (controllerScheduledCfg mode tok c).output = c.output := rfl

/-! ## The two bit-reading steps -/

/-- Read the first nonblank input bit, advancing right and preserving parked
work and output tapes. -/
theorem validEmitterTM_read_first_step_internal {Q : Type}
    (mode : StreamMode) (bit : Bool) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.ofBool bit)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerReadCfg mode c) =
      some (controllerSecondCfg mode bit c) := by
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  cases bit <;>
    simp [validEmitterTM, TM.step, controllerReadCfg, controllerSecondCfg,
      controllerRead, controllerDone, hread, Γ.ofBool]
  all_goals
    constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Read the second nonblank input bit, schedule its decoded token, advance
right, and preserve parked work and output tapes. -/
theorem validEmitterTM_read_second_step_internal {Q : Type}
    (mode : StreamMode) (first second : Bool) (c : Cfg workTapeCount Q)
    (hread : (c.input.move .right).read = Γ.ofBool second)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerSecondCfg mode first c) =
      some (controllerScheduledCfg mode (tokenOfPair first second) c) := by
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  cases second <;>
    simp [validEmitterTM, TM.step, controllerSecondCfg, controllerScheduledCfg,
      controllerRead, controllerDone, hread, Γ.ofBool]
  all_goals
    constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Reading the two concrete bits of `tok` schedules that token in exactly two
controller steps. The endpoint records exact head/cell and tape framing. -/
theorem validEmitterTM_read_token_reachesIn_internal {Q : Type}
    (mode : StreamMode) (tok : EncToken) (c : Cfg workTapeCount Q)
    (hinput : InputTokenAt c.input tok)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.reachesIn 2 (controllerReadCfg mode c)
      (controllerScheduledCfg mode tok c) := by
  have hfirst := validEmitterTM_read_first_step_internal mode
    (tokenFirstBit tok) c hinput.1 hwork hout
  have hsecond := validEmitterTM_read_second_step_internal mode
    (tokenFirstBit tok) (tokenSecondBit tok) c hinput.2 hwork hout
  rw [tokenOfPair_token_bits] at hsecond
  exact .step hfirst (.step hsecond .zero)

/-! ## Trailing blank -/

/-- A blank in first-bit mode halts the controller in one step and preserves
the input and all parked work/output tapes. -/
theorem validEmitterTM_read_blank_step_internal {Q : Type}
    (mode : StreamMode) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.step (controllerReadCfg mode c) =
      some (controllerDoneCfg c) := by
  have hinpIdle : c.input.move (TM.idleDir c.input.read) = c.input := by
    simp [hread, TM.idleDir, Tape.move]
  have hworkIdle :
      (fun i => (c.work i).writeAndMove (TM.readBackWrite (c.work i).read)
        (TM.idleDir (c.work i).read)) = c.work := by
    funext i
    exact (hwork i).writeAndMove_readBack_idle
  have houtIdle :
      c.output.writeAndMove (TM.readBackWrite c.output.read)
        (TM.idleDir c.output.read) = c.output :=
    hout.writeAndMove_readBack_idle
  simp [validEmitterTM, TM.step, controllerReadCfg, controllerDoneCfg,
    controllerRead, controllerDone, hread]
  constructor
  · simpa only [hread] using hinpIdle
  · constructor
    · simpa only [Γw.toΓ] using hworkIdle
    · simpa only [Γw.toΓ] using houtIdle

/-- Exact one-step reachability form of the first-bit blank transition. -/
theorem validEmitterTM_read_blank_reachesIn_internal {Q : Type}
    (mode : StreamMode) (c : Cfg workTapeCount Q)
    (hread : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    validEmitterTM.reachesIn 1 (controllerReadCfg mode c) (controllerDoneCfg c) :=
  .step (validEmitterTM_read_blank_step_internal mode c hread hwork hout) .zero

end Machine

end ThreeSAT

end SAT

end Complexity
