/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Registers.Emit

/-!
# Experimental effect contracts for emitter machines

`TM.Experimental.EmitSpec` packages the common endpoint effect of a machine
that preserves a parked input tape, tracks exact before/after work-tape
families, and updates an output accumulator. Its sequencing rule owns the
parked phase-boundary proof required by `TM.seqTM_hoareTime`.

This is deliberately an endpoint-and-time-bound contract. It does not claim an
exact running time, all-reachable auxiliary-space safety, or structural
transducer safety. In particular, it does not assert that the final output
extends the initial output; callers needing append-only behavior must prove
that separately.

This contract complements `TM.bigSeqTM_hoareTime`: that theorem handles an
indexed list fold with one uniform per-stage bound, while `EmitSpec` handles
short heterogeneous machine trees and retains each stage's structural bound.
-/

@[expose] public section

namespace Complexity

namespace TM

namespace Experimental

/-- A concrete machine contract with exact before/after tape families and an
upper time bound. The parked endpoint facts are precisely what sequential
composition needs at the next phase boundary. -/
structure EmitSpec (machine : TM n) (input : Tape)
    (beforeWork afterWork : Fin n → Tape)
    (beforeOutput afterOutput : List Bool) (time : ℕ) : Prop where
  /-- The fixed input is stable across combinator phase transitions. -/
  inputParked : Parked input
  /-- Every work tape at the endpoint is stable across the next phase
  transition. -/
  afterWorkParked : ∀ i, Parked (afterWork i)
  /-- The machine realizes the stated endpoint effect within the supplied time
  bound. -/
  hoareTime : machine.HoareTime
    (EmitPred input beforeWork beforeOutput)
    (EmitPred input afterWork afterOutput) time

/-- Package one concrete machine's endpoint-and-time contract. -/
theorem EmitSpec.ofHoareTime {machine : TM n} {input : Tape}
    {beforeWork afterWork : Fin n → Tape}
    {beforeOutput afterOutput : List Bool} {time : ℕ}
    (inputParked : Parked input)
    (afterWorkParked : ∀ i, Parked (afterWork i))
    (hoareTime : machine.HoareTime
      (EmitPred input beforeWork beforeOutput)
      (EmitPred input afterWork afterOutput) time) :
    EmitSpec machine input beforeWork afterWork
      beforeOutput afterOutput time :=
  ⟨inputParked, afterWorkParked, hoareTime⟩

/-- Compose two emitter effects. The intermediate parked frame discharges the
concrete `seqTM` transition seam, and the resulting bound includes that real
one-step phase change. -/
theorem EmitSpec.seq {first second : TM n} {input : Tape}
    {startWork middleWork endWork : Fin n → Tape}
    {startOutput middleOutput endOutput : List Bool}
    {firstTime secondTime : ℕ}
    (hfirst : EmitSpec first input startWork middleWork
      startOutput middleOutput firstTime)
    (hsecond : EmitSpec second input middleWork endWork
      middleOutput endOutput secondTime) :
    EmitSpec (seqTM first second) input startWork endWork
      startOutput endOutput (firstTime + 1 + secondTime) where
  inputParked := hfirst.inputParked
  afterWorkParked := hsecond.afterWorkParked
  hoareTime := seqTM_hoareTime first second hfirst.hoareTime
    (emitPred_transition hfirst.inputParked hfirst.afterWorkParked middleOutput)
    hsecond.hoareTime

end Experimental

end TM

end Complexity
