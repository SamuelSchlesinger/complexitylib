/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs

/-!
# Experimental first-order Turing-machine routines — definitions

This module provides a deliberately small authoring layer over the existing
executable Turing-machine combinators. A routine is either a call to a concrete
machine, sequential composition, or a read-only-input loop. `Routine.lower`
compiles the syntax structurally through `TM.seqTM` and `TM.forInputTM`, so the
concrete `TM` remains the semantic and resource-accounting ground truth.

`Routine.TransducerSafe` is an explicit certificate that every called machine
obeys the one-way-output discipline. Its name deliberately does not suggest
input preservation, termination, or resource safety.
-/

@[expose] public section

namespace Complexity

namespace TM

namespace Experimental

/-- An experimental first-order routine assembled from concrete machine calls
and existing machine combinators. -/
inductive Routine (n : ℕ) where
  /-- Invoke one concrete machine. -/
  | call (machine : TM n)
  /-- Run two routines sequentially on the same named tapes. -/
  | seq (first second : Routine n)
  /-- Run a routine once per Boolean input symbol, subject to the body's
  input-preservation contract at the proof layer. -/
  | forInput (body : Routine n)

namespace Routine

/-- Compile a first-order routine to the concrete Turing-machine model using
the existing executable combinators. -/
def lower : Routine n → TM n
  | .call machine => machine
  | .seq first second => seqTM first.lower second.lower
  | .forInput body => forInputTM body.lower

/-- Proof-carrying one-way-output safety for routines. Leaf calls expose the
concrete `TM.IsTransducer` obligation; composition certificates are structural. -/
inductive TransducerSafe : Routine n → Prop where
  /-- A concrete call is transducer-safe when the called machine is a transducer. -/
  | call {machine : TM n} (h : machine.IsTransducer) : TransducerSafe (.call machine)
  /-- Sequential composition is transducer-safe when both routines are. -/
  | seq {first second : Routine n}
      (hfirst : TransducerSafe first) (hsecond : TransducerSafe second) :
      TransducerSafe (.seq first second)
  /-- An input loop is transducer-safe when its body routine is. -/
  | forInput {body : Routine n} (hbody : TransducerSafe body) :
      TransducerSafe (.forInput body)

end Routine

end Experimental

end TM

end Complexity
