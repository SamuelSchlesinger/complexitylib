/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.RawGate.Defs

/-!
# One streaming raw-gate step

This definitions layer couples raw-gate code emission with incrementing the
binary counter that records the first unused circuit wire. It is the atomic
append operation used by circuit serializers.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

/-- Separation conditions for the mutable first-unused-wire counter, the
emitter's zero scratch, and its two preserved reference tapes. The two
references may coincide, which is useful for copy and constant gates. -/
structure RawGateStepDistinct {n : ℕ}
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) : Prop where
  /-- The emitter scratch is not the first-unused-wire counter. -/
  emitCounter_ne_available : emitCounterIdx ≠ availableIdx
  /-- The emitter scratch is not the first reference. -/
  emitCounter_ne_input₀ : emitCounterIdx ≠ input₀Idx
  /-- The emitter scratch is not the second reference. -/
  emitCounter_ne_input₁ : emitCounterIdx ≠ input₁Idx
  /-- The mutable wire counter is not the first preserved reference. -/
  available_ne_input₀ : availableIdx ≠ input₀Idx
  /-- The mutable wire counter is not the second preserved reference. -/
  available_ne_input₁ : availableIdx ≠ input₁Idx

/-- Emit one raw gate from two binary reference tapes, then increment the
canonical binary first-unused-wire counter. -/
def emitRawGateStepTM {n : ℕ}
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) : TM n :=
  TM.seqTM
    (emitRawGateTM op negated₀ negated₁ emitCounterIdx input₀Idx
      input₁Idx)
    (TM.binarySuccTM availableIdx)

/-- Compositional running-time bound for one streaming gate step. -/
def emitRawGateStepTime (available input₀ input₁ : ℕ) : ℕ :=
  emitRawGateTime input₀ input₁ + 1 + TM.binarySuccTime available

/-- All-prefix space bound for one streaming gate step. -/
def emitRawGateStepSpace
    (initialSpace available input₀ input₁ : ℕ) : ℕ :=
  max (emitRawGateSpace initialSpace input₀ input₁)
    (initialSpace + TM.binarySuccTime available)

end Machine

end CircuitCode

end Complexity
