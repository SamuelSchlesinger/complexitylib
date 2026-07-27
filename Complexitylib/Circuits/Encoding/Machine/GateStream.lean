/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.GateStream.Defs
public import Complexitylib.Circuits.Encoding.Machine.GateStream.Internal

/-!
# One streaming raw-gate step

This module exposes the atomic operation of an append-only raw-circuit
serializer: emit one encoded gate from preserved binary references and advance
the binary first-unused-wire counter by one. The emitter's private counter is
restored to zero and every other tape is preserved literally.

## Main results

- `emitRawGateStepTM_hoareTime` gives exact output and wire-counter effects.
- `emitRawGateStepTM_hoareTimeSpace` adds an all-prefix width bound.
- `emitRawGateStepTM_isTransducer` proves append-only-output safety.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

/-- Emit one encoded gate and advance `availableIdx`; all other tapes,
including both references and the zero emitter counter, are restored literally. -/
theorem emitRawGateStepTM_hoareTime
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    (hdistinct : RawGateStepDistinct emitCounterIdx availableIdx input₀Idx
      input₁Idx)
    (available input₀ input₁ : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hemitCounter : (work₀ emitCounterIdx).HasBinaryNat 0)
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ emitCounterIdx → i ≠ availableIdx →
      i ≠ input₀Idx → i ≠ input₁Idx → Parked (work₀ i)) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          ((Tape.init ((available + 1).bits.map Γ.ofBool)).move Dir3.right))
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateStepTime available input₀ input₁) :=
  emitRawGateStepTM_hoareTime_internal op negated₀ negated₁
    emitCounterIdx availableIdx input₀Idx input₁Idx hdistinct available
    input₀ input₁ inp₀ work₀ ys hinp hemitCounter havailable hinput₀
    hinput₁ hother

/-- Time-and-space form of one streaming gate step. -/
theorem emitRawGateStepTM_hoareTimeSpace
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n)
    (hdistinct : RawGateStepDistinct emitCounterIdx availableIdx input₀Idx
      input₁Idx)
    (available input₀ input₁ inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hemitCounter : (work₀ emitCounterIdx).HasBinaryNat 0)
    (havailable : (work₀ availableIdx).HasBinaryNat available)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ emitCounterIdx → i ≠ availableIdx →
      i ≠ input₀Idx → i ≠ input₁Idx → Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀
        (Function.update work₀ availableIdx
          ((Tape.init ((available + 1).bits.map Γ.ofBool)).move Dir3.right))
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateStepTime available input₀ input₁) inputLength
      (emitRawGateStepSpace initialSpace available input₀ input₁) :=
  emitRawGateStepTM_hoareTimeSpace_internal op negated₀ negated₁
    emitCounterIdx availableIdx input₀Idx input₁Idx hdistinct available
    input₀ input₁ inputLength initialSpace inp₀ work₀ ys hinp
    hemitCounter havailable hinput₀ hinput₁ hother hworkSpace hinputSpace

/-- A streaming gate step never moves the output head left. -/
theorem emitRawGateStepTM_isTransducer
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateStepTM op negated₀ negated₁ emitCounterIdx availableIdx
      input₀Idx input₁Idx).IsTransducer :=
  emitRawGateStepTM_isTransducer_internal op negated₀ negated₁
    emitCounterIdx availableIdx input₀Idx input₁Idx

end Machine

end CircuitCode

end Complexity
