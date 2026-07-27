/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Machine.RawGate.Defs
public import Complexitylib.Circuits.Encoding.Machine.RawGate.Internal

/-!
# Machine emission of raw circuit gates

This module exposes a serializer leaf for append-only tableau generators.  A
fixed operation-and-negation header is followed by two terminated-unary wire
references read from canonical binary work tapes.  The input, all work tapes,
and the reusable zero scratch are restored literally.

## Main results

- `emitRawGateTM_hoareTime` appends exactly one `RawGate.encode` word.
- `emitRawGateTM_hoareTimeSpace` adds an all-prefix auxiliary-space bound.
- `emitRawGateTM_isTransducer` proves one-way-output safety.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

namespace Machine

open TM

variable {n : ℕ}

/-- Emit one complete raw-gate code from two preserved binary references,
restoring the zero scratch and complete external frame. -/
theorem emitRawGateTM_hoareTime
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ counterIdx → i ≠ input₀Idx → i ≠ input₁Idx →
      Parked (work₀ i)) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).HoareTime
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateTime input₀ input₁) :=
  emitRawGateTM_hoareTime_internal op negated₀ negated₁ counterIdx
    input₀Idx input₁Idx hcounterInput₀ hcounterInput₁ input₀ input₁
    inp₀ work₀ ys hinp hcounter hinput₀ hinput₁ hother

/-- Time-and-space form of `emitRawGateTM_hoareTime`. -/
theorem emitRawGateTM_hoareTimeSpace
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n)
    (hcounterInput₀ : counterIdx ≠ input₀Idx)
    (hcounterInput₁ : counterIdx ≠ input₁Idx)
    (input₀ input₁ inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (ys : List Bool)
    (hinp : Parked inp₀)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinput₀ : (work₀ input₀Idx).HasBinaryNat input₀)
    (hinput₁ : (work₀ input₁Idx).HasBinaryNat input₁)
    (hother : ∀ i, i ≠ counterIdx → i ≠ input₀Idx → i ≠ input₁Idx →
      Parked (work₀ i))
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).HoareTimeSpace
      (EmitPred inp₀ work₀ ys)
      (EmitPred inp₀ work₀
        (ys ++ RawGate.encode
          { op := op
            input₀ := input₀
            input₁ := input₁
            negated₀ := negated₀
            negated₁ := negated₁ }))
      (emitRawGateTime input₀ input₁) inputLength
      (emitRawGateSpace initialSpace input₀ input₁) :=
  emitRawGateTM_hoareTimeSpace_internal op negated₀ negated₁ counterIdx
    input₀Idx input₁Idx hcounterInput₀ hcounterInput₁ input₀ input₁
    inputLength initialSpace inp₀ work₀ ys hinp hcounter hinput₀ hinput₁
    hother hworkSpace hinputSpace

/-- Raw-gate emission never moves its output head left. -/
theorem emitRawGateTM_isTransducer
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (counterIdx input₀Idx input₁Idx : Fin n) :
    (emitRawGateTM op negated₀ negated₁ counterIdx input₀Idx
      input₁Idx).IsTransducer :=
  emitRawGateTM_isTransducer_internal op negated₀ negated₁ counterIdx
    input₀Idx input₁Idx

end Machine

end CircuitCode

end Complexity
