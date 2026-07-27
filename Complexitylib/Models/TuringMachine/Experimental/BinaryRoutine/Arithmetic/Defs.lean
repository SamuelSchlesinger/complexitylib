/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPolynomial.Defs

/-!
# Arithmetic leaves for proof-carrying binary routines -- definitions

These adapters expose the remaining framed binary subroutines through the
pure value-vector interface. Static index separation and reusable-zero
requirements remain explicit in `BinaryRoutine.requires`.
-/

@[expose] public section

namespace Complexity

namespace BinaryRoutine

/-- Clear one canonical binary work value to zero. -/
def clear (idx : Fin n) : BinaryRoutine n where
  machine := TM.clearWorkTM idx
  requires := fun _ => True
  effect := fun values => Function.update values idx 0
  emitted := fun _ => []
  timeBound := fun values => TM.clearWorkTimeBound (values idx).bits.length
  spaceBound := fun initialSpace values =>
    initialSpace + TM.clearWorkTimeBound (values idx).bits.length

/-- Add one hardwired natural to a canonical binary value. -/
def addConst (idx : Fin n) (constant : ℕ) : BinaryRoutine n where
  machine := TM.binaryAddConstTM idx constant
  requires := fun _ => True
  effect := fun values =>
    Function.update values idx (values idx + constant)
  emitted := fun _ => []
  timeBound := fun values => TM.binaryAddConstTime constant (values idx)
  spaceBound := fun initialSpace values =>
    TM.binaryAddConstSpace initialSpace constant (values idx)

/-- Replace one canonical binary value by a hardwired natural. -/
def set (idx : Fin n) (value : ℕ) : BinaryRoutine n :=
  seq (clear idx) (addConst idx value)

/-- Add a preserved source into a destination and restore a private counter. -/
def add (srcIdx dstIdx counterIdx : Fin n) : BinaryRoutine n where
  machine := TM.binaryAddIntoTM srcIdx dstIdx counterIdx
  requires := fun values =>
    srcIdx ≠ dstIdx ∧ srcIdx ≠ counterIdx ∧ dstIdx ≠ counterIdx ∧
      values counterIdx = 0
  effect := fun values =>
    Function.update values dstIdx (values dstIdx + values srcIdx)
  emitted := fun _ => []
  timeBound := fun values => TM.binaryAddTime (values srcIdx) (values dstIdx)
  spaceBound := fun initialSpace values =>
    TM.binaryAddSpace initialSpace (values srcIdx) (values dstIdx)

/-- Add the product of two preserved values into an accumulator and restore
both private counters. -/
def mulAdd (leftIdx rightIdx accIdx mulCounterIdx addCounterIdx : Fin n) :
    BinaryRoutine n where
  machine := TM.binaryMulAddIntoTM leftIdx rightIdx accIdx mulCounterIdx
    addCounterIdx
  requires := fun values =>
    TM.BinaryMulAddDistinct leftIdx rightIdx accIdx mulCounterIdx
      addCounterIdx ∧ values mulCounterIdx = 0 ∧ values addCounterIdx = 0
  effect := fun values => Function.update values accIdx
    (values accIdx + values leftIdx * values rightIdx)
  emitted := fun _ => []
  timeBound := fun values =>
    TM.binaryMulAddTime (values leftIdx) (values rightIdx) (values accIdx)
  spaceBound := fun initialSpace values =>
    TM.binaryMulAddSpace initialSpace (values leftIdx) (values rightIdx)
      (values accIdx)

/-- Evaluate one fixed natural polynomial from a preserved input into a zero
result tape, restoring the alternate accumulator and both counters. -/
noncomputable def evalPolynomial
    (inputIdx resultIdx scratchIdx mulCounterIdx addCounterIdx : Fin n)
    (p : Polynomial ℕ) : BinaryRoutine n where
  machine := TM.binaryPolynomialEvalTM inputIdx resultIdx scratchIdx
    mulCounterIdx addCounterIdx p
  requires := fun values =>
    TM.BinaryPolynomialDistinct inputIdx resultIdx scratchIdx mulCounterIdx
      addCounterIdx ∧ values resultIdx = 0 ∧ values scratchIdx = 0 ∧
      values mulCounterIdx = 0 ∧ values addCounterIdx = 0
  effect := fun values => Function.update values resultIdx (p.eval (values inputIdx))
  emitted := fun _ => []
  timeBound := fun values => TM.binaryPolynomialTime p (values inputIdx)
  spaceBound := fun initialSpace values =>
    TM.binaryPolynomialSpace initialSpace p (values inputIdx)

/-- Emit the terminated-unary code of a preserved value, restoring the zero
scratch counter and leaving all pure values unchanged. -/
def emitNatCode (counterIdx valueIdx : Fin n) : BinaryRoutine n where
  machine := CircuitCode.Machine.emitNatCodeTM counterIdx valueIdx
  requires := fun values =>
    counterIdx ≠ valueIdx ∧ values counterIdx = 0
  effect := id
  emitted := fun values => CircuitCode.NatCode.encode (values valueIdx)
  timeBound := fun values => CircuitCode.Machine.emitNatCodeTime (values valueIdx)
  spaceBound := fun initialSpace values =>
    CircuitCode.Machine.emitNatCodeSpace initialSpace (values valueIdx)

/-- Emit one raw gate without advancing any pure value. This is the loop body
used when the surrounding binary driver itself advances the wire frontier. -/
def emitRawGate
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx input₀Idx input₁Idx : Fin n) : BinaryRoutine n where
  machine := CircuitCode.Machine.emitRawGateTM op negated₀ negated₁
    emitCounterIdx input₀Idx input₁Idx
  requires := fun values =>
    emitCounterIdx ≠ input₀Idx ∧ emitCounterIdx ≠ input₁Idx ∧
      values emitCounterIdx = 0
  effect := id
  emitted := fun values => CircuitCode.RawGate.encode
    { op := op
      input₀ := values input₀Idx
      input₁ := values input₁Idx
      negated₀ := negated₀
      negated₁ := negated₁ }
  timeBound := fun values => CircuitCode.Machine.emitRawGateTime
    (values input₀Idx) (values input₁Idx)
  spaceBound := fun initialSpace values =>
    CircuitCode.Machine.emitRawGateSpace initialSpace (values input₀Idx)
      (values input₁Idx)

end BinaryRoutine

end Complexity
