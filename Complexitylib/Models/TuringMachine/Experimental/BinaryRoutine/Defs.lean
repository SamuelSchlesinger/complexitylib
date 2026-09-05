/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.Machine.GateStream.Defs
public import Complexitylib.Models.TuringMachine.Hoare.Space.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred.Defs
public import Complexitylib.Circuits.Encoding.Defs

/-!
# Proof-carrying binary stream routines -- definitions

A binary routine operates on a vector of natural numbers represented by
canonical rewound `Nat.bits` tapes. It may update that pure vector and append a
value-dependent word to an output accumulator. A value-level precondition
supports honest partial leaves such as positive predecessor and zero-scratch
copying without weakening the canonical state model.
-/


@[expose] public section

namespace Complexity

/-- Pure values represented by all work tapes of a binary routine. -/
abbrev BinaryValues (n : ℕ) := Fin n → ℕ

namespace BinaryRoutine

/-- Canonical rewound tape representation of one natural number. -/
def natTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

/-- Canonical work-tape vector corresponding to `values`. -/
def workTapes (values : BinaryValues n) : Fin n → Tape :=
  fun i => natTape (values i)

/-- A fixed parked input, canonical binary work vector, and append accumulator. -/
def CanonicalPred (inp₀ : Tape) (values : BinaryValues n)
    (ys : List Bool) : TapePred n :=
  TM.EmitPred inp₀ (workTapes values) ys

end BinaryRoutine

/-- A concrete streaming machine paired with its pure value effect, emitted
word, domain, and explicit time/all-prefix-space bounds. -/
structure BinaryRoutine (n : ℕ) where
  /-- Concrete machine implementing the routine. -/
  machine : TM n
  /-- Pure value-level domain on which the routine contract holds. -/
  requires : BinaryValues n → Prop
  /-- Exact pure work-vector effect. -/
  effect : BinaryValues n → BinaryValues n
  /-- Exact word appended from each starting value vector. -/
  emitted : BinaryValues n → List Bool
  /-- Time bound from each starting value vector. -/
  timeBound : BinaryValues n → ℕ
  /-- All-prefix auxiliary-space bound from an initial work budget. -/
  spaceBound : ℕ → BinaryValues n → ℕ

namespace BinaryRoutine

/-- Soundness of a proof-carrying routine on every canonical state in its
value-level domain. The input tape is fixed and parked for each invocation;
`initialSpace ≥ 1` covers the canonical work heads at cell one. -/
structure Sound (routine : BinaryRoutine n) : Prop where
  /-- Exact endpoint, time, and all-reachable space contract. -/
  hoareTimeSpace : ∀ values inp₀ ys inputLength initialSpace,
    routine.requires values →
    TM.Parked inp₀ →
    1 ≤ initialSpace →
    inp₀.head ≤ inputLength + initialSpace + 1 →
    routine.machine.HoareTimeSpace
      (CanonicalPred inp₀ values ys)
      (CanonicalPred inp₀ (routine.effect values)
        (ys ++ routine.emitted values))
      (routine.timeBound values) inputLength
      (routine.spaceBound initialSpace values)
  /-- The routine never moves its output head left. -/
  isTransducer : routine.machine.IsTransducer

/-- Append a fixed word without changing the binary work vector. -/
def emitBits (word : List Bool) : BinaryRoutine n where
  machine := TM.emitBitsTM word
  requires := fun _ => True
  effect := id
  emitted := fun _ => word
  timeBound := fun _ => word.length
  spaceBound := fun initialSpace _ => initialSpace + word.length

/-- Empty fixed-word emission is the canonical routine identity. -/
def identity : BinaryRoutine n :=
  emitBits []

/-- Sequential composition, including the concrete `seqTM` seam step. -/
def seq (first second : BinaryRoutine n) : BinaryRoutine n where
  machine := TM.seqTM first.machine second.machine
  requires := fun values =>
    first.requires values ∧ second.requires (first.effect values)
  effect := fun values => second.effect (first.effect values)
  emitted := fun values =>
    first.emitted values ++ second.emitted (first.effect values)
  timeBound := fun values =>
    first.timeBound values + 1 + second.timeBound (first.effect values)
  spaceBound := fun initialSpace values =>
    max (first.spaceBound initialSpace values)
      (second.spaceBound initialSpace (first.effect values))

/-- Replace a routine's public pure precondition while preserving its concrete
machine, effect, emitted word, and resource bounds exactly. Soundness requires
the replacement precondition to imply the original one. -/
def restrict (routine : BinaryRoutine n)
    (newRequires : BinaryValues n → Prop) : BinaryRoutine n :=
  { routine with requires := newRequires }

/-- Increment one canonical binary work value. -/
def binarySucc (idx : Fin n) : BinaryRoutine n where
  machine := TM.binarySuccTM idx
  requires := fun _ => True
  effect := fun values => Function.update values idx (values idx + 1)
  emitted := fun _ => []
  timeBound := fun values => TM.binarySuccTime (values idx)
  spaceBound := fun initialSpace values =>
    initialSpace + TM.binarySuccTime (values idx)

/-- Decrement one positive canonical binary work value. -/
def binaryPred (idx : Fin n) : BinaryRoutine n where
  machine := TM.binaryPredTM idx
  requires := fun values => 0 < values idx
  effect := fun values => Function.update values idx (values idx - 1)
  emitted := fun _ => []
  timeBound := fun values => TM.binaryPredTime (values idx - 1)
  spaceBound := fun initialSpace values =>
    TM.binaryPredSpace initialSpace (values idx - 1)

/-- Copy one canonical binary value into another using a zero scratch counter. -/
def binaryCopy (srcIdx dstIdx counterIdx : Fin n) : BinaryRoutine n where
  machine := TM.binaryCopyIntoTM srcIdx dstIdx counterIdx
  requires := fun values =>
    srcIdx ≠ dstIdx ∧ srcIdx ≠ counterIdx ∧ dstIdx ≠ counterIdx ∧
      values counterIdx = 0
  effect := fun values => Function.update values dstIdx (values srcIdx)
  emitted := fun _ => []
  timeBound := fun values => TM.binaryCopyTime (values srcIdx) (values dstIdx)
  spaceBound := fun initialSpace values =>
    TM.binaryCopySpace initialSpace (values srcIdx) (values dstIdx)

/-- Emit one raw gate and advance the first-unused-wire value. -/
def emitRawGateStep
    (op : AndOrOp) (negated₀ negated₁ : Bool)
    (emitCounterIdx availableIdx input₀Idx input₁Idx : Fin n) :
    BinaryRoutine n where
  machine := CircuitCode.Machine.emitRawGateStepTM op negated₀ negated₁
    emitCounterIdx availableIdx input₀Idx input₁Idx
  requires := fun values =>
    CircuitCode.Machine.RawGateStepDistinct emitCounterIdx availableIdx
      input₀Idx input₁Idx ∧ values emitCounterIdx = 0
  effect := fun values =>
    Function.update values availableIdx (values availableIdx + 1)
  emitted := fun values => CircuitCode.RawGate.encode
    { op := op
      input₀ := values input₀Idx
      input₁ := values input₁Idx
      negated₀ := negated₀
      negated₁ := negated₁ }
  timeBound := fun values => CircuitCode.Machine.emitRawGateStepTime
    (values availableIdx) (values input₀Idx) (values input₁Idx)
  spaceBound := fun initialSpace values =>
    CircuitCode.Machine.emitRawGateStepSpace initialSpace
      (values availableIdx) (values input₀Idx) (values input₁Idx)

end BinaryRoutine

end Complexity
