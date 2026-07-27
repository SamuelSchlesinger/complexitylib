/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Registers.InputLen
public import Complexitylib.SAT.ThreeSAT

/-!
# Machine building blocks for the CNF-to-3CNF reduction

This file starts the concrete deterministic-machine implementation of
`ThreeSAT.reduction`. The first pass is a finite-state syntax validator for
the concrete two-bit SAT encoding. No output from the transformation is
emitted before that pass succeeds. The machine then rewinds the input and can
enter a valid-input streaming emitter; malformed inputs take a fixed branch
that emits `ThreeSAT.fallbackEncoding`.

The six work tapes have fixed roles. The fresh-variable register is initialized
to `|z| + 1`, and four further registers hold the current literal and the three
pending literals used by the streaming Tseitin algorithm. This file also gives
the concrete register-copy and emission machines for committing a literal,
emitting a wide-clause link, and closing a clause. `Machine.Controller`
supplies the finite-state controller that reads validated tokens and schedules
these machines.

## Main definitions

- `ValidationState` — bit-pair syntax-validator state
- `validationTM` — concrete one-pass validation machine
- `PendingSigns` — finite-control signs for the three literal buffers
- `commitLiteralTM` — buffer or emit one decoded literal
- `closeClauseTM` — emit the completed exact-3 clause gadget
- `seedFreshTM` — initialize the fresh register to `|z| + 1`
- `reductionTMWith` — validate first, then branch to an emitter or fallback
-/

@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

/-! ## Finite-state validation -/

/-- Token-parser information retained by the regular syntax validator.

`between hasLiteral` means that no literal is currently open; `hasLiteral`
records whether the current clause already contains a completed literal.
`literal hasLiteral` means that a sign bit has been read and every subsequent
raw bit seen so far was `true`. -/
inductive ValidationMode where
  | between (hasLiteral : Bool)
  | literal (hasLiteral : Bool)
  | reject
  deriving DecidableEq, Fintype, Repr

/-- Decode one concrete pair of input bits as a SAT encoding token. -/
def tokenOfPair : Bool → Bool → EncToken
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

/-- One token transition of the syntax validator. -/
def ValidationMode.step : ValidationMode → EncToken → ValidationMode
  | .between seen, .bit _ => .literal seen
  | .between _, .litSep => .reject
  | .between _, .clauseSep => .between false
  | .literal seen, .bit true => .literal seen
  | .literal _, .bit false => .reject
  | .literal _, .litSep => .between true
  | .literal _, .clauseSep => .reject
  | .reject, _ => .reject

/-- Bit-level state: either waiting for the first or the second bit of a
two-bit token. Ending in `second` rejects odd-length inputs. -/
inductive ValidationState where
  | first (mode : ValidationMode)
  | second (mode : ValidationMode) (firstBit : Bool)
  deriving DecidableEq, Fintype, Repr

/-- Initial state of the validation scan. -/
def ValidationState.initial : ValidationState := .first (.between false)

/-- Consume one concrete input bit. -/
def ValidationState.step : ValidationState → Bool → ValidationState
  | .first mode, bit => .second mode bit
  | .second mode firstBit, bit => .first (mode.step (tokenOfPair firstBit bit))

/-- A scan accepts only between clauses, with no unfinished current clause. -/
def ValidationState.accepts : ValidationState → Bool
  | .first (.between false) => true
  | _ => false

/-- Executable finite-state validity check for concrete SAT encodings. -/
def validEncoding (z : List Bool) : Bool :=
  (z.foldl ValidationState.step ValidationState.initial).accepts

/-- Control state of `validationTM`. -/
inductive ValidationPhase where
  | scan (state : ValidationState)
  | done
  deriving DecidableEq, Fintype

/-- Scan the input from its current left boundary, returning `1` exactly when
the bit-pair syntax is a complete CNF encoding. The start-marker case lets the
same machine run both from an initial configuration and after `seedFreshTM`,
where the input is already parked at cell one. Work tapes are preserved. -/
def validationTM : TM n where
  Q := ValidationPhase
  qstart := .scan .initial
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    match phase with
    | .scan state =>
      if iHead = Γ.start then
        (.scan state, fun i => TM.readBackWrite (wHeads i), TM.readBackWrite oHead,
          .right, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      else if iHead = Γ.blank then
        (.done, fun i => TM.readBackWrite (wHeads i),
          if state.accepts then Γw.one else Γw.zero,
          TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
      else
        let bit : Bool := decide (iHead = Γ.one)
        (.scan (state.step bit), fun i => TM.readBackWrite (wHeads i),
          TM.readBackWrite oHead, .right, fun i => TM.idleDir (wHeads i),
          TM.idleDir oHead)
    | .done => TM.allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    match phase with
    | .scan _ =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
          TM.idleDir_right_of_start⟩
      · split
        · exact ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => TM.idleDir_right_of_start,
            TM.idleDir_right_of_start⟩
    | .done => exact TM.rightOfStart_allIdle iHead wHeads oHead

/-! ## Fixed work-tape layout -/

/-- Number of work tapes used by the streaming reduction. -/
abbrev workTapeCount : ℕ := 6

/-- Unary register containing the first unused auxiliary variable. -/
def freshReg : Fin workTapeCount := ⟨0, by decide⟩

/-- Unary register for the literal currently being scanned. -/
def currentReg : Fin workTapeCount := ⟨1, by decide⟩

/-- First pending-literal variable buffer. -/
def bufferAReg : Fin workTapeCount := ⟨2, by decide⟩

/-- Second pending-literal variable buffer. -/
def bufferBReg : Fin workTapeCount := ⟨3, by decide⟩

/-- Third pending-literal variable buffer. -/
def bufferCReg : Fin workTapeCount := ⟨4, by decide⟩

/-- Scratch register reserved for controller-level copies and counters. -/
def scratchReg : Fin workTapeCount := ⟨5, by decide⟩

/-- Signs of the at most three source literals buffered in finite control.
Their variable indices live in `bufferAReg`, `bufferBReg`, and `bufferCReg`. -/
inductive PendingSigns where
  | zero
  | one (a : Bool)
  | two (a b : Bool)
  | three (a b c : Bool)
  deriving DecidableEq, Fintype, Repr

/-! ## Buffer and emission phases -/

/-- Emit one encoded clause with exactly three buffered literals. -/
def emitClauseTM (aSign : Bool) (aReg : Fin workTapeCount)
    (bSign : Bool) (bReg : Fin workTapeCount)
    (cSign : Bool) (cReg : Fin workTapeCount) : TM workTapeCount :=
  TM.seqTM (TM.emitLitTM aSign aReg)
    (TM.seqTM (TM.emitLitTM bSign bReg)
      (TM.seqTM (TM.emitLitTM cSign cReg)
        (TM.emitBitsTM [true, false])))

/-- Emit the first link of a wide clause: `(a ∨ b ∨ fresh)`. -/
def emitWideLinkTM (aSign bSign : Bool) : TM workTapeCount :=
  emitClauseTM aSign bufferAReg bSign bufferBReg true freshReg

/-- Emit the exact-3 gadget for the pending clause. The empty-clause case
emits the contradictory positive/negative pair but does not yet increment
the fresh register. -/
def emitPendingTM : PendingSigns → TM workTapeCount
  | .zero =>
      TM.seqTM
        (emitClauseTM true freshReg true freshReg true freshReg)
        (emitClauseTM false freshReg false freshReg false freshReg)
  | .one a => emitClauseTM a bufferAReg a bufferAReg a bufferAReg
  | .two a b => emitClauseTM a bufferAReg b bufferBReg b bufferBReg
  | .three a b c => emitClauseTM a bufferAReg b bufferBReg c bufferCReg

/-- Clear the current-literal register and all three pending buffers. -/
def clearBuffersTM : TM workTapeCount :=
  TM.seqTM (TM.clearRegTM currentReg)
    (TM.seqTM (TM.clearRegTM bufferAReg)
      (TM.seqTM (TM.clearRegTM bufferBReg) (TM.clearRegTM bufferCReg)))

/-- Rotate the register buffers after emitting a wide-clause link.

Before the phase, the registers represent pending literals `a,b,c`, the
current register contains `d`, and `freshReg` contains `z`. Afterwards the
pending registers represent `¬z,c,d`, the fresh register contains `z+1`,
and the current register is zero. -/
def rollWideBuffersTM : TM workTapeCount :=
  TM.seqTM (TM.copyIntoTM freshReg bufferAReg)
    (TM.seqTM (TM.copyIntoTM bufferCReg bufferBReg)
      (TM.seqTM (TM.copyIntoTM currentReg bufferCReg)
        (TM.seqTM (TM.incRegTM freshReg) (TM.clearRegTM currentReg))))

/-- Finite-control update paired with `commitLiteralTM`. -/
def PendingSigns.push (pending : PendingSigns) (sign : Bool) : PendingSigns :=
  match pending with
  | .zero => .one sign
  | .one a => .two a sign
  | .two a b => .three a b sign
  | .three _ _ c => .three false c sign

/-- Commit the decoded literal in `currentReg`.

The first three literals are copied into the pending buffers. Every later
literal first emits `(a ∨ b ∨ fresh)`, then rotates the buffers to
`(¬fresh,c,current)` and increments `freshReg`. -/
def commitLiteralTM (pending : PendingSigns) : TM workTapeCount :=
  match pending with
  | .zero =>
      TM.seqTM (TM.copyIntoTM currentReg bufferAReg) (TM.clearRegTM currentReg)
  | .one _ =>
      TM.seqTM (TM.copyIntoTM currentReg bufferBReg) (TM.clearRegTM currentReg)
  | .two _ _ =>
      TM.seqTM (TM.copyIntoTM currentReg bufferCReg) (TM.clearRegTM currentReg)
  | .three a b _ =>
      TM.seqTM (emitWideLinkTM a b) rollWideBuffersTM

/-- Emit and clear the current clause. Empty clauses consume one fresh
variable; nonempty pending clauses consume no additional fresh variable. -/
def closeClauseTM (pending : PendingSigns) : TM workTapeCount :=
  let advanceFresh : TM workTapeCount :=
    match pending with
    | .zero => TM.incRegTM freshReg
    | _ => TM.skipTM
  TM.seqTM (emitPendingTM pending) (TM.seqTM advanceFresh clearBuffersTM)

/-! ## Validation-first assembly -/

/-- Initialize all tape heads, compute the source bit length in `freshReg`,
and increment it. The resulting fresh counter is exactly `|z| + 1`. -/
def seedFreshTM : TM workTapeCount :=
  TM.seqTM TM.bumpTM
    (TM.seqTM (TM.inputLenRegTM freshReg) (TM.incRegTM freshReg))

/-- Run the fresh-counter initialization followed by the syntax validator.
This is an executable front end for the reduction machine. -/
def reductionFrontEndTM : TM workTapeCount :=
  TM.seqTM seedFreshTM validationTM

/-- Blank the validator verdict at output cell one while preserving the input
and every work register. The output head remains parked at cell one, ready for
the append-only streaming emitter. -/
def clearValidationOutputTM : TM workTapeCount where
  Q := TM.BumpPhase
  qstart := .go
  qhalt := .done
  δ := fun _ iHead wHeads oHead =>
    (.done, fun i => TM.readBackWrite (wHeads i), .blank,
      TM.idleDir iHead, fun i => TM.idleDir (wHeads i), TM.idleDir oHead)
  δ_right_of_start := fun _ _ _ _ =>
    ⟨TM.idleDir_right_of_start, fun _ => TM.idleDir_right_of_start,
      TM.idleDir_right_of_start⟩

/-- Assemble the validation-first total reduction around a valid-input
streaming emitter. The validator runs before either branch emits transformed
data, and both branches clear its verdict before producing output. A valid
input is rewound to cell one and handed to `validEmitter`; an invalid input
emits the fixed no-instance `fallbackEncoding`. `Machine.Controller` supplies
the concrete valid emitter used by the final reduction machine. -/
def reductionTMWith (validEmitter : TM workTapeCount) : TM workTapeCount :=
  TM.seqTM seedFreshTM
    (TM.ifTM validationTM
      (TM.seqTM clearValidationOutputTM
        (TM.seqTM TM.rewindInputTM validEmitter))
      (TM.seqTM clearValidationOutputTM (TM.emitBitsTM fallbackEncoding)))

end Machine

end ThreeSAT

end SAT

end Complexity
