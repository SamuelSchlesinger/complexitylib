/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Family
public import Complexitylib.Models.TuringMachine.Lift
public import Complexitylib.Models.TuringMachine.Subroutines
public import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.PairValidate.Defs
public import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Serialized circuit-evaluator machine front end

Definitions for validating one self-delimiting input `pair code input` and
staging its two components on three work tapes. The higher-order dispatcher
places an evaluator core inside the valid branch, so malformed outer inputs
can never fall through into that core.
-/

@[expose] public section

namespace Complexity

namespace CircuitCode

/-- The language decided by evaluating a paired tagged-family code and input.
Malformed outer pairs and malformed inner codes are rejected. -/
def circuitEvalLanguage : Language :=
  {z | evalFamilyPair? z = some true}

namespace Machine

/-- The serialized circuit evaluator uses three work tapes. -/
abbrev workTapeCount : ℕ := 3

/-- Work tape containing the tagged family code after staging. -/
def codeIdx : Fin workTapeCount := ⟨0, by decide⟩

/-- Work tape containing the primary input and, later, memoized wire values. -/
def wiresIdx : Fin workTapeCount := ⟨1, by decide⟩

/-- Work tape reserved for the evaluator's unary gate counter. -/
def counterIdx : Fin workTapeCount := ⟨2, by decide⟩

/-- Rewind a validated paired input and split its two components onto the code
and wire tapes. This machine assumes the outer input is canonical. -/
def validPairStageTM : TM workTapeCount :=
  TM.seqTM (TM.rewindInputTM (n := workTapeCount))
    (TM.pairSplitCoreTM codeIdx wiresIdx)

/-- Validate and stage a paired input. Malformed inputs take a frame-preserving
rewind branch and retain the validator's zero verdict. -/
def pairStageTM : TM workTapeCount :=
  TM.ifTM (TM.pairValidateTM.liftTM workTapeCount)
    validPairStageTM (TM.rewindInputTM (n := workTapeCount))

/-- Validate and stage a paired input before invoking `core`. The core occurs
inside the valid branch, so it is unreachable on malformed outer inputs. -/
def evalFamilyTMWith (core : TM workTapeCount) : TM workTapeCount :=
  TM.ifTM (TM.pairValidateTM.liftTM workTapeCount)
    (TM.seqTM validPairStageTM core)
    (TM.rewindInputTM (n := workTapeCount))

/-- Concrete front-end bound derived from the current validator, rewind,
splitter, and conditional-composition contracts. -/
def pairStageTime (inputLength : ℕ) : ℕ :=
  4 * inputLength + 16

/-- Front-end overhead when the valid branch additionally invokes a core with
the supplied time bound. -/
def evalFamilyTMWithTime (inputLength coreTime : ℕ) : ℕ :=
  4 * inputLength + coreTime + 17

/-- Fresh machine tapes before validation begins. -/
def PairStagePre (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp = Tape.init (bits.map Γ.ofBool) ∧
  work = (fun _ => Tape.init []) ∧
  out = Tape.init []

/-- Auditable result of the pair-staging front end. The output is parked at
cell one with its start invariant intact, so a later core can safely overwrite
the staging verdict. Invalid encodings retain fresh work tapes and a zero
verdict. Valid encodings expose appendable code and wire prefixes, including
the left markers needed by later rewind proofs. -/
def PairStagePost (bits : List Bool) (inp : Tape)
    (work : Fin workTapeCount → Tape) (out : Tape) : Prop :=
  inp.cells = (Tape.init (bits.map Γ.ofBool)).cells ∧
  out.head = 1 ∧
  out.StartInvariant ∧
  match unpair? bits with
  | none =>
      inp.head = 1 ∧
      (∀ i, work i = (Tape.init []).move Dir3.right) ∧
      out.cells 1 = Γ.zero
  | some (code, input) =>
      inp.head = bits.length + 1 ∧
      (work codeIdx).cells 0 = Γ.start ∧
      (work codeIdx).HasBinaryPrefix code ∧
      (work wiresIdx).cells 0 = Γ.start ∧
      (work wiresIdx).HasBinaryPrefix input ∧
      work counterIdx = (Tape.init []).move Dir3.right ∧
      out.cells 1 = Γ.one

end Machine

end CircuitCode

end Complexity
