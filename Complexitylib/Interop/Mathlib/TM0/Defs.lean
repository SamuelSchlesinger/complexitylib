/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Interop.SymbolTracks
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Finite Mathlib TM0 machines with binary input and output

The source has a finite alphabet and state set. Input bits are mapped to source
symbols. A halted source configuration supplies the complete binary output at
and to the right of its tape head. The CSLib simulator copies and rewinds its
input, simulates each source transition on symbol tracks, then emits that output.
-/

@[expose] public section

namespace Complexity.MathlibTM0

/-- A finite Mathlib machine with a faithful binary encoding of its input and output. -/
structure BinaryMachine where
  /-- Source tape alphabet. -/
  Alphabet : Type
  /-- Source control states. -/
  State : Type
  /-- The tape alphabet is finite. -/
  [alphabetFinite : Fintype Alphabet]
  /-- The default symbol is blank. -/
  [alphabetInhabited : Inhabited Alphabet]
  /-- The control state set is finite. -/
  [stateFinite : Fintype State]
  /-- The default control state is initial. -/
  [stateInhabited : Inhabited State]
  /-- Encode an input or output bit as a source symbol. -/
  bit : Bool → Alphabet
  /-- Decode an output bit, stopping on a nonbinary symbol. -/
  readBit : Alphabet → Option Bool
  /-- Encoded bits decode faithfully. -/
  readBit_bit : ∀ b, readBit (bit b) = some b
  /-- Blank terminates the output. -/
  readBit_blank : readBit default = none
  /-- The source transition function. -/
  code : Turing.TM0.Machine Alphabet State

attribute [instance] BinaryMachine.alphabetFinite BinaryMachine.alphabetInhabited
  BinaryMachine.stateFinite BinaryMachine.stateInhabited

namespace BinaryMachine

/-- A configuration of the source machine. -/
abbrev Config (M : BinaryMachine) := Turing.TM0.Cfg M.Alphabet M.State

/-- One transition, using the alphabet and initial-state instances of the bundle. -/
abbrev step (M : BinaryMachine) : M.Config → Option M.Config := Turing.TM0.step M.code

/-- Run exactly the given number of source transitions, failing if a step is unavailable. -/
def run (M : BinaryMachine) : ℕ → M.Config → Option M.Config
  | 0, c => some c
  | t + 1, c => (M.step c).bind (M.run t)

/-- A halted source run whose entire right-of-head tape is the encoded binary output. -/
def OutputsWithin (M : BinaryMachine) (input output : List Bool) (time : ℕ) : Prop :=
  ∃ t ≤ time, ∃ c : M.Config,
    M.run t (Turing.TM0.init (input.map M.bit)) = some c ∧
    M.step c = none ∧
    c.Tape.right₀ = Turing.ListBlank.mk (output.map M.bit)

end BinaryMachine

/-- Simulator phases: input copying, rewind, source execution, and output emission. -/
inductive Control (Q : Type*) where
  /-- Copy input bits to symbol tracks. -/
  | copy
  /-- Rewind the symbol tracks to the first input cell. -/
  | rewind
  /-- Execute one source control state. -/
  | run : Q → Control Q
  /-- Emit the binary output at and right of the halted source head. -/
  | emit
  deriving Fintype

/-- One binary work tape per source alphabet symbol. -/
abbrev Track (M : BinaryMachine) := Fin (Fintype.card M.Alphabet)

/-- Associate each work tape with its source alphabet symbol. -/
noncomputable def trackEquiv (M : BinaryMachine) : Track M ≃ M.Alphabet :=
  (Fintype.equivFin _).symm

/-- A transition leaving the work tapes unchanged. -/
def idle (M : BinaryMachine) (state : Option (Control M.State))
    (output : Option Bool) (inputMove : SignType) :
    Turing.Action (Fintype.card M.Alphabet) Bool (Control M.State) where
  state := state
  inputTape := inputMove
  output := output
  workTapes := fun _ => (none, 0)

/-- The displacement corresponding to one source move. -/
def moveSign : Turing.Dir → SignType
  | .left => .neg
  | .right => .pos

/-- Simulate a source transition, switching to output emission when the source halts. -/
noncomputable def runAction (M : BinaryMachine) (q : M.State)
    (work : Track M → Option Bool) :
    Turing.Action (Fintype.card M.Alphabet) Bool (Control M.State) :=
  match M.code q (SymbolTracks.decode (fun a => work ((trackEquiv M).symm a))) with
  | none => idle M (some .emit) none 0
  | some (q', .move d) =>
      { state := some (.run q'), inputTape := 0, output := none,
        workTapes := fun _ => (none, moveSign d) }
  | some (q', .write a) =>
      { state := some (.run q'), inputTape := 0, output := none,
        workTapes := fun i => (some (SymbolTracks.encode a (trackEquiv M i)), 0) }

/-- The finite binary CSLib simulator. -/
noncomputable def machine (M : BinaryMachine) :
    Turing.MultiTapeTM (Fintype.card M.Alphabet) Bool (Control M.State) where
  q₀ := .copy
  tr q input work := match q with
    | .run q => runAction M q work
    | .copy => match input with
      | none => idle M (some .rewind) none (-1)
      | some b =>
          { state := some .copy, inputTape := 1, output := none,
            workTapes := fun i => (some (SymbolTracks.encode (M.bit b) (trackEquiv M i)), 1) }
    | .rewind => match input with
      | none => idle M (some (.run default)) none 0
      | some _ =>
          { state := some .rewind, inputTape := -1, output := none,
            workTapes := fun _ => (none, -1) }
    | .emit =>
        match M.readBit (SymbolTracks.decode (fun a => work ((trackEquiv M).symm a))) with
        | none => idle M none none 0
        | some b =>
            { state := some .emit, inputTape := 0, output := some b,
              workTapes := fun _ => (none, 1) }

end Complexity.MathlibTM0
