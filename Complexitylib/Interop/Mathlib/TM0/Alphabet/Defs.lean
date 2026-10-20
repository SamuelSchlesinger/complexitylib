/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
public import Complexitylib.Encoding.FiniteAlphabet.Defs
public import Complexitylib.Interop.Mathlib.TM0.Marked.Defs

/-!
# Marked tape computations over finite input and output alphabets

The binary simulator parses explicit finite-alphabet codewords before writing
source cells. It rejects malformed codes before starting the source. Source
execution reuses symbol tracks, and output emission writes complete codewords.
Input and output alphabets and their chosen numberings are independent.
-/

@[expose] public section

namespace Complexity.MathlibTM0

/-- A finite tape machine with marked input symbols and a separate output alphabet. -/
structure AlphabetMachine (Input Output : Type) where
  /-- Source tape alphabet. -/
  Alphabet : Type
  /-- Source control states. -/
  State : Type
  /-- Source alphabet finiteness. -/
  [alphabetFinite : Fintype Alphabet]
  /-- Default source symbol is blank. -/
  [alphabetInhabited : Inhabited Alphabet]
  /-- Source control finiteness. -/
  [stateFinite : Fintype State]
  /-- Default control is initial. -/
  [stateInhabited : Inhabited State]
  /-- Encode an input letter, distinguishing the first cell. -/
  inputSymbol : Bool → Input → Alphabet
  /-- The single cell representing empty input. -/
  empty : Alphabet
  /-- Decode an output letter, stopping on a symbol with no output letter. -/
  readSymbol : Alphabet → Option Output
  /-- Blank terminates output. -/
  readSymbol_blank : readSymbol default = none
  /-- Source transition function. -/
  code : Turing.TM0.Machine Alphabet State

attribute [instance] AlphabetMachine.alphabetFinite AlphabetMachine.alphabetInhabited
  AlphabetMachine.stateFinite AlphabetMachine.stateInhabited

namespace AlphabetMachine

variable {Input Output : Type}

/-- Reuse the existing source simulator; its binary endpoints are never entered. -/
abbrev simulatorSource (M : AlphabetMachine Input Output) : MarkedMachine where
  Alphabet := M.Alphabet
  State := M.State
  alphabetInhabited := M.alphabetInhabited
  stateInhabited := M.stateInhabited
  bit _ _ := default
  empty := M.empty
  readBit _ := none
  readBit_blank := rfl
  code := M.code

/-- Source cells for a complete input or an unmarked suffix. -/
def inputCells (M : AlphabetMachine Input Output) : Bool → List Input → List M.Alphabet
  | first, [] => if first then [M.empty] else []
  | first, a :: xs => M.inputSymbol first a :: M.inputCells false xs

/-- A bounded source run specifying every decoded output cell. -/
def OutputsWithin (M : AlphabetMachine Input Output) (input : List Input)
    (output : List Output) (time : ℕ) : Prop :=
  ∃ t ≤ time, ∃ c : M.simulatorSource.Config,
    M.simulatorSource.run t (Turing.TM0.init (M.inputCells true input)) = some c ∧
    Turing.TM0.step M.code c = none ∧
    ∀ j : ℕ, M.readSymbol (c.Tape.nth j) = output[j]?

/-- Parse a symbol code, rewind, run the existing simulator, or finish a codeword. -/
inductive Phase (inputSize outputSize : ℕ) (Q : Type) where
  /-- `none` waits for an opening delimiter; `some i` counts unary index bits. -/
  | copy : Bool → Option (Fin (inputSize + 1)) → Phase inputSize outputSize Q
  /-- Moving backwards alternates between closing and opening delimiters. -/
  | rewind : Bool → Phase inputSize outputSize Q
  /-- Existing source execution control; emission is replaced by encoded output. -/
  | source : Control Q → Phase inputSize outputSize Q
  /-- Emit the remaining unary index bits and then the closing delimiter. -/
  | emit : Fin (outputSize + 1) → Phase inputSize outputSize Q
  deriving Fintype

/-- An action preserving every work tape and head. -/
def pause {k : ℕ} {Q : Type} (state : Option Q) (output : Option Bool)
    (move : SignType) : Turing.Action k Bool Q where
  state := state
  inputTape := move
  output := output
  workTapes := fun _ => (none, 0)

/-- Parse finite-alphabet inputs, simulate the source, and encode its complete output. -/
noncomputable def machine (M : AlphabetMachine Input Output)
    (input : FiniteAlphabetCode Input) (output : FiniteAlphabetCode Output) :
    Turing.MultiTapeTM (Fintype.card M.simulatorSource.binary.Alphabet) Bool
      (Phase input.size output.size M.State) where
  q₀ := .copy true none
  tr q bit work := match q with
    | .copy first count => match count, bit with
      | none, some false => pause (some (.copy first (some 0))) none 1
      | none, some true => pause none none 0
      | some i, some true =>
          if h : i.val + 1 < input.size then
            pause (some (.copy first (some ⟨i.val + 1, by omega⟩))) none 1
          else pause none none 0
      | some i, some false =>
          if h : i.val < input.size then
            { state := some (.copy false none), inputTape := 1, output := none,
              workTapes := fun j =>
                (some (SymbolTracks.encode
                  (.source (M.inputSymbol first (input.index.symm ⟨i.val, h⟩)))
                  (trackEquiv M.simulatorSource.binary j)), 1) }
          else pause none none 0
      | some _, none => pause none none 0
      | none, none =>
          { state := some (.rewind true), inputTape := -1, output := none,
            workTapes := fun j =>
              (if first then some (SymbolTracks.encode (.source M.empty)
                (trackEquiv M.simulatorSource.binary j)) else none, 0) }
    | .rewind closing => match bit with
      | none => pause (some (.source (.run default))) none 0
      | some b =>
          { state := some (.rewind (if b then closing else !closing)),
            inputTape := -1, output := none,
            workTapes := fun _ => (none, if !b && closing then -1 else 0) }
    | .source .emit =>
        match M.readSymbol (MarkedMachine.Symbol.value (SymbolTracks.decode
          (fun a => work ((trackEquiv M.simulatorSource.binary).symm a)))) with
        | none => pause none none 0
        | some a =>
            { state := some (.emit ⟨(output.index a).val, by have := (output.index a).isLt; omega⟩),
              inputTape := 0, output := some false,
              workTapes := fun _ => (none, 1) }
    | .source q =>
        let a := (MathlibTM0.machine M.simulatorSource.binary).tr q bit work
        { a with state := a.state.map Phase.source }
    | .emit i =>
        if h : i.val = 0 then pause (some (.source .emit)) (some false) 0
        else pause (some (.emit ⟨i.val - 1, by omega⟩)) (some true) 0

end AlphabetMachine
end Complexity.MathlibTM0
