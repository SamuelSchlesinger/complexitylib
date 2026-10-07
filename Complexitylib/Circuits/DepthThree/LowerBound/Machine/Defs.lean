/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Defs
public import Complexitylib.Interop.SymbolTracks
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# A binary simulator for finite-alphabet multitape machines

Each source tape is represented by one binary track per source symbol. Input copying and
rewinding cost `2 * n + 2` steps; each source transition costs one step, and halting costs one.
The source model is OpenAI's finite multitape model, imported in `LowerBound.Defs`.
-/

@[expose] public section

namespace Complexity.DepthThreeLowerBound.FiniteMultiTapeBridge

/-- Encode a symbol by one track per alphabet symbol; blank is all blank tracks. -/
noncomputable def encode {Γ : Type*} [Inhabited Γ] (a b : Γ) : Option Bool :=
  SymbolTracks.encode a b

/-- Decode a vector of symbol tracks, inverse to the one-hot encoding. -/
noncomputable def decode {Γ : Type*} [Inhabited Γ] (v : Γ → Option Bool) : Γ :=
  SymbolTracks.decode v

/-- Translate the three source head directions to CSLib head displacements. -/
def moveSign : HeadMove → SignType
  | .left => .neg
  | .stay => .zero
  | .right => .pos

/-- Copy the input, rewind its work tracks, then run the source control. -/
inductive Control (Q : Type*) where
  /-- Copy the input bits to the designated work tracks. -/
  | copy
  /-- Return all input work heads to the first cell. -/
  | rewind
  /-- Simulate the source control state. -/
  | run : Q → Control Q
  deriving Fintype

/-- One binary work tape per source tape and source alphabet symbol. -/
abbrev Track (M : FiniteMultiTapeMachine) := Fin (Fintype.card (M.K × M.Γ))

/-- Identify the numbered CSLib work tapes with source tape-symbol pairs. -/
noncomputable def trackEquiv (M : FiniteMultiTapeMachine) : Track M ≃ M.K × M.Γ :=
  (Fintype.equivFin _).symm

/-- The binary work tape recording one symbol on one source tape. -/
noncomputable def track (M : FiniteMultiTapeMachine) (k : M.K) (a : M.Γ) : Track M :=
  (trackEquiv M).symm (k, a)

/-- A transition that leaves every work tape unchanged. -/
def idle (M : FiniteMultiTapeMachine) (state : Option (Control M.Q))
    (output : Option Bool) (inputMove : SignType) :
    Turing.Action (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) where
  state := state
  inputTape := inputMove
  output := output
  workTapes := fun _ => (none, 0)

/-- Simulate a source transition, or emit its verdict and halt. -/
noncomputable def runAction (M : FiniteMultiTapeMachine) (q : M.Q)
    (work : Track M → Option Bool) :
    Turing.Action (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) :=
  match M.code q (fun k => decode (fun a => work (track M k a))) with
  | none => idle M none (some (M.accept q)) 0
  | some (q', writes, moves) =>
    { state := some (.run q')
      inputTape := 0
      output := none
      workTapes := fun i =>
        (some (encode (writes (trackEquiv M i).1) (trackEquiv M i).2),
          moveSign (moves (trackEquiv M i).1)) }

/-- A binary CSLib simulator with two initialization states and one state per source state. -/
noncomputable def machine (M : FiniteMultiTapeMachine) :
    Turing.MultiTapeTM (Fintype.card (M.K × M.Γ)) Bool (Control M.Q) where
  q₀ := .copy
  tr q input work := match q with
    | .run q => runAction M q work
    | .copy => match input with
      | none => idle M (some .rewind) none (-1)
      | some b =>
        { state := some .copy
          inputTape := 1
          output := none
          workTapes := fun i =>
            if (trackEquiv M i).1 = M.inputTape then
              (some (encode (M.inputSymbol b) (trackEquiv M i).2), 1)
            else (none, 0) }
    | .rewind => match input with
      | none => idle M (some (.run M.initialState)) none 0
      | some _ =>
        { state := some .rewind
          inputTape := -1
          output := none
          workTapes := fun i =>
            (none, if (trackEquiv M i).1 = M.inputTape then -1 else 0) }

end Complexity.DepthThreeLowerBound.FiniteMultiTapeBridge
