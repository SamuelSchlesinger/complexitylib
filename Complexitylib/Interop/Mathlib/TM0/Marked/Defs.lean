/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
public import Complexitylib.Interop.Mathlib.TM0.Defs

/-!
# Finite tape machines with a marked first input cell

Stack encodings distinguish the first cell and represent the empty word by a
marker. This bundle keeps that format explicit, while allowing output symbols
to differ from input symbols. The binary-track simulator can decode the output
without rewriting the source tape.
-/

@[expose] public section

namespace Complexity.MathlibTM0

/-- A finite TM0 with a first-cell input marker and a separate output decoder. -/
structure MarkedMachine where
  /-- Source tape alphabet. -/
  Alphabet : Type
  /-- Source control states. -/
  State : Type
  /-- The source alphabet is finite. -/
  [alphabetFinite : Fintype Alphabet]
  /-- The default symbol is blank. -/
  [alphabetInhabited : Inhabited Alphabet]
  /-- The source control is finite. -/
  [stateFinite : Fintype State]
  /-- The default state is initial. -/
  [stateInhabited : Inhabited State]
  /-- Encode a bit, distinguishing the first cell from subsequent cells. -/
  bit : Bool → Bool → Alphabet
  /-- The single cell representing empty input. -/
  empty : Alphabet
  /-- Decode output, stopping at the first symbol with no decoded bit. -/
  readBit : Alphabet → Option Bool
  /-- Blank terminates output. -/
  readBit_blank : readBit default = none
  /-- Source transitions. -/
  code : Turing.TM0.Machine Alphabet State

attribute [instance] MarkedMachine.alphabetFinite MarkedMachine.alphabetInhabited
  MarkedMachine.stateFinite MarkedMachine.stateInhabited

namespace MarkedMachine

/-- Source symbols plus unused raw bits needed by the existing simulator bundle. -/
inductive Symbol (Γ : Type) where
  /-- A raw bit in the simulator's ordinary binary interface. -/
  | raw : Bool → Symbol Γ
  /-- An actual source symbol. -/
  | source : Γ → Symbol Γ
  deriving Fintype

instance {Γ : Type} [Inhabited Γ] : Inhabited (Symbol Γ) := ⟨.source default⟩

/-- Forget the unused raw-bit symbols. -/
def Symbol.value {Γ : Type} [Inhabited Γ] : Symbol Γ → Γ
  | .raw _ => default
  | .source a => a

/-- Format an input suffix; only an empty complete input needs the empty marker. -/
def inputCells (M : MarkedMachine) : Bool → List Bool → List M.Alphabet
  | first, [] => if first then [M.empty] else []
  | first, b :: bs => M.bit first b :: M.inputCells false bs

/-- A source configuration with the bundle's blank and initial-state conventions. -/
abbrev Config (M : MarkedMachine) := Turing.TM0.Cfg M.Alphabet M.State

/-- Execute exactly the specified number of source transitions. -/
def run (M : MarkedMachine) : ℕ → M.Config → Option M.Config
  | 0, c => some c
  | t + 1, c => (Turing.TM0.step M.code c).bind (M.run t)

/-- A bounded source run whose complete decoded right-of-head output is specified. -/
def OutputsWithin (M : MarkedMachine) (input output : List Bool) (time : ℕ) : Prop :=
  ∃ t ≤ time, ∃ c : M.Config,
    M.run t (Turing.TM0.init (M.inputCells true input)) = some c ∧
    Turing.TM0.step M.code c = none ∧
    ∀ j : ℕ, M.readBit (c.Tape.nth j) = output[j]?

/-- Add unused raw-bit symbols to reuse the existing binary-machine simulation. -/
abbrev binary (M : MarkedMachine) : BinaryMachine where
  Alphabet := Symbol M.Alphabet
  alphabetInhabited := ⟨.source default⟩
  State := M.State
  bit := .raw
  readBit a := match a with
    | .raw b => some b
    | .source a => M.readBit a
  readBit_bit _ := rfl
  readBit_blank := M.readBit_blank
  code := M.code.map ⟨Symbol.source, rfl⟩ ⟨Symbol.value, rfl⟩ id id

/-- The new copying phase, followed by the existing rewind, run, and emit phases. -/
abbrev TargetState (M : MarkedMachine) := Bool ⊕ Control M.State

/-- Copy a marked source input, then delegate to the existing tape simulator. -/
noncomputable def machine (M : MarkedMachine) :
    Turing.MultiTapeTM (Fintype.card M.binary.Alphabet) Bool (TargetState M) where
  q₀ := .inl true
  tr q input work := match q with
    | .inr q =>
        let a := (MathlibTM0.machine M.binary).tr q input work
        { a with state := a.state.map Sum.inr }
    | .inl first => match input with
      | some b =>
          { state := some (.inl false), inputTape := 1, output := none,
            workTapes := fun i =>
              (some (SymbolTracks.encode (.source (M.bit first b)) (trackEquiv M.binary i)), 1) }
      | none =>
          { state := some (.inr .rewind), inputTape := -1, output := none,
            workTapes := fun i =>
              (if first then
                some (SymbolTracks.encode (.source M.empty) (trackEquiv M.binary i))
                else none, 0) }

end MarkedMachine
end Complexity.MathlibTM0
