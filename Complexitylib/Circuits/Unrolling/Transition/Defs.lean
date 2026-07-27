/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Batch.Defs
public import Complexitylib.Circuits.Unrolling.Defs
public import Mathlib.Data.Fintype.Prod

/-!
# Boolean formulas for one Turing-machine transition

This file defines the proof-free formula layer for one step of a bounded
nondeterministic Turing-machine trace. A `TransitionCase` records a complete
local view of the machine, including its choice bit. Its `TransitionEffect`
names the otherwise deeply nested components returned by `NTM.δ`.

The formulas read one encoded configuration block and produce the value of
each atom in its halted-or-successor configuration. Input cells are preserved,
writable cell zero is immutable, writes use the old head position, and head
movement uses saturated subtraction at the left boundary. A right move from
the largest represented head position has no represented target; clients rule
out that case with `HeadsLt` before applying transition correctness.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace WritableSlot

/-- Select a writable work/output tape from a machine configuration. -/
def get (c : Cfg k Q) : WritableSlot k → Tape
  | .work i => c.work i
  | .output => c.output

end WritableSlot

/-- A complete finite local view determining one nondeterministic transition. -/
@[ext] structure TransitionCase (tm : NTM k) where
  /-- The nondeterministic or probabilistic choice bit for this step. -/
  choice : Bool
  /-- The current control state. -/
  state : tm.Q
  /-- The symbol under the input head. -/
  inputRead : Γ
  /-- The symbol under each work-tape head. -/
  workRead : Fin k → Γ
  /-- The symbol under the output head. -/
  outputRead : Γ
  deriving DecidableEq

/-- Product representation used to enumerate complete local views. -/
def transitionCaseEquiv (tm : NTM k) :
    TransitionCase tm ≃ Bool × tm.Q × Γ × (Fin k → Γ) × Γ where
  toFun view :=
    (view.choice, view.state, view.inputRead, view.workRead, view.outputRead)
  invFun
    | (choice, state, inputRead, workRead, outputRead) =>
        { choice := choice
          state := state
          inputRead := inputRead
          workRead := workRead
          outputRead := outputRead }
  left_inv view := by cases view; rfl
  right_inv view := by rcases view with ⟨choice, state, inputRead, workRead, outputRead⟩; rfl

/-- Complete local transition views form a finite type. -/
noncomputable instance (tm : NTM k) : Fintype (TransitionCase tm) :=
  Fintype.ofEquiv (Bool × tm.Q × Γ × (Fin k → Γ) × Γ) (transitionCaseEquiv tm).symm

namespace TransitionCase

/-- Select the read symbol for a named tape from a transition case. -/
def read {k : ℕ} {tm : NTM k} (view : TransitionCase tm) : TapeSlot k → Γ
  | .input => view.inputRead
  | .work i => view.workRead i
  | .output => view.outputRead

end TransitionCase

/-- The complete local transition view presented by a configuration and choice bit. -/
def currentCase (tm : NTM k) (choice : Bool) (c : Cfg k tm.Q) : TransitionCase tm :=
  { choice := choice
    state := c.state
    inputRead := c.input.read
    workRead := fun i => (c.work i).read
    outputRead := c.output.read }

/-- The named components of the action returned by `NTM.δ` for a local view. -/
structure TransitionEffect (tm : NTM k) where
  /-- The successor control state. -/
  nextState : tm.Q
  /-- The symbol written on each work tape before its head moves. -/
  workWrite : Fin k → Γw
  /-- The symbol written on the output tape before its head moves. -/
  outputWrite : Γw
  /-- The input-head movement. -/
  inputMove : Dir3
  /-- Each work-head movement. -/
  workMove : Fin k → Dir3
  /-- The output-head movement. -/
  outputMove : Dir3
  deriving DecidableEq

namespace TransitionEffect

/-- Select the write symbol for a named writable tape. -/
def write {k : ℕ} {tm : NTM k} (effect : TransitionEffect tm) : WritableSlot k → Γw
  | .work i => effect.workWrite i
  | .output => effect.outputWrite

/-- Select the movement of any named tape head. -/
def move {k : ℕ} {tm : NTM k} (effect : TransitionEffect tm) : TapeSlot k → Dir3
  | .input => effect.inputMove
  | .work i => effect.workMove i
  | .output => effect.outputMove

end TransitionEffect

namespace TransitionCase

/-- Unpack the transition action selected by a complete local view. -/
def effect {k : ℕ} {tm : NTM k} (view : TransitionCase tm) : TransitionEffect tm :=
  let (nextState, workWrite, outputWrite, inputMove, workMove, outputMove) :=
    tm.δ view.choice view.state view.inputRead view.workRead view.outputRead
  { nextState := nextState
    workWrite := workWrite
    outputWrite := outputWrite
    inputMove := inputMove
    workMove := workMove
    outputMove := outputMove }

end TransitionCase

/-- Every possible local view, in the finite ordering induced by `Fintype`. -/
noncomputable def transitionCases (tm : NTM k) : List (TransitionCase tm) :=
  (Finset.univ : Finset (TransitionCase tm)).toList

/-- Every named head lies strictly below `T`.

For the layout with head positions `Fin (T + 1)`, this excludes the sole
position whose right successor would fall outside the represented block. -/
def HeadsLt (T : ℕ) (c : Cfg k Q) : Prop :=
  ∀ tape : TapeSlot k, (tape.get c).head < T

/-- Execute the halted-or-one-step semantics selected by one choice bit. -/
def choiceStep (tm : NTM k) (choice : Bool) (c : Cfg k tm.Q) : Cfg k tm.Q :=
  tm.trace 1 (fun _ => choice) c

/-- The formula variable carrying an atom of the incoming configuration. -/
noncomputable def configVar (tm : NTM k) (T base : ℕ)
    (atom : ConfigAtom tm T) : BoolFormula :=
  .var (configWire tm T base atom)

/-- The incoming configuration's halted-state bit. -/
noncomputable def haltVar (tm : NTM k) (T base : ℕ) : BoolFormula :=
  configVar tm T base (.state tm.qhalt)

/-- Embed a represented head position into the one-cell-larger cell range. -/
def headCellPosition (position : Fin (T + 1)) : Fin (T + 2) :=
  ⟨position.val, by omega⟩

/-- Formula saying that a named tape reads a given symbol under its head. -/
noncomputable def readFormula (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (symbol : Γ) : BoolFormula :=
  BoolFormula.disjs <| List.ofFn fun position : Fin (T + 1) =>
    .conj (configVar tm T base (.head tape position))
      (configVar tm T base (.cell tape (headCellPosition position) symbol))

/-- Formula recognizing one complete local transition case. -/
noncomputable def caseFormula (tm : NTM k) (T base choiceWire : ℕ)
    (view : TransitionCase tm) : BoolFormula :=
  BoolFormula.conjs <|
    [BoolFormula.literal choiceWire view.choice,
      configVar tm T base (.state view.state),
      readFormula tm T base .input view.inputRead] ++
    (List.ofFn fun i : Fin k =>
      readFormula tm T base (.work i) (view.workRead i)) ++
    [readFormula tm T base .output view.outputRead]

/-- Select transition cases whose named effect satisfies a Boolean test. -/
noncomputable def effectFormula (tm : NTM k) (T base choiceWire : ℕ)
    (selects : TransitionEffect tm → Bool) : BoolFormula :=
  BoolFormula.disjs <| (transitionCases tm).map fun view =>
    if selects view.effect then caseFormula tm T base choiceWire view else .fls

/-- Formula selecting transition cases with a specified successor state. -/
noncomputable def selectedStateFormula (tm : NTM k) (T base choiceWire : ℕ)
    (state : tm.Q) : BoolFormula :=
  effectFormula tm T base choiceWire fun effect => decide (effect.nextState = state)

/-- Formula selecting transition cases that move a named head in a given direction. -/
noncomputable def selectedMoveFormula (tm : NTM k) (T base choiceWire : ℕ)
    (tape : TapeSlot k) (direction : Dir3) : BoolFormula :=
  effectFormula tm T base choiceWire fun effect => decide (effect.move tape = direction)

/-- Formula selecting transition cases that write a specified symbol. -/
noncomputable def selectedWriteFormula (tm : NTM k) (T base choiceWire : ℕ)
    (tape : WritableSlot k) (symbol : Γ) : BoolFormula :=
  effectFormula tm T base choiceWire fun effect =>
    decide ((effect.write tape).toΓ = symbol)

/-- Numeric head position after one move, with saturated movement at zero. -/
def movedHeadPosition (position : ℕ) : Dir3 → ℕ
  | .left => position - 1
  | .right => position + 1
  | .stay => position

/-- Incoming head positions that reach a target under one fixed direction. -/
noncomputable def predecessorHeadFormula (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) (direction : Dir3) : BoolFormula :=
  BoolFormula.disjs <| List.ofFn fun source : Fin (T + 1) =>
    if movedHeadPosition source.val direction = target.val then
      configVar tm T base (.head tape source)
    else
      .fls

/-- Non-halted formula for a named head's next represented position. -/
noncomputable def movedHeadFormula (tm : NTM k) (T base choiceWire : ℕ)
    (tape : TapeSlot k) (target : Fin (T + 1)) : BoolFormula :=
  BoolFormula.disjs
    [.conj (selectedMoveFormula tm T base choiceWire tape .left)
        (predecessorHeadFormula tm T base tape target .left),
      .conj (selectedMoveFormula tm T base choiceWire tape .right)
        (predecessorHeadFormula tm T base tape target .right),
      .conj (selectedMoveFormula tm T base choiceWire tape .stay)
        (predecessorHeadFormula tm T base tape target .stay)]

/-- Formula saying that the old head is at a represented cell position.

The final cell in `Fin (T + 2)` has no corresponding old head position and
therefore produces `false`. -/
noncomputable def headAtCellFormula (tm : NTM k) (T base : ℕ)
    (tape : TapeSlot k) (position : Fin (T + 2)) : BoolFormula :=
  if h : position.val < T + 1 then
    configVar tm T base (.head tape ⟨position.val, h⟩)
  else
    .fls

/-- Choose the old atom when halted and a transition formula otherwise. -/
noncomputable def haltedOrFormula (tm : NTM k) (T base : ℕ)
    (oldValue nextValue : BoolFormula) : BoolFormula :=
  .disj (.conj (haltVar tm T base) oldValue)
    (.conj (.neg (haltVar tm T base)) nextValue)

/-- Formula for a positive writable cell after the write phase of one step. -/
noncomputable def writtenCellFormula (tm : NTM k) (T base choiceWire : ℕ)
    (tape : WritableSlot k) (position : Fin (T + 2)) (symbol : Γ) : BoolFormula :=
  let oldValue := configVar tm T base (.cell tape.toTapeSlot position symbol)
  let atHead := headAtCellFormula tm T base tape.toTapeSlot position
  .disj
    (.conj atHead (selectedWriteFormula tm T base choiceWire tape symbol))
    (.conj (.neg atHead) oldValue)

/-- Formula for one atom of the halted-or-successor configuration.

Input cells never change. Writable cell zero also never changes, because
`Tape.write` is a no-op there. Every other writable cell is updated at the old
head position before the head movement represented by the head atoms. -/
noncomputable def nextFormula (tm : NTM k) (T base choiceWire : ℕ) :
    ConfigAtom tm T → BoolFormula
  | atom@(.state state) =>
      haltedOrFormula tm T base (configVar tm T base atom)
        (selectedStateFormula tm T base choiceWire state)
  | atom@(.head tape position) =>
      haltedOrFormula tm T base (configVar tm T base atom)
        (movedHeadFormula tm T base choiceWire tape position)
  | atom@(.cell .input _ _) =>
      configVar tm T base atom
  | atom@(.cell (.work i) position symbol) =>
      if position.val = 0 then
        configVar tm T base atom
      else
        haltedOrFormula tm T base (configVar tm T base atom)
          (writtenCellFormula tm T base choiceWire (.work i) position symbol)
  | atom@(.cell .output position symbol) =>
      if position.val = 0 then
        configVar tm T base atom
      else
        haltedOrFormula tm T base (configVar tm T base atom)
          (writtenCellFormula tm T base choiceWire .output position symbol)

end CircuitUnrolling

end Complexity
