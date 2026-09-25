/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexitylib.Models.TuringMachine
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.DeriveFintype

/-!
# Simulating Complexitylib machines on CSLib multi-tape machines

This file defines a CSLib multi-tape machine (`Turing.MultiTapeTM`) over the
binary alphabet that simulates a Complexitylib machine `tm : TM n` step for
step.

The two models differ in four ways, and the simulator handles each:

- **Left-end markers.** Our tapes carry `▷` in cell 0, but CSLib's binary
  tapes hold only `0`, `1`, and blank. Each of our work tapes and our output
  tape is therefore simulated by two CSLib tapes whose heads move together: a
  data tape holding cells `1, 2, …` and a marker tape holding a single `1` at
  position 0, written in the simulator's first step. The marker tape reads `1`
  exactly when the head is on our cell 0, where writes are no-ops and left
  moves stay put.
- **Output.** Our output tape is read-write, while CSLib emits output symbols
  one at a time. When `tm` halts, the simulator rewinds its copy of the output
  tape to cell 1, reads the verdict there, and emits it as a single bit.
- **Input head range.** CSLib's input head stops one cell past the input, but
  ours can run arbitrarily far into the blank tail. The last CSLib work tape
  counts how far our head is past that last cell. It holds `1` at position 0
  and is never written again, so it reads `1` exactly when the count is zero.
- **The left input boundary.** CSLib reads a blank both before and after the
  input. An `InputZone` flag in the state records whether our input head is
  on `▷`. After a left move from inside the input the flag is `probe`, and
  the next read settles it: the only position left of the input's end that
  reads blank is position 0.

## Main definitions

- `Complexity.TM.MultiTapeState` — the simulator's states
- `Complexity.TM.toMultiTape` — the CSLib machine simulating `tm`
- `Complexity.TM.toMultiTapeFun` — the variant whose final phase copies the
  whole output string instead of the verdict bit, for function computation
-/


@[expose] public section

namespace Complexity

open Turing

/-- A head direction as a CSLib head movement. -/
def Dir3.toSign : Dir3 → SignType
  | .left => -1
  | .right => 1
  | .stay => 0

/-- Read a binary CSLib cell as one of our symbols, with CSLib's blank as `□`. -/
def Γ.ofCell : Option Bool → Γ
  | none => .blank
  | some b => .ofBool b

/-- Store a writable symbol in a binary CSLib cell, with `□` as CSLib's blank. -/
def Γw.toCell : Γw → Option Bool
  | .zero => some false
  | .one => some true
  | .blank => none

namespace TM

/-- Where the simulated input head is, as far as the simulator's finite
control knows. -/
inductive InputZone where
  /-- On the left-end marker. -/
  | left
  /-- Past the left-end marker. -/
  | inner
  /-- Just moved left from within the input: on `▷` exactly when the input
  symbol now read is blank. -/
  | probe
  deriving DecidableEq

instance : Fintype InputZone where
  elems := {.left, .inner, .probe}
  complete := fun z => by cases z <;> simp

/-- Whether the input head is on the left-end marker, given the zone flag and
the CSLib input symbol under the head. -/
def InputZone.atLeft : InputZone → Option Bool → Bool
  | .left, _ => true
  | .inner, _ => false
  | .probe, i => i.isNone

/-- The states of the simulator for a machine with states `Q`. -/
inductive MultiTapeState (Q : Type) where
  /-- Write the position-0 markers. -/
  | init
  /-- Simulate state `q` of the original machine. -/
  | run (q : Q) (zone : InputZone)
  /-- Move the simulated output head back to the left-end marker. -/
  | rewind
  /-- Read the verdict in output cell 1 and halt. -/
  | verdict
  deriving DecidableEq, Fintype

variable {n : ℕ}

/-- The number of CSLib work tapes simulating a machine with `n` work tapes: a
data tape and a marker tape for each of our `n + 1` read-write tapes, and the
input overshoot counter. -/
abbrev simTapes (n : ℕ) : ℕ := (n + 1) + (n + 1) + 1

/-- CSLib data tape of our read-write tape `i`; tape `Fin.last n` is our
output tape. -/
def dataIdx (i : Fin (n + 1)) : Fin (simTapes n) := Fin.castAdd 1 (Fin.castAdd (n + 1) i)

/-- CSLib marker tape of our read-write tape `i`. -/
def markIdx (i : Fin (n + 1)) : Fin (simTapes n) := Fin.castAdd 1 (Fin.natAdd (n + 1) i)

/-- CSLib work tape counting how far the input head is past the input. -/
def overIdx : Fin (simTapes n) := Fin.natAdd ((n + 1) + (n + 1)) 0

/-- Assemble per-tape actions into CSLib's tape order. -/
def tapeLayout {α : Type*} (data mark : Fin (n + 1) → α) (over : α) : Fin (simTapes n) → α :=
  Fin.append (Fin.append data mark) ![over]

/-- Our symbol under the head of simulated tape `i`, from the CSLib symbols
`w` under all heads. -/
def simRead (w : Fin (simTapes n) → Option Bool) (i : Fin (n + 1)) : Γ :=
  if w (markIdx i) = some true then Γ.start else Γ.ofCell (w (dataIdx i))

/-- The CSLib head move simulating move `d` on a one-sided tape. On `▷`
(cell 0) a left move stays put, matching `Tape.move`. -/
def oneSidedMove (atStart : Bool) (d : Dir3) : SignType :=
  if atStart && d = Dir3.left then 0 else d.toSign

/-- The CSLib write simulating a write of `w` on a one-sided tape. On `▷`
(cell 0) the write is dropped, matching `Tape.write`. -/
def oneSidedWrite (atStart : Bool) (w : Γw) : Option (Option Bool) :=
  if atStart then none else some w.toCell

/-- The moves simulating an input-head move `d`: the CSLib input head move,
the overshoot counter move, and the next zone. `atLeft` says the head is on
`▷`, `i` is the CSLib input symbol, and `ov` is the counter tape's symbol,
which is `1` exactly when the counter is zero. -/
def inputAction (atLeft : Bool) (i ov : Option Bool) : Dir3 → SignType × SignType × InputZone
  | .right => if !atLeft && i.isNone then (0, 1, .inner) else (1, 0, .inner)
  | .left =>
    if atLeft then (0, 0, .left)
    else if i.isNone && ov ≠ some true then (0, -1, .inner)
    else (-1, 0, .probe)
  | .stay => (0, 0, if atLeft then .left else .inner)

/-- The simulator's transition function. -/
def toMultiTapeTr (tm : TM n) (q : MultiTapeState tm.Q) (i : Option Bool)
    (w : Fin (simTapes n) → Option Bool) : Action (simTapes n) Bool (MultiTapeState tm.Q) :=
  match q with
  | .init =>
    { inputTape := -1
      workTapes := tapeLayout (fun _ => (none, 0)) (fun _ => (some (some true), 0))
        (some (some true), 0)
      output := none
      state := some (.run tm.qstart .left) }
  | .run q zone =>
    if q = tm.qhalt then
      { inputTape := 0
        workTapes := fun _ => (none, 0)
        output := none
        state := some .rewind }
    else
      let atLeft := zone.atLeft i
      let rIn := if atLeft then Γ.start else Γ.ofCell i
      let o := tm.δ q rIn (fun j => simRead w j.castSucc) (simRead w (Fin.last n))
      let ops : Fin (n + 1) → Γw × Dir3 :=
        Fin.lastCases (o.2.2.1, o.2.2.2.2.2) fun j => (o.2.1 j, o.2.2.2.2.1 j)
      let atStart := fun j => decide (w (markIdx j) = some true)
      let a := inputAction atLeft i (w overIdx) o.2.2.2.1
      { inputTape := a.1
        workTapes := tapeLayout
          (fun j => (oneSidedWrite (atStart j) (ops j).1, oneSidedMove (atStart j) (ops j).2))
          (fun j => (none, oneSidedMove (atStart j) (ops j).2)) (none, a.2.1)
        output := none
        state := some (.run o.1 a.2.2) }
  | .rewind =>
    let atStart := w (markIdx (Fin.last n)) = some true
    let move : Fin (n + 1) → SignType := fun j =>
      if j = Fin.last n then (if atStart then 1 else -1) else 0
    { inputTape := 0
      workTapes := tapeLayout (fun j => (none, move j)) (fun j => (none, move j)) (none, 0)
      output := none
      state := some (if atStart then .verdict else .rewind) }
  | .verdict =>
    { inputTape := 0
      workTapes := fun _ => (none, 0)
      output := some (decide (simRead w (Fin.last n) = Γ.one))
      state := none }

/-- The CSLib multi-tape machine simulating `tm`. Our work tape `i` and our
output tape (`i = n`) each use a data tape and a marker tape, and the last tape
counts input-head overshoot. It emits the single bit `true` to accept and
`false` to reject. -/
def toMultiTape (tm : TM n) : MultiTapeTM (simTapes n) Bool (MultiTapeState tm.Q) where
  q₀ := .init
  tr := tm.toMultiTapeTr

/-- The transition function of the function-computing simulator: the decision
simulator's, except that the final state copies the simulated output cell under
the head to CSLib's output and moves right, halting at the first blank. -/
def toMultiTapeFunTr (tm : TM n) (q : MultiTapeState tm.Q) (i : Option Bool)
    (w : Fin (simTapes n) → Option Bool) : Action (simTapes n) Bool (MultiTapeState tm.Q) :=
  match q with
  | .verdict =>
    let move : Fin (n + 1) → SignType := fun j => if j = Fin.last n then 1 else 0
    { inputTape := 0
      workTapes := tapeLayout (fun j => (none, move j)) (fun j => (none, move j)) (none, 0)
      output := w (dataIdx (Fin.last n))
      state := if w (dataIdx (Fin.last n)) = none then none else some .verdict }
  | q => tm.toMultiTapeTr q i w

/-- The CSLib multi-tape machine computing the function `tm` computes: it
simulates `tm`, rewinds the simulated output tape, and copies the output string
to CSLib's output. -/
def toMultiTapeFun (tm : TM n) : MultiTapeTM (simTapes n) Bool (MultiTapeState tm.Q) where
  q₀ := .init
  tr := tm.toMultiTapeFunTr

end TM

end Complexity
