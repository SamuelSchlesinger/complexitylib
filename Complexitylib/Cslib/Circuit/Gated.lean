/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Composition

/-!
# CSLib circuits whose outputs are gates

A CSLib circuit (`Cslib.Circuits.Circuit`) may designate any wire as an output,
including an original input, and designating outputs is free. Complexitylib's
typed circuits instead charge one gate per output. The two conventions agree
exactly on circuits whose every output is an internal gate, which this file
names `Circuit.GatedOutputs`.

Sequential composition keeps this property when the outer circuit has it, and
parallel composition keeps it when both circuits do. The number of outputs
that forward an input, `Circuit.inputOutputCount`, measures how far a circuit
is from having it.

This file lives in `Complexitylib/Cslib/` because it extends CSLib types in
their home namespace `Cslib.Circuits`; its contents are candidates for
upstreaming to CSLib.

## Main definitions

- `Cslib.Circuits.Wire.IsGate` — a wire is the output of an internal gate
- `Cslib.Circuits.Wire.gateOf` — the gate carrying a gate wire
- `Cslib.Circuits.Circuit.GatedOutputs` — every output is an internal gate
- `Cslib.Circuits.Circuit.inputOutputCount` — the number of outputs that
  forward an input

## Main results

- `Cslib.Circuits.Circuit.GatedOutputs.size_pos` — a gated circuit with an
  output has a gate
- `Cslib.Circuits.Circuit.GatedOutputs.comp`,
  `Cslib.Circuits.Circuit.GatedOutputs.append` — composition keeps gated
  outputs
- `Cslib.Circuits.Circuit.inputOutputCount_eq_zero_iff` — no output forwards
  an input exactly when the outputs are gated
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n m p k g g₁ g₂ : ℕ}

namespace Wire

/-- Whether a wire is the output of an internal gate rather than an original
input. -/
def IsGate : Wire n g → Prop
  | .input _ => False
  | .gate _ => True

/-- Whether a wire is a gate is decided by its constructor. -/
instance instDecidableIsGate (w : Wire n g) : Decidable w.IsGate :=
  match w with
  | .input _ => isFalse id
  | .gate _ => isTrue trivial

/-- An original input is not a gate. -/
@[simp] theorem not_isGate_input (i : Fin n) : ¬ (input i : Wire n g).IsGate :=
  id

/-- A gate wire is a gate. -/
@[simp] theorem isGate_gate (j : Fin g) : (gate j : Wire n g).IsGate :=
  trivial

/-- A wire is a gate exactly when it is `gate j` for some `j`. -/
theorem isGate_iff_exists (w : Wire n g) : w.IsGate ↔ ∃ j, w = gate j := by
  cases w <;> simp

/-- Widening a wire into a longer program keeps whether it is a gate. -/
@[simp] theorem isGate_castSucc (w : Wire n g) : w.castSucc.IsGate ↔ w.IsGate := by
  cases w <;> simp

/-- Continuing a program by further gates keeps whether a wire is a gate. -/
@[simp] theorem isGate_castAdd (w : Wire n g) : (w.castAdd k).IsGate ↔ w.IsGate := by
  cases w <;> simp

/-- The gate carrying a gate wire. The input case is absurd, so this is
computable. -/
def gateOf : (w : Wire n g) → w.IsGate → Fin g
  | .gate j, _ => j
  | .input _, h => False.elim h

/-- The gate carrying `gate j` is `j`. -/
@[simp] theorem gateOf_gate (j : Fin g) (h : (gate j : Wire n g).IsGate) :
    (gate j : Wire n g).gateOf h = j :=
  rfl

/-- A gate wire is the wire of the gate carrying it. -/
@[simp] theorem gate_gateOf : ∀ (w : Wire n g) (h : w.IsGate), gate (w.gateOf h) = w
  | .gate _, _ => rfl
  | .input _, h => False.elim h

/-- A gate wire of a continued program's second part is a gate. -/
theorem IsGate.appendWire {w : Wire k g₂} (h : w.IsGate) (feed : Fin k → Wire n g₁) :
    (Program.appendWire feed w).IsGate := by
  cases w with
  | input i => exact False.elim h
  | gate j => trivial

end Wire

namespace Circuit

/-- Every designated output of `c` is an internal gate, never an original
input. These are the circuits on which charging one gate per output, as typed
circuits do, and CSLib's free outputs agree. -/
def GatedOutputs (c : Circuit σ n m) : Prop :=
  ∀ o, (c.outputs o).IsGate

/-- Whether every output is a gate is decidable, output by output. -/
instance instDecidableGatedOutputs (c : Circuit σ n m) : Decidable c.GatedOutputs :=
  Fintype.decidableForallFintype

/-- **A gated circuit with an output has a gate.** -/
theorem GatedOutputs.size_pos [NeZero m] {c : Circuit σ n m} (h : c.GatedOutputs) :
    0 < c.size :=
  ((c.outputs 0).gateOf (h 0)).pos

/-- **Sequential composition keeps gated outputs** when the outer circuit has
them: its outputs are gates after the inner circuit's gates. -/
theorem GatedOutputs.comp {d : Circuit σ m p} (hd : d.GatedOutputs) (c : Circuit σ n m) :
    (d.comp c).GatedOutputs :=
  fun o => (hd o).appendWire c.outputs

/-- **Parallel composition keeps gated outputs** when both circuits have
them. -/
theorem GatedOutputs.append {c : Circuit σ n m} {d : Circuit σ n p}
    (hc : c.GatedOutputs) (hd : d.GatedOutputs) : (c.append d).GatedOutputs := by
  intro o
  induction o using Fin.addCases with
  | left o =>
    simp only [Circuit.append, Fin.append_left, Wire.isGate_castAdd]
    exact hc o
  | right o =>
    simp only [Circuit.append, Fin.append_right]
    exact (hd o).appendWire Wire.input

/-- The number of outputs of `c` that forward an original input instead of a
gate. -/
def inputOutputCount (c : Circuit σ n m) : ℕ :=
  (Finset.univ.filter fun o => ¬ (c.outputs o).IsGate).card

/-- **No output forwards an input exactly when the outputs are gated.** -/
theorem inputOutputCount_eq_zero_iff {c : Circuit σ n m} :
    c.inputOutputCount = 0 ↔ c.GatedOutputs := by
  simp [inputOutputCount, GatedOutputs, Finset.filter_eq_empty_iff]

/-- At most every output forwards an input. -/
theorem inputOutputCount_le (c : Circuit σ n m) : c.inputOutputCount ≤ m :=
  (Finset.card_filter_le _ _).trans (by simp)

end Circuit

end Cslib.Circuits
