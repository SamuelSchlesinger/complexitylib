/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Cslib.Computability.Circuit.Boolean.Basic
public import Complexitylib.Circuits.AndOrNot.Defs
public import Mathlib.Data.Fin.VecNotation

/-!
# CSLib De Morgan circuits as Complexitylib circuits

CSLib's circuit model (`Cslib.Circuits.Circuit`) is a straight-line program
over a signature, with designated output wires. Its De Morgan basis
(`Cslib.Circuits.Boolean.signature`) has constants, negation, and binary
conjunction and disjunction, and every gate counts toward size. A circuit
carries its gate count as the field `size`.

A CSLib wire (`Cslib.Circuits.Wire N g`) is either an input `Wire.input i` or
a gate `Wire.gate j`. Our circuits number their wires `Fin (N + g)`, the inputs
first and gate `j` driving wire `N + j`, which is exactly CSLib's numbering
`Wire.index`. This file translates a CSLib De Morgan circuit gate for gate into
a fan-in-two AND/OR circuit over `Basis.andOr2`, whose negations are free:

- a negation `¬w` becomes `¬w ∧ ¬w`;
- a constant becomes `x₀ ∧ ¬x₀` or `x₀ ∨ ¬x₀` on the first input;
- conjunction and disjunction are unchanged;
- an output wire `w` becomes the output gate `w ∧ w`.

So the translated circuit has exactly the CSLib circuit's gates as internal
gates, plus one output gate per output.

## Main definitions

- `Complexity.Circuit.ofCslibGate` — the gate simulating one CSLib line
- `Complexity.Circuit.ofCslib` — the circuit simulating a CSLib circuit
-/


@[expose] public section

namespace Complexity

open Cslib.Circuits

namespace Circuit

variable {N g : ℕ}

/-- The first input wire, read by the gates simulating constants. -/
def firstWire [NeZero N] : Fin (N + g) :=
  ⟨0, Nat.lt_add_right g (Nat.pos_of_ne_zero (NeZero.ne N))⟩

/-- The fan-in-two AND/OR gate computing a CSLib De Morgan line. -/
def ofCslibGate [NeZero N] (l : Line Boolean.signature N g) : Gate Basis.andOr2 (N + g) :=
  match l with
  | ⟨.const b, _⟩ =>
    { op := if b then .or else .and, fanIn := 2, arityOk := rfl
      inputs := ![firstWire, firstWire]
      negated := ![false, true] }
  | ⟨.not, w⟩ =>
    { op := .and, fanIn := 2, arityOk := rfl
      inputs := ![(w ⟨0, by decide⟩).index, (w ⟨0, by decide⟩).index]
      negated := ![true, true] }
  | ⟨.and, w⟩ =>
    { op := .and, fanIn := 2, arityOk := rfl
      inputs := ![(w ⟨0, by decide⟩).index, (w ⟨1, by decide⟩).index]
      negated := ![false, false] }
  | ⟨.or, w⟩ =>
    { op := .or, fanIn := 2, arityOk := rfl
      inputs := ![(w ⟨0, by decide⟩).index, (w ⟨1, by decide⟩).index]
      negated := ![false, false] }

/-- The gate simulating a line reads only the first input and the line's own
wires. -/
theorem ofCslibGate_inputs_lt [NeZero N] (l : Line Boolean.signature N g) {bound : ℕ}
    (hN : N ≤ bound) (hl : ∀ a, (l.wires a).index.val < bound)
    (k : Fin (ofCslibGate l).fanIn) : ((ofCslibGate l).inputs k).val < bound := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨op, w⟩ := l
  revert k
  cases op <;> simp only [ofCslibGate, Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
    simp [firstWire] <;> first | omega | exact hl _

/-- The fan-in-two AND/OR circuit simulating a CSLib De Morgan circuit. Its
internal gates are the CSLib circuit's gates, and output `j` is the gate
`w ∧ w` on CSLib's output wire `w`. -/
def ofCslib {M : ℕ} [NeZero N] [NeZero M]
    (c : Cslib.Circuits.Circuit Boolean.signature N M) : Circuit Basis.andOr2 N M c.size where
  gates j := ofCslibGate (c.program.lines j)
  outputs j :=
    { op := .and, fanIn := 2, arityOk := rfl
      inputs := ![(c.outputs j).index, (c.outputs j).index]
      negated := ![false, false] }
  acyclic j k :=
    ofCslibGate_inputs_lt _ (by omega) (Program.lines_wires_lt c.program j) k

end Circuit

end Complexity
