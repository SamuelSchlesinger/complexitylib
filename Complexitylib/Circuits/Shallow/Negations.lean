/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.AndOrNot.Defs
public import Cslib.Computability.Circuit.Composition

/-!
# Negations only at primary inputs

The ambient unbounded AND/OR signature permits a negation on any argument.
This predicate restricts a CSLib circuit to the paper's convention: only
primary input wires may be negated. The layer compiler preserves it.
-/

@[expose] public section

namespace Complexity.Shallow

open Cslib.Circuits

/-- Every negated argument in a program reads a primary input. -/
def ProgramInputNegationsOnly {n : ℕ} : {g : ℕ} →
    Program Basis.unboundedAndOr.signature n g → Prop
  | _, .empty => True
  | _, .gate p l => ProgramInputNegationsOnly p ∧
      ∀ i, l.op.negated i = true → ∃ j, l.wires i = .input j

/-- A CSLib circuit in negation normal form, with negations only at inputs. -/
def InputNegationsOnly {n m : ℕ}
    (c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m) : Prop :=
  ProgramInputNegationsOnly c.program

/-- Parallel continuation preserves input-only negations. -/
theorem ProgramInputNegationsOnly.append {n g h : ℕ}
    {p : Program Basis.unboundedAndOr.signature n g}
    {q : Program Basis.unboundedAndOr.signature n h}
    (hp : ProgramInputNegationsOnly p) (hq : ProgramInputNegationsOnly q) :
    ProgramInputNegationsOnly (p.append Wire.input q) := by
  induction q with
  | empty => exact hp
  | gate q l ih =>
    refine ⟨ih hq.1, fun i hi => ?_⟩
    obtain ⟨j, hj⟩ := hq.2 i hi
    refine ⟨j, ?_⟩
    change Program.appendedWire Wire.input (l.wires i) = Wire.input j
    rw [hj]
    rfl

/-- Parallel circuits preserve input-only negations. -/
theorem InputNegationsOnly.append {n m r : ℕ}
    {c : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n m}
    {e : Cslib.Circuits.Circuit Basis.unboundedAndOr.signature n r}
    (hc : InputNegationsOnly c) (he : InputNegationsOnly e) :
    InputNegationsOnly (c.append e) := ProgramInputNegationsOnly.append hc he

end Complexity.Shallow
