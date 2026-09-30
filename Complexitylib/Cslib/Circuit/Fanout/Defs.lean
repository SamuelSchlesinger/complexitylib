/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Complexitylib.Cslib.Circuit.Program
public import Mathlib.Data.Fintype.Sigma

/-!
# Counting wire uses in CSLib circuits

A wire use is one argument slot of a gate or one designated output. Repeated
arguments of the same gate and repeated outputs are separate uses. In
particular, counting distinct consumer gates would give the wrong fan-out.

`Circuit.inputUses` counts uses of original inputs. `Circuit.excessFanout`
counts uses beyond the first for each gate wire, and `Circuit.sharedGates`
selects gates with at least two uses. Outputs count as uses, so these notions
also handle a gate that supplies both another gate and a designated output.
On a trimmed single-output circuit this selects the usual shared internal gates.
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

variable {σ : Signature} {n m : ℕ}

/-- A gate argument slot or a designated output, counting repeated occurrences separately. -/
abbrev Circuit.WireUse (c : Circuit σ n m) :=
  (Σ j : Fin c.size, Fin (σ.Arity (c.program.lines j).op)) ⊕ Fin m

/-- The wire read by an argument slot or a designated output. -/
def Circuit.useWire (c : Circuit σ n m) : c.WireUse → Wire n c.size
  | .inl ⟨j, a⟩ => (c.program.lines j).wires a
  | .inr o => c.outputs o

/-- The number of uses of a wire, including designated outputs. -/
def Circuit.wireUses (c : Circuit σ n m) (w : Wire n c.size) : ℕ :=
  (Finset.univ.filter fun u : c.WireUse => c.useWire u = w).card

/-- Total occurrences of original input wires among gate arguments and outputs. -/
def Circuit.inputUses (c : Circuit σ n m) : ℕ :=
  ∑ i : Fin n, c.wireUses (.input i)

/-- Gate-wire uses beyond the first; unused gates contribute zero. -/
def Circuit.excessFanout (c : Circuit σ n m) : ℕ :=
  ∑ j : Fin c.size, (c.wireUses (.gate j) - 1)

/-- Gates whose output is used at least twice. Primary inputs are excluded. -/
def Circuit.sharedGates (c : Circuit σ n m) : Finset (Fin c.size) :=
  Finset.univ.filter fun j => 2 ≤ c.wireUses (.gate j)

/-- Every gate wire supplies at least one gate argument or designated output. -/
def Circuit.NoUnusedGates (c : Circuit σ n m) : Prop :=
  ∀ j : Fin c.size, 0 < c.wireUses (.gate j)

end Cslib.Circuits
