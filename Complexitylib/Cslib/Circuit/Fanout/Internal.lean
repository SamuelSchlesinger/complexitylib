/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Complexitylib.Cslib.Circuit.Fanout.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Double counting wire uses -/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

variable {σ : Signature} {n m : ℕ}

/-- The number of wire-use occurrences is the total fan-in plus the output count. -/
theorem Circuit.card_wireUse (c : Circuit σ n m) :
    Fintype.card c.WireUse = c.totalFanIn + m := by
  simp [Circuit.WireUse, Fintype.card_sigma, Circuit.totalFanIn,
    Program.totalFanIn_eq_sum_lines]

/-- Every wire-use occurrence reads exactly one wire. -/
theorem Circuit.sum_wireUses (c : Circuit σ n m) :
    ∑ w : Wire n c.size, c.wireUses w = c.totalFanIn + m := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset c.WireUse) (Finset.univ : Finset (Wire n c.size)) c.useWire
  simpa [Circuit.wireUses, c.card_wireUse] using h

/-- Splitting the wires into inputs and gates preserves the total number of uses. -/
theorem Circuit.inputUses_add_sum_gate_uses (c : Circuit σ n m) :
    c.inputUses + ∑ j : Fin c.size, c.wireUses (.gate j) = c.totalFanIn + m := by
  rw [← c.sum_wireUses]
  have h := Fintype.sum_equiv (Wire.equiv n c.size) c.wireUses
    (Sum.elim (fun i => c.wireUses (.input i)) (fun j => c.wireUses (.gate j)))
    (by intro w; cases w <;> rfl)
  simpa [Fintype.sum_sum_type, Circuit.inputUses] using h.symm

/-- Without unused gates, the first use of each gate accounts for exactly `size` uses. -/
theorem Circuit.sum_gate_uses_eq (c : Circuit σ n m) (used : c.NoUnusedGates) :
    (∑ j : Fin c.size, c.wireUses (.gate j)) = c.excessFanout + c.size := by
  have h (j : Fin c.size) : c.wireUses (.gate j) = (c.wireUses (.gate j) - 1) + 1 := by
    have := used j
    omega
  calc
    (∑ j : Fin c.size, c.wireUses (.gate j)) =
        ∑ j : Fin c.size, ((c.wireUses (.gate j) - 1) + 1) :=
      Finset.sum_congr rfl fun j _ => h j
    _ = c.excessFanout + c.size := by simp [Finset.sum_add_distrib, Circuit.excessFanout]

/-- Bounded fan-in bounds the total number of gate argument slots. -/
theorem Circuit.totalFanIn_le_of_fanInAtMost (c : Circuit σ n m) {r : ℕ}
    (bounded : c.FanInAtMost r) : c.totalFanIn ≤ r * c.size := by
  rcases c with ⟨p, outputs⟩
  change p.totalFanIn ≤ r * _
  dsimp only
  change p.FanInAtMost r at bounded
  clear outputs
  induction p with
  | empty => simp
  | @gate g p line ih =>
    obtain ⟨prior, last⟩ := bounded
    simpa [Nat.mul_add] using Nat.add_le_add (ih prior) last

end Cslib.Circuits
