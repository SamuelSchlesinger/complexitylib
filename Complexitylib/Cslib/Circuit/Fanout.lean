/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
public import Complexitylib.Cslib.Circuit.Fanout.Defs
public import Complexitylib.Cslib.Circuit.Fanout.Internal
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Wire accounting and shared gates

For a circuit with no unused gates, let `w` count original input occurrences
and let `e` sum each gate's uses beyond its first. Double counting gives
`w + e + size = totalFanIn + outputCount`. Thus a binary single-output
circuit satisfies `w + e = size + 1`. Every shared gate contributes at least
one to `e`, so `w + sharedGates.card ≤ size + 1` as well.

Uses include designated outputs and count repeated gate arguments separately.
No assumption of distinct arguments, Boolean values, positive input count, or
gated outputs is needed. The no-unused-gates hypothesis is essential to the
balance equation: an unused gate has no first use to subtract.

These generic extensions of CSLib's circuit model are candidates for
upstreaming. They count structural sharing, without assigning a semantic or
communication cost to a shared gate.
-/

@[expose] public section

namespace Cslib.Circuits

open scoped BigOperators

variable {σ : Signature} {n m : ℕ}

/-- Exact wire-use accounting for a circuit without unused gates. -/
theorem Circuit.wire_use_balance (c : Circuit σ n m) (used : c.NoUnusedGates) :
    c.inputUses + c.excessFanout + c.size = c.totalFanIn + m := by
  have h := c.inputUses_add_sum_gate_uses
  rw [c.sum_gate_uses_eq used] at h
  simpa only [Nat.add_assoc] using h

/-- Each shared gate contributes at least one use beyond its first. -/
theorem Circuit.card_sharedGates_le_excessFanout (c : Circuit σ n m) :
    c.sharedGates.card ≤ c.excessFanout := by
  simp only [Circuit.sharedGates, Finset.card_eq_sum_ones, Finset.sum_filter,
    Circuit.excessFanout]
  apply Finset.sum_le_sum
  intro j _
  split_ifs with h <;> omega

/-- Exact binary fan-in turns wire accounting into `w + e = size + outputCount`. -/
theorem Circuit.inputUses_add_excessFanout_eq (c : Circuit σ n m)
    (used : c.NoUnusedGates) (binary : ∀ j, σ.Arity (c.program.lines j).op = 2) :
    c.inputUses + c.excessFanout = c.size + m := by
  have fanin : c.totalFanIn = 2 * c.size := by
    simp [Circuit.totalFanIn, Program.totalFanIn_eq_sum_lines, binary, Nat.mul_comm]
  have balance := c.wire_use_balance used
  omega

/-- Fan-in at most two bounds input occurrences plus excess gate uses. -/
theorem Circuit.inputUses_add_excessFanout_le (c : Circuit σ n m)
    (used : c.NoUnusedGates) (bounded : c.FanInAtMost 2) :
    c.inputUses + c.excessFanout ≤ c.size + m := by
  have balance := c.wire_use_balance used
  have fanin := c.totalFanIn_le_of_fanInAtMost bounded
  omega

/-- In fan-in-two circuits, shared gates consume the same budget as input occurrences. -/
theorem Circuit.inputUses_add_card_sharedGates_le (c : Circuit σ n m)
    (used : c.NoUnusedGates) (bounded : c.FanInAtMost 2) :
    c.inputUses + c.sharedGates.card ≤ c.size + m :=
  (Nat.add_le_add_left c.card_sharedGates_le_excessFanout _).trans
    (c.inputUses_add_excessFanout_le used bounded)

end Cslib.Circuits
