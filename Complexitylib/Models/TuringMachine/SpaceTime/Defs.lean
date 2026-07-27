/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite observations of space-bounded transducer configurations

This file defines the finite snapshots used to turn an auxiliary-space bound
for a deterministic transducer into a time bound. A work tape whose head stays
within `space` is observed only through that bounded head position and the
cells through `space`. The input is read-only, so its head position suffices.
For the one-way output tape, only whether the head is at the left marker and
the symbol currently under the head can affect future execution.

## Main definitions

- `Tape.BoundedObs` — the finite observable part of a space-bounded tape
- `Tape.boundedObs` — observe a tape whose head satisfies the space bound
- `TM.TransducerSnapshot` — the finite observable part of a transducer configuration
- `TM.transducerSnapshot` — observe a configuration within auxiliary space
- `TM.transducerConfigBound` — the number of possible transducer snapshots
-/

@[expose] public section

namespace Complexity

namespace Γ

/-- The fixed tape alphabet has four symbols. -/
@[simp] theorem card : Fintype.card Γ = 4 := by decide

end Γ

namespace Tape

/-- The observable part of a tape whose head never travels beyond `space`.
It records the bounded head position and every cell the head can visit. -/
abbrev BoundedObs (space : ℕ) :=
  Fin (space + 1) × (Fin (space + 1) → Γ)

/-- Restrict a tape to the cells visible under a given head-space bound. -/
def boundedObs (t : Tape) (space : ℕ) (h : t.head ≤ space) : BoundedObs space :=
  (⟨t.head, Nat.lt_succ_iff.mpr h⟩, fun i => t.cells i)

/-- The exact number of bounded observations of one work tape. -/
theorem card_boundedObs (space : ℕ) :
    Fintype.card (BoundedObs space) = (space + 1) * 4 ^ (space + 1) := by
  simp [BoundedObs]

end Tape

namespace TM

/-- The finite observable part of a space-bounded transducer configuration.

The output position and written prefix are deliberately absent: for a one-way
output tape, future execution can inspect only whether the head is still on
the exceptional left-marker cell and the symbol under its current head. -/
abbrev TransducerSnapshot (tm : TM k) (inputLength space : ℕ) :=
  tm.Q × Fin (inputLength + space + 2) ×
    (Fin k → Tape.BoundedObs space) × Bool × Γ

/-- Observe the finite part of a configuration satisfying an auxiliary-space
bound. The output-head zero flag distinguishes the immutable left-marker cell
from ordinary output cells. -/
def transducerSnapshot (tm : TM k) (c : Cfg k tm.Q) (inputLength space : ℕ)
    (hspace : c.WithinAuxSpace inputLength space) :
    tm.TransducerSnapshot inputLength space :=
  (c.state,
    ⟨c.input.head, Nat.lt_succ_iff.mpr hspace.2⟩,
    fun i => Tape.boundedObs (c.work i) space (hspace.1 i),
    decide (c.output.head = 0),
    c.output.read)

/-- A concrete upper bound on the number of finite snapshots of a `k`-work-tape
transducer using auxiliary space `space` on inputs of length `inputLength`. -/
def transducerConfigBound (tm : TM k) (inputLength space : ℕ) : ℕ :=
  8 * Fintype.card tm.Q * (inputLength + space + 2) *
    (((space + 1) * 4 ^ (space + 1)) ^ k)

/-- `transducerConfigBound` is the exact cardinality of the snapshot type. -/
theorem card_transducerSnapshot (tm : TM k) (inputLength space : ℕ) :
    Fintype.card (tm.TransducerSnapshot inputLength space) =
      tm.transducerConfigBound inputLength space := by
  simp [TransducerSnapshot, transducerConfigBound]
  ac_rfl

end TM

end Complexity
