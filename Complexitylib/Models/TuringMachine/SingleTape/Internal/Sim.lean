/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sum
public import Complexitylib.Models.TuringMachine

/-!
# Single-tape simulation — simulator state type

The state type `SimQ k Q` of `NTM.singleTapeSim` (for a source machine with
state type `Q` and `k` work tapes) and its `Fintype`/`DecidableEq` instances.
See `docs/A4-SingleTapeSimulation.md` §4–5 for the phase semantics.

The instances are **noncomputable** by design: `singleTapeSim` is a
`noncomputable def`, and synthesizing computable `DecidableEq` for the
function-typed phase data (`Fin k → Γ`, `Fin k → Γw × Dir3`) hits Lean's
product/`Pi` synthesis-size limit. `Finite` is a `Prop` and composes with no
such limit, so we route through it (`Fintype.ofFinite` / `Classical.decEq`).
-/


@[expose] public section

namespace Complexity

namespace NTM.SingleTape

/-- A sweep position: which tape's triple (`Fin k`) and which of its 3 cells
    (head-bit / sym-hi / sym-lo, as `Fin 3`). The tape index is `Fin (k+1)` — a
    *finite* type (so the state stays `Finite`) whose `0` is constructible even
    when `k = 0`; the slack index `k` is unused in normal sweeps, and updates
    into `Fin k`-indexed data are guarded by `if h : t.val < k`. -/
abbrev SweepPos (k : ℕ) := Fin (k + 1) × Fin 3

/-- GATHER-phase data: the simulated state `q`, the head symbols accumulated so
    far (`acc`), the input/output symbols read at macro-step start (kept for the
    `δ` computation and the `▷`-dodge), the current sweep position, a flag for
    whether the current tape's head marker was seen in this triple, and the
    pending high symbol cell read. -/
abbrev GatherData (k : ℕ) (Q : Type) := Q × (Fin k → Γ) × Γ × Γ × SweepPos k × Bool × Γ

/-- REWIND-phase data (between GATHER and SCATTER): the next state `q'`, the `δ`
    results carried leftward back to cell 1 — per-tape write+move action, the
    deferred output write/dir, input dir, original input/output symbols — and the
    initial `rightCarry` marking heads that were at position 0 (`acc = ▷`, forced
    right off `▷`), whose new marker must be deposited at block 1 by SCATTER. -/
abbrev RewindData (k : ℕ) (Q : Type) :=
  Q × (Fin k → Γw × Dir3) × (Γw × Dir3) × Dir3 × Γ × Γ × (Fin k → Bool)

/-- SCATTER sweep-1 data (rightward: write new symbols, place stay/right markers,
    materialize): the carried `δ` results, the sweep position, the per-tape
    `rightCarry` (markers to deposit at the next block), `isLeftMover` (recorded
    for sweep 2), and a `writeFlag` (currently overwriting a head's symbol). -/
abbrev Scatter1Data (k : ℕ) (Q : Type) :=
  Q × (Fin k → Γw × Dir3) × (Γw × Dir3) × Dir3 × Γ × Γ × SweepPos k ×
    (Fin k → Bool) × (Fin k → Bool) × Bool × Bool

/-- SCATTER sweep-2 data (leftward: deposit left-movers, rewind to cell 1): the
    deferred commit info, the sweep position, the `isLeftMover` set (from sweep
    1) and the per-tape `leftCarry` (markers to deposit at the next-left block). -/
abbrev Scatter2Data (k : ℕ) (Q : Type) :=
  Q × (Γw × Dir3) × Dir3 × Γ × Γ × SweepPos k × (Fin k → Bool) × (Fin k → Bool)

/-- COMMIT-phase data: the next simulated state and the deferred input/output
    actions (output write+dir, input dir) with the symbols originally read. -/
abbrev CommitData (Q : Type) := Q × Γw × Dir3 × Dir3 × Γ × Γ

/-- The simulator's state type. Phases (see `docs/A4`):
    `run → gather → rewind → scatter1 → scatter2 → commit → run`, plus `halt`. -/
abbrev SimQ (k : ℕ) (Q : Type) :=
  Q ⊕ GatherData k Q ⊕ RewindData k Q ⊕ Scatter1Data k Q ⊕ Scatter2Data k Q ⊕
    CommitData Q ⊕ Unit

namespace SimQ

variable {k : ℕ} {Q : Type}

/-- Between macro-steps, about to simulate an `N`-step from state `q`. -/
@[match_pattern] def run (q : Q) : SimQ k Q := Sum.inl q
/-- Rightward read sweep, gathering head symbols. -/
@[match_pattern] def gather (d : GatherData k Q) : SimQ k Q := Sum.inr (Sum.inl d)
/-- Leftward rewind back to cell 1, carrying the `δ` results. -/
@[match_pattern] def rewind (d : RewindData k Q) : SimQ k Q := Sum.inr (Sum.inr (Sum.inl d))
/-- Rightward write/marker sweep (stay/right moves + materialize). -/
@[match_pattern] def scatter1 (d : Scatter1Data k Q) : SimQ k Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl d)))
/-- Leftward marker sweep (left moves) + final rewind. -/
@[match_pattern] def scatter2 (d : Scatter2Data k Q) : SimQ k Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d))))
/-- Applying the deferred input/output actions. -/
@[match_pattern] def commit (d : CommitData Q) : SimQ k Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl d)))))
/-- The halt state. -/
@[match_pattern] def halt : SimQ k Q :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))

end SimQ

set_option synthInstance.maxSize 4000 in
/-- `Finite` composes freely (a `Prop`), so this synthesizes despite the
    function-typed phase data — the seven wide summands just need a raised
    instance-search size. -/
instance instFiniteSimQ (k : ℕ) (Q : Type) [Fintype Q] : Finite (SimQ k Q) := by
  infer_instance

/-- Noncomputable `Fintype` via `Finite` — sidesteps the product/`Pi`
    `DecidableEq` synthesis limit. -/
noncomputable instance instFintypeSimQ (k : ℕ) (Q : Type) [Fintype Q] :
    Fintype (SimQ k Q) := Fintype.ofFinite _

/-- Noncomputable decidable equality — only used inside proofs (`trace`/`step`
    reduce `c.state = qhalt` in `Prop`), never executed. -/
noncomputable instance instDecidableEqSimQ (k : ℕ) (Q : Type) :
    DecidableEq (SimQ k Q) := Classical.decEq _

end NTM.SingleTape

end Complexity
