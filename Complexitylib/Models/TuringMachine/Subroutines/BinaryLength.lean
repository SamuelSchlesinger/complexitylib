/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Models.TuringMachine.Experimental.Routine
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength.Defs
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength.Internal

/-!
# Binary input-length counter

This module exposes a read-only input scan that counts every Boolean input
symbol in canonical little-endian binary on one designated work tape. The
machine preserves input cells; output and unrelated work tapes remain blank
and finish with their heads initialized at cell one.

The resource contracts are deliberately separate: the runtime theorem gives
an `n · size(n)`-shaped bound, while the all-reachable auxiliary-space proof
reuses the local successor bound at each iteration and is formally `O(log n)`.

## Main results

- `TM.binaryLengthTM_reachesIn_frame` — exact endpoint and complete tape frame.
- `TM.binaryLengthTM_hoareTimeSpace` — time-bounded and all-reachable space contract.
- `TM.binaryLengthSpace_bigO_log` — the explicit space budget is logarithmic.
- `TM.Experimental.binaryLengthRoutine_transducerSafe` — the experimental routine is
  structurally output-safe.
- `TM.binaryLengthTM_isTransducer` — the output head never moves left.
-/

@[expose] public section

namespace Complexity

namespace TM

/-- The exact binary-length-counter runtime has a concrete `O(n log n)`-shaped
upper bound. -/
theorem binaryLengthTime_le (length : ℕ) :
    binaryLengthTime length ≤ 2 + length * (2 * length.size + 4) :=
  binaryLengthTime_le_internal length

/-- The explicit all-reachable auxiliary-space budget is logarithmic. -/
theorem binaryLengthSpace_bigO_log :
    binaryLengthSpace =O (fun length => Nat.log 2 length) :=
  binaryLengthSpace_bigO_log_internal

/-- From fresh tapes, the machine halts after exactly `binaryLengthTime`
transitions with the canonical binary input length on `counterIdx`. Input
cells are preserved exactly; output and unrelated work tapes remain blank and
finish with their heads at cell one. -/
theorem binaryLengthTM_reachesIn_frame {n : ℕ} (counterIdx : Fin n)
    (x : List Bool) :
    ∃ c',
      (binaryLengthTM counterIdx).reachesIn (binaryLengthTime x.length)
        ((binaryLengthTM counterIdx).initCfg x) c' ∧
      (binaryLengthTM counterIdx).halted c' ∧
      c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      c'.input.head = x.length + 1 ∧
      (c'.work counterIdx).HasBinaryNat x.length ∧
      (∀ i, i ≠ counterIdx →
        c'.work i = (Tape.init []).move Dir3.right) ∧
      c'.output = (Tape.init []).move Dir3.right :=
  binaryLengthTM_reachesIn_frame_internal counterIdx x

/-- Fresh-start time-bounded Hoare contract for binary length counting. -/
theorem binaryLengthTM_hoareTime {n : ℕ} (counterIdx : Fin n)
    (x : List Bool) :
    (binaryLengthTM counterIdx).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work counterIdx).HasBinaryNat x.length ∧
        (∀ i, i ≠ counterIdx →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (binaryLengthTime x.length) :=
  binaryLengthTM_hoareTime_internal counterIdx x

/-- Time-bounded and honest all-reachable auxiliary-space contract. In
particular, this does not derive space from the total runtime. -/
theorem binaryLengthTM_hoareTimeSpace {n : ℕ} (counterIdx : Fin n)
    (x : List Bool) :
    (binaryLengthTM counterIdx).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work counterIdx).HasBinaryNat x.length ∧
        (∀ i, i ≠ counterIdx →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (binaryLengthTime x.length) x.length (binaryLengthSpace x.length) :=
  binaryLengthTM_hoareTimeSpace_internal counterIdx x

/-- Binary length counting is assembled only from transducer-safe routine
constructors and calls. -/
theorem Experimental.binaryLengthRoutine_transducerSafe {n : ℕ}
    (counterIdx : Fin n) :
    (Experimental.binaryLengthRoutine counterIdx).TransducerSafe :=
  Experimental.binaryLengthRoutine_transducerSafe_internal counterIdx

/-- `binaryLengthTM` is safe for append-only-output composition. -/
theorem binaryLengthTM_isTransducer {n : ℕ} (counterIdx : Fin n) :
    (binaryLengthTM counterIdx).IsTransducer :=
  binaryLengthTM_isTransducer_internal counterIdx

end TM

end Complexity
