/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Initialization.Internal

/-!
# Numeric initialization schedule for direct tableau serialization

This module exposes the state, head, input-cell, and writable-cell segments of
the direct deterministic initialization fragment. Its variable indices are
natural numbers; machine states and symbols occur only as fixed finite
parameters or in proof adapters.

The final equality is intentionally literal equality of raw gate lists. It
does not yet construct a Turing machine that emits those gates.

## Main results

- `length_directInitSchedule` gives the exact configuration-block width.
- `getElem_directInitSchedule_configIndex` identifies every scheduled gate.
- `directInitSchedule_eq_initFragment` identifies the schedule with the
  existing positive-input initialization fragment.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- An indexed concatenation of fixed-width blocks has the expected length. -/
@[simp] theorem length_indexedGateBlocks
    (count width : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hlen : ∀ index < count, (blockAt index).length = width) :
    (indexedGateBlocks count blockAt).length = count * width :=
  length_indexedGateBlocks_internal count width blockAt hlen

/-- A numeric block index and in-block offset recover the corresponding gate. -/
theorem getElem_indexedGateBlocks
    (count width : ℕ) (blockAt : ℕ → CircuitCode.RawCircuit)
    (hlen : ∀ index < count, (blockAt index).length = width)
    (blockIndex offset : ℕ) (hblock : blockIndex < count)
    (hoffset : offset < width) :
    (indexedGateBlocks count blockAt)[blockIndex * width + offset]'(by
      rw [length_indexedGateBlocks count width blockAt hlen]
      nlinarith) =
      (blockAt blockIndex)[offset]'(by
        rw [hlen blockIndex hblock]
        exact hoffset) :=
  getElem_indexedGateBlocks_internal count width blockAt hlen blockIndex
    offset hblock hoffset

@[simp] theorem length_directInitStartCell :
    directInitStartCell.length = 4 :=
  length_directInitStartCell_internal

@[simp] theorem length_directInitBlankCell :
    directInitBlankCell.length = 4 :=
  length_directInitBlankCell_internal

@[simp] theorem length_directInitDataCell (inputIndex : ℕ) :
    (directInitDataCell inputIndex).length = 4 :=
  length_directInitDataCell_internal inputIndex

@[simp] theorem length_directInitStateGates (tm : TM k) :
    (directInitStateGates tm).length = Fintype.card tm.Q :=
  length_directInitStateGates_internal tm

@[simp] theorem length_directInitHeadTapeGates (T : ℕ) :
    (directInitHeadTapeGates T).length = T + 1 :=
  length_directInitHeadTapeGates_internal T

@[simp] theorem length_directInitHeadGates (k T : ℕ) :
    (directInitHeadGates k T).length = (k + 2) * (T + 1) :=
  length_directInitHeadGates_internal k T

@[simp] theorem length_directInitInputDataGates (n : ℕ) :
    (directInitInputDataGates n).length = 4 * n :=
  length_directInitInputDataGates_internal n

@[simp] theorem length_directInitInputBlankTailGates (T n : ℕ) :
    (directInitInputBlankTailGates T n).length = 4 * (T + 1 - n) :=
  length_directInitInputBlankTailGates_internal T n

/-- The marker, data, and blank-tail input ranges cover exactly one tape. -/
@[simp] theorem length_directInitInputCellGates (T n : ℕ)
    (hn : n ≤ T + 1) :
    (directInitInputCellGates T n).length = 4 * (T + 2) :=
  length_directInitInputCellGates_internal T n hn

@[simp] theorem length_directInitBlankTapeCellGates (T : ℕ) :
    (directInitBlankTapeCellGates T).length = 4 * (T + 2) :=
  length_directInitBlankTapeCellGates_internal T

@[simp] theorem length_directInitWritableCellGates (k T : ℕ) :
    (directInitWritableCellGates k T).length = 4 * (k + 1) * (T + 2) :=
  length_directInitWritableCellGates_internal k T

/-- The four concatenated ranges occupy exactly one configuration block. -/
@[simp] theorem length_directInitSchedule (tm : TM k) (T n : ℕ)
    (hn : n ≤ T + 1) :
    (directInitSchedule tm T n).length = configWidth tm.toNTM T :=
  length_directInitSchedule_internal tm T n hn

/-- Every canonical configuration index selects its intended initialization
gate. `ConfigAtom` is used only to state the proof adapter, not as schedule
run-time state. -/
theorem getElem_directInitSchedule_configIndex
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n ≤ T + 1)
    (atom : ConfigAtom tm.toNTM T) :
    (directInitSchedule tm T n)[configIndex tm.toNTM T atom]'(by
      rw [length_directInitSchedule tm T n hn]
      exact configIndex_lt tm.toNTM T atom) =
      (initSource tm.toNTM T n n (deterministicInputWires T n) atom).gate :=
  getElem_directInitSchedule_configIndex_internal tm T n hn atom

/-- Under the normalized positive-input horizon bound, the numeric schedule is
literally the existing initialization fragment's raw gate list. -/
theorem directInitSchedule_eq_initFragment
    (tm : TM k) (T n : ℕ) [NeZero n] (hn : n + 1 ≤ T) :
    directInitSchedule tm T n =
      initFragment tm.toNTM T n n (deterministicInputWires T n) :=
  directInitSchedule_eq_initFragment_internal tm T n hn

end Serializer

end CircuitUnrolling

end Complexity
