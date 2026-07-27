/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Defs
public import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Defs

/-!
# Numeric initialization schedule for direct tableau serialization

This definitions layer flattens the positive-input initialization fragment
into state, head, and cell segments. Variable schedule data consists only of
natural-number indices and positions. Machine states remain fixed finite
parameters, and symbol order is baked into four-gate cell blocks.

Input cells are separated into the left marker, data positions `1, ..., n`,
and the blank tail. Work and output tapes share one blank-tape schedule. No
run-time schedule value stores a configuration atom or formula tree.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Concatenate `count` blocks supplied by an increasing natural index. -/
def indexedGateBlocks : (count : ℕ) → (ℕ → CircuitCode.RawCircuit) →
    CircuitCode.RawCircuit
  | 0, _ => []
  | count + 1, blockAt =>
      blockAt 0 ++ indexedGateBlocks count (fun index => blockAt (index + 1))

/-- One raw constant gate using existing wire zero. -/
def directInitConstant (value : Bool) : CircuitCode.RawGate :=
  CircuitCode.RawGate.constant 0 value

/-- Symbol gates for a left-marker cell, in zero/one/blank/start order. -/
def directInitStartCell : CircuitCode.RawCircuit :=
  [directInitConstant false, directInitConstant false,
    directInitConstant false, directInitConstant true]

/-- Symbol gates for a blank cell, in zero/one/blank/start order. -/
def directInitBlankCell : CircuitCode.RawCircuit :=
  [directInitConstant false, directInitConstant false,
    directInitConstant true, directInitConstant false]

/-- Symbol gates for one data cell whose source is primary wire `inputIndex`. -/
def directInitDataCell (inputIndex : ℕ) : CircuitCode.RawCircuit :=
  [CircuitCode.RawGate.copy inputIndex true,
    CircuitCode.RawGate.copy inputIndex,
    directInitConstant false, directInitConstant false]

/-- Initial-state one-hot gates in the machine's fixed finite-state order. -/
noncomputable def directInitStateGates (tm : TM k) : CircuitCode.RawCircuit :=
  List.ofFn fun index : Fin (Fintype.card tm.Q) =>
    directInitConstant
      (decide (tm.qstart = (Fintype.equivFin tm.Q).symm index))

/-- One head-position gate: exactly position zero is initially active. -/
def directInitHeadGate (position : ℕ) : CircuitCode.RawGate :=
  directInitConstant (decide (position = 0))

/-- Initial head gates for one tape, at positions `0, ..., T`. -/
def directInitHeadTapeGates (T : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks (T + 1) fun position => [directInitHeadGate position]

/-- Initial head gates in input/work/output tape-major order. -/
def directInitHeadGates (k T : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks (k + 2) fun _ => directInitHeadTapeGates T

/-- Input data-cell gates for positions `1, ..., n`; block index `i` reads wire `i`. -/
def directInitInputDataGates (n : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks n directInitDataCell

/-- Blank input-cell gates for positions `n + 1, ..., T + 1`. -/
def directInitInputBlankTailGates (T n : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks (T + 1 - n) fun _ => directInitBlankCell

/-- Complete input-tape cell segment: marker, data, then blank tail. -/
def directInitInputCellGates (T n : ℕ) : CircuitCode.RawCircuit :=
  directInitStartCell ++ directInitInputDataGates n ++
    directInitInputBlankTailGates T n

/-- Cell segment for one initially blank work or output tape. -/
def directInitBlankTapeCellGates (T : ℕ) : CircuitCode.RawCircuit :=
  directInitStartCell ++
    indexedGateBlocks (T + 1) fun _ => directInitBlankCell

/-- Cell gates for all work tapes followed by the output tape. -/
def directInitWritableCellGates (k T : ℕ) : CircuitCode.RawCircuit :=
  indexedGateBlocks (k + 1) fun _ => directInitBlankTapeCellGates T

/-- Complete direct positive-input initialization schedule. -/
noncomputable def directInitSchedule (tm : TM k) (T n : ℕ) :
    CircuitCode.RawCircuit :=
  directInitStateGates tm ++ directInitHeadGates k T ++
    directInitInputCellGates T n ++ directInitWritableCellGates k T

end Serializer

end CircuitUnrolling

end Complexity
