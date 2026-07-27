/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Stream.Defs

/-!
# Numeric schedules for streaming tableau serialization

This definitions layer isolates two variable-length pieces of raw formula
compilation as schedules driven only by natural-number counters and a numeric
size oracle. A future Turing-machine serializer can recompute that oracle from
its fixed formula templates; it never needs to store a `BoolFormula`, a raw
circuit, or a run-time syntax stack.

The right-fold schedule counts connector ranks upward while visiting source
members in reverse order. The batch-copy schedule counts source formulas
forward and reconstructs each delayed output reference from a prefix-size sum.
-/

@[expose] public section

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

/-- Sum the first `count` values of a numeric size oracle. -/
def prefixSize (sizeAt : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 => prefixSize sizeAt count + sizeAt count

/-- Source-member index visited at an upward-counting reverse rank. -/
def reverseMember (count rank : ℕ) : ℕ :=
  count - rank - 1

/-- Connector emitted at `rank` in a stack-free right-fold suffix.

For an in-range rank, `member = count - rank - 1`. The first input is the
member formula's output, while the second is the identity gate at rank zero
or the preceding connector thereafter. -/
def indexedRightFoldConnector (op : AndOrOp) (available count : ℕ)
    (sizeAt : ℕ → ℕ) (rank : ℕ) : CircuitCode.RawGate :=
  let member := reverseMember count rank
  { op := op
    input₀ := available + prefixSize sizeAt (member + 1) - 1
    input₁ := available + prefixSize sizeAt count + rank
    negated₀ := false
    negated₁ := false }

/-- Reverse connector suffix, indexed by an increasing natural rank. -/
def indexedRightFoldConnectors (op : AndOrOp) (available count : ℕ)
    (sizeAt : ℕ → ℕ) : CircuitCode.RawCircuit :=
  (List.range count).map (indexedRightFoldConnector op available count sizeAt)

/-- Delayed packed-output copy for the formula at a forward source index. -/
def indexedBatchCopy (available : ℕ) (sizeAt : ℕ → ℕ)
    (index : ℕ) : CircuitCode.RawGate :=
  CircuitCode.RawGate.copy
    (available + prefixSize sizeAt (index + 1) - 1)

/-- Delayed batch-copy suffix, indexed in forward source-formula order. -/
def indexedBatchCopies (available count : ℕ) (sizeAt : ℕ → ℕ) :
    CircuitCode.RawCircuit :=
  (List.range count).map (indexedBatchCopy available sizeAt)

end Serializer

end CircuitUnrolling

end Complexity
