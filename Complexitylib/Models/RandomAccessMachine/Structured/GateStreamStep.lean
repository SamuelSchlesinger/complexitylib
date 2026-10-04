/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.RandomAccessMachine.Structured.GateStreamStep.Defs
public import Complexitylib.Models.RandomAccessMachine.Structured.GateStreamStep.Internal
public import Complexitylib.Models.RandomAccessMachine.Structured

/-!
# Verified structured RAM iterable serialized-gate step

This module exposes the split-layout gate routine used by the serialized-circuit
experiment. Code and mutable memo occupy disjoint regions, so the exact same
routine can be invoked again at the returned cursor.

The calling convention `Ready` constrains only the occupied memo cells, the
parser registers, and the code region; `ready_readyStore` exhibits a store
meeting it, together with the store envelope, for every gate, tail, and memo.
-/


public section

namespace Complexity

namespace RAM

namespace Structured

namespace GateStreamStep

/-- The calling convention is satisfiable for every gate, unread tail, and
memo: whenever the memo lies above the continuation cells and below the code,
the canonical `readyStore` satisfies `Ready` and the store envelope required by
`routine_correct` and `compiled_correct`. In particular both theorems apply to
AND and OR gates with arbitrary references and negation bits. -/
theorem ready_readyStore {gateStart base : ℕ} (gate : CircuitCode.RawGate)
    (tail wires : List Bool) (hbase : spillRemainingReg < base)
    (hcode : base + wires.length < gateStart) :
    Ready gateStart base gate tail wires
        (readyStore gateStart base gate tail wires) ∧
      Internal.StoreEnvelope (codeEnd gateStart gate tail)
        (codeEnd gateStart gate tail)
        (readyStore gateStart base gate tail wires) :=
  ⟨readyStore_ready_internal gate tail wires hbase hcode,
    readyStore_envelope_internal gate tail wires hbase hcode⟩

/-- Consume and evaluate one gate while preserving the unread code tail and
advancing the independent mutable memo. -/
theorem routine_correct {gateStart base : ℕ} {gate : CircuitCode.RawGate}
    {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store)
    (hbound : Internal.StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec routine store final (stepCount gate) cost space ∧
      final UnaryDecode.pointerReg = gateStart + gate.encode.length ∧
      final UnaryDecode.remainingReg = tail.length ∧
      final memoBaseReg = base ∧
      final wireCountMetaReg = wires.length + 1 ∧
      final (base + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ delta,
        final (gateStart + gate.encode.length + delta) =
          match tail[delta]? with
          | some bit => Input.bitValue bit
          | none => 0 :=
  routine_exec_internal hready hbound value0 value1 hvalue0 hvalue1

/-- Structural compilation transfers the exact iterable-gate execution,
including its logarithmic cost and peak-space measurements. -/
theorem compiled_correct {gateStart base : ℕ} {gate : CircuitCode.RawGate}
    {tail wires : List Bool} {store : Store}
    (hready : Ready gateStart base gate tail wires store)
    (hbound : Internal.StoreEnvelope (codeEnd gateStart gate tail)
      (codeEnd gateStart gate tail) store)
    (value0 value1 : Bool) (hvalue0 : wires[gate.input₀]? = some value0)
    (hvalue1 : wires[gate.input₁]? = some value1) :
    ∃ final cost space,
      Exec routine store final (stepCount gate) cost space ∧
      run compiled (stepCount gate) { pc := 0, regs := store } =
        { pc := routine.codeSize, regs := final } ∧
      Halted compiled
        (run compiled (stepCount gate) { pc := 0, regs := store }) ∧
      logTimeUpto compiled (stepCount gate) { pc := 0, regs := store } = cost ∧
      spaceUpto compiled (stepCount gate) { pc := 0, regs := store } = space ∧
      final UnaryDecode.pointerReg = gateStart + gate.encode.length ∧
      final UnaryDecode.remainingReg = tail.length ∧
      final memoBaseReg = base ∧
      final wireCountMetaReg = wires.length + 1 ∧
      final (base + wires.length) =
        Input.bitValue (gate.eval value0 value1) ∧
      (∀ index (hindex : index < wires.length),
        final (base + index) = Input.bitValue wires[index]) ∧
      ∀ delta,
        final (gateStart + gate.encode.length + delta) =
          match tail[delta]? with
          | some bit => Input.bitValue bit
          | none => 0 := by
  obtain ⟨final, cost, space, hexec, hpointer, hremaining, hbase,
      hcount, happended, hwires, htail⟩ :=
    routine_correct hready hbound value0 value1 hvalue0 hvalue1
  have hcompiled := Exec.compile_correct hexec
  exact ⟨final, cost, space, hexec, hcompiled.1, Exec.compile_halted hexec,
    hcompiled.2.1, hcompiled.2.2, hpointer, hremaining, hbase, hcount,
    happended, hwires, htail⟩

end GateStreamStep

end Structured

end RAM

end Complexity
