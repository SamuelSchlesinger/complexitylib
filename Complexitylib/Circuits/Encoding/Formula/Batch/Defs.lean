/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Encoding.Formula.Defs

/-!
# Batch compilation of Boolean formulas

This file defines small finite conjunction and disjunction constructors and a
proof-free batch compiler for `BoolFormula`. Every formula in a batch is
compiled against the same incoming wire prefix. The individual formula
outputs are then copied into one contiguous block, in list order.

The contiguous block is the key interface for clients that represent a
structured value by many Boolean formulas: later fragments can address the
result by a base wire and an index without retaining the variable-sized
offset of every formula tree.
-/

@[expose] public section

namespace Complexity

namespace BoolFormula

/-- A Boolean literal testing whether an existing wire has the requested value. -/
def literal (wire : ℕ) (value : Bool) : BoolFormula :=
  if value then .var wire else .neg (.var wire)

/-- Conjoin a finite list of formulas. The empty conjunction is true. -/
def conjs : List BoolFormula → BoolFormula
  | [] => .tru
  | formula :: formulas => .conj formula (conjs formulas)

/-- Disjoin a finite list of formulas. The empty disjunction is false. -/
def disjs : List BoolFormula → BoolFormula
  | [] => .fls
  | formula :: formulas => .disj formula (disjs formulas)

/-- Raw formulas compiled in sequence, together with their absolute output wires. -/
structure RawBatchBuild where
  /-- The concatenated formula fragments, before output packing. -/
  circuit : CircuitCode.RawCircuit
  /-- One absolute output wire per source formula, in source order. -/
  outputs : List ℕ

/-- Compile formulas successively, recording each variable-sized output wire.

Every formula may refer only to wires in the prefix present at the start of
the whole batch. The increasing `available` parameter is used solely to place
the emitted fragments after one another. -/
def compileRawOutputs (available : ℕ) : List BoolFormula → RawBatchBuild
  | [] => ⟨[], []⟩
  | formula :: formulas =>
      let tail := compileRawOutputs (available + formula.size) formulas
      { circuit := compileRaw available formula ++ tail.circuit
        outputs := rawOutputWire available formula :: tail.outputs }

/-- First wire of the packed output block of a formula batch. -/
def rawBatchOutputBase (available : ℕ) (formulas : List BoolFormula) : ℕ :=
  available + (formulas.map size).sum

/-- Compile formulas successively and copy their results into a contiguous block. -/
def compileRawBatch (available : ℕ) (formulas : List BoolFormula) :
    CircuitCode.RawCircuit :=
  let built := compileRawOutputs available formulas
  built.circuit ++ built.outputs.map CircuitCode.RawGate.copy

end BoolFormula

end Complexity
