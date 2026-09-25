/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Reduction

/-!
# Proof-carrying program compaction

Programs are rebuilt from left to right. A source gate is either copied to the
new program or identified with an existing wire. The constructors hide all
dependent `Fin` transport and preserve the complete source trace.
-/

@[expose] public section

namespace Algebraic

/-- A semantics-preserving rebuilding of a program with no additional gates. -/
structure _root_.Cslib.Circuits.Program.Compaction
    (source : Program σ n g)
    (interpretation : Interpretation σ U) where
  /-- Number of gates in the rebuilt program. -/
  gateCount : Nat
  /-- Rebuilt program. -/
  result : Program σ n gateCount
  /-- Translation of every source wire to its representative. -/
  wireMap : Wire.Renaming n g gateCount
  /-- Every translated wire computes its original value. -/
  trace_eq : ∀ input wire,
    result.trace interpretation input (wireMap wire) =
      source.trace interpretation input wire
  /-- The rebuilt program has no more gates than the source. -/
  gateCount_le : gateCount ≤ g
  /-- Compaction does not increase any nonnegative operation cost. -/
  cost_le : ∀ operationCost : OperationCost σ,
    result.cost operationCost ≤ source.cost operationCost

export Cslib.Circuits (Program.Compaction)

/-- A semantics-preserving circuit compaction that does not increase cost. -/
structure _root_.Cslib.Circuits.Circuit.Compaction
    (source : Circuit σ n g m)
    (interpretation : Interpretation σ U) where
  /-- Number of internal gates in the rebuilt circuit. -/
  gateCount : Nat
  /-- Rebuilt circuit. -/
  result : Circuit σ n gateCount m
  /-- Pointwise semantic preservation. -/
  eval_eq : ∀ input, result.eval interpretation input =
    source.eval interpretation input
  /-- The rebuilt circuit has no more internal gates than the source. -/
  gateCount_le : gateCount ≤ g
  /-- Compaction does not increase any nonnegative operation cost. -/
  cost_le : ∀ operationCost : OperationCost σ,
    result.cost operationCost ≤ source.cost operationCost

export Cslib.Circuits (Circuit.Compaction)

namespace Program.Compaction

variable {σ : Signature} {n g m : Nat} {U : Type u}
variable {source : Program σ n g}
variable {interpretation : Interpretation σ U}

/-- The empty program compacts to itself. -/
def _root_.Cslib.Circuits.Program.Compaction.empty {σ : Signature} {n : Nat} {U : Type u}
    (interpretation : Interpretation σ U) :
    Program.Compaction (Program.empty : Program σ n 0) interpretation where
  gateCount := 0
  result := .empty
  wireMap := Wire.Renaming.id
  trace_eq := by
    intro input wire
    simp
  gateCount_le := Nat.le_refl 0
  cost_le := fun _ => Nat.le_refl 0

export Cslib.Circuits.Program.Compaction (empty)

/-- Evaluation of a line is preserved after mapping it through a compaction. -/
theorem _root_.Cslib.Circuits.Program.Compaction.mapLine_eval
    (compaction : Program.Compaction source interpretation)
    (line : Line σ n g)
    (input : Fin n → U) :
    (line.mapWires compaction.wireMap).eval interpretation input
        (compaction.result.eval interpretation input) =
      line.eval interpretation input (source.eval interpretation input) := by
  apply line.eval_mapRenaming
  intro gate
  simpa only [Program.trace, Wire.Renaming.apply_gate,
    Fin.addCases_right] using
    compaction.trace_eq input (Wire.gate gate)

export Cslib.Circuits.Program.Compaction (mapLine_eval)

/-- Retain the new last source gate in the rebuilt program. -/
def _root_.Cslib.Circuits.Program.Compaction.copy
    (compaction : Program.Compaction source interpretation)
    (line : Line σ n g) :
    Program.Compaction (source.gate line) interpretation := by
  let mappedLine := line.mapWires compaction.wireMap
  exact
    { gateCount := compaction.gateCount + 1
      result := compaction.result.gate mappedLine
      wireMap := compaction.wireMap.appendLast
      trace_eq := by
        intro input wire
        refine Fin.lastCases ?_ (fun priorWire => ?_) wire
        · calc
            (compaction.result.gate mappedLine).trace interpretation input
                (compaction.wireMap.appendLast (Fin.last (n + g))) =
              (compaction.result.gate mappedLine).trace interpretation input
                (Wire.gate (Fin.last compaction.gateCount)) := congrArg
                  ((compaction.result.gate mappedLine).trace interpretation input)
                  (Wire.Renaming.appendLast_lastWire compaction.wireMap)
            _ = (compaction.result.gate mappedLine).gateFunction interpretation
                (Fin.last compaction.gateCount) input := by
              rw [Program.trace_gateWire]
            _ = mappedLine.eval interpretation input
                (compaction.result.eval interpretation input) := by
              rw [Program.gateFunction_gate_last]
            _ = line.eval interpretation input
                (source.eval interpretation input) :=
              compaction.mapLine_eval line input
            _ = (source.gate line).trace interpretation input
                (Fin.last (n + g)) :=
              (Program.trace_gate_last source line interpretation input).symm
        · rw [Wire.Renaming.appendLast_castSucc,
            Program.trace_gate_castSucc, Program.trace_gate_castSucc]
          exact compaction.trace_eq input priorWire
      gateCount_le := Nat.add_le_add_right compaction.gateCount_le 1
      cost_le := by
        intro operationCost
        simp only [Program.cost_gate]
        exact Nat.add_le_add_right
          (compaction.cost_le operationCost) (operationCost line.op) }

export Cslib.Circuits.Program.Compaction (copy)

/-- Replace the new last source gate by an existing rebuilt wire. -/
def _root_.Cslib.Circuits.Program.Compaction.eliminate
    (compaction : Program.Compaction source interpretation)
    (line : Line σ n g)
    (replacement : Wire n compaction.gateCount)
    (replacement_eq : ∀ input,
      compaction.result.trace interpretation input replacement =
        (line.mapWires compaction.wireMap).eval interpretation input
          (compaction.result.eval interpretation input)) :
    Program.Compaction (source.gate line) interpretation where
  gateCount := compaction.gateCount
  result := compaction.result
  wireMap := compaction.wireMap.skipLast replacement
  trace_eq := by
    intro input wire
    refine Fin.lastCases ?_ (fun priorWire => ?_) wire
    · calc
        compaction.result.trace interpretation input
            (compaction.wireMap.skipLast replacement (Fin.last (n + g))) =
          compaction.result.trace interpretation input replacement := congrArg
            (compaction.result.trace interpretation input)
            (Wire.Renaming.skipLast_lastWire compaction.wireMap replacement)
        _ = (line.mapWires compaction.wireMap).eval interpretation input
            (compaction.result.eval interpretation input) := replacement_eq input
        _ = line.eval interpretation input
            (source.eval interpretation input) :=
          compaction.mapLine_eval line input
        _ = (source.gate line).trace interpretation input
            (Fin.last (n + g)) :=
          (Program.trace_gate_last source line interpretation input).symm
    · rw [Wire.Renaming.skipLast_castSucc, Program.trace_gate_castSucc]
      exact compaction.trace_eq input priorWire
  gateCount_le := compaction.gateCount_le.trans (Nat.le_succ g)
  cost_le := by
    intro operationCost
    exact (compaction.cost_le operationCost).trans
      (Nat.le_add_right _ (operationCost line.op))

export Cslib.Circuits.Program.Compaction (eliminate)

/-- Lift a program compaction to a circuit by renaming its output wires. -/
def _root_.Cslib.Circuits.Program.Compaction.toCircuit
    {circuit : Circuit σ n g m}
    (compaction : Program.Compaction circuit.program interpretation) :
    Circuit.Compaction circuit interpretation := by
  let result : Circuit σ n compaction.gateCount m :=
    { program := compaction.result
      outputs := fun output =>
        compaction.wireMap (circuit.outputs output) }
  exact
    { gateCount := compaction.gateCount
      result := result
      eval_eq := by
        intro input
        funext output
        exact compaction.trace_eq input (circuit.outputs output)
      gateCount_le := compaction.gateCount_le
      cost_le := by
        intro operationCost
        exact compaction.cost_le operationCost }

export Cslib.Circuits.Program.Compaction (toCircuit)

end Program.Compaction

namespace Circuit.Compaction

variable {σ : Signature} {n g m : Nat} {U : Type u}
variable {source : Circuit σ n g m}
variable {interpretation : Interpretation σ U}

/-- View a compaction as a certified identity-substitution reduction. -/
def _root_.Cslib.Circuits.Circuit.Compaction.toReduction
    (compaction : Circuit.Compaction source interpretation)
    (operationCost : OperationCost σ) :
    Circuit.Reduction operationCost source interpretation
      InputSubstitution.id where
  gateCount := compaction.gateCount
  result := compaction.result
  eval_eq := by
    intro input
    simpa using compaction.eval_eq input
  saving := source.cost operationCost - compaction.result.cost operationCost
  saving_le := by
    rw [Nat.sub_add_cancel (compaction.cost_le operationCost)]

export Cslib.Circuits.Circuit.Compaction (toReduction)

end Circuit.Compaction

end Algebraic
