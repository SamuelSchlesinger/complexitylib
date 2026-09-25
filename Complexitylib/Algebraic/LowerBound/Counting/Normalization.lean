/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Counting.Basic
public import Complexitylib.Algebraic.Compaction
public import Cslib.Computability.Circuit.Normalization

/-!
# Semantic circuit normalization

Programs are hash-consed by the scalar functions computed at their gates. The
result computes the same values, has no duplicate gate functions, and never has
more gates. This is the semantic bridge needed for the factorial Shannon count.
-/

@[expose] public section

namespace Algebraic

/-! ## Program normalization -/

/-- The result and semantic invariant produced by hash-consing a program's gate
functions. -/
structure _root_.Cslib.Circuits.Program.Normalization
    (program : Program σ n g)
    (interpretation : Interpretation σ U) where
  /-- Number of gates after semantic hash-consing. -/
  gateCount : Nat
  /-- Program with pairwise distinct gate functions. -/
  result : Program σ n gateCount
  /-- Input-fixing translation of old wires to their representatives. -/
  wireMap : Wire.Renaming n g gateCount
  /-- Every translated wire computes its original value. -/
  trace_eq : ∀ input wire,
    result.trace interpretation input (wireMap wire) =
      program.trace interpretation input wire
  /-- No two retained gates compute the same scalar function. -/
  injective_gateFunction : Function.Injective (result.gateFunction interpretation)
  /-- Normalization never adds gates. -/
  gateCount_le : gateCount ≤ g
  /-- Normalization does not increase any nonnegative operation cost. -/
  cost_le : ∀ operationCost : OperationCost σ,
    result.cost operationCost ≤ program.cost operationCost

export Cslib.Circuits (Program.Normalization)

/-- Hash-cons a program by semantic gate function, preserving every wire value. -/
noncomputable def _root_.Cslib.Circuits.Program.normalize
    [Fintype U]
    (interpretation : Interpretation σ U) :
    (program : Program σ n g) → Program.Normalization program interpretation
  | .empty =>
      { gateCount := 0
        result := .empty
        wireMap := Wire.Renaming.id
        trace_eq := by
          intro input wire
          simp
        injective_gateFunction := fun impossible => Fin.elim0 impossible
        gateCount_le := Nat.le_refl 0
        cost_le := fun _ => Nat.le_refl 0 }
  | @Program.gate _ _ g program line => by
      classical
      let prior := program.normalize interpretation
      let priorCompaction : Program.Compaction program interpretation :=
        { gateCount := prior.gateCount
          result := prior.result
          wireMap := prior.wireMap
          trace_eq := prior.trace_eq
          gateCount_le := prior.gateCount_le
          cost_le := prior.cost_le }
      let mappedLine := line.mapWires prior.wireMap
      let freshFunction : ScalarFunction U n :=
        fun input => mappedLine.eval interpretation input
          (prior.result.eval interpretation input)
      by_cases duplicate : ∃ representative,
          prior.result.gateFunction interpretation representative = freshFunction
      · let representative := Classical.choose duplicate
        have representative_eq := Classical.choose_spec duplicate
        have replacement_eq (input : Fin n → U) :
            prior.result.trace interpretation input
                (Wire.gate (n := n) representative) =
              mappedLine.eval interpretation input
                (prior.result.eval interpretation input) := by
          rw [Program.trace_gateWire]
          exact congrFun representative_eq input
        let compacted := priorCompaction.eliminate line
          (Wire.gate (n := n) representative) replacement_eq
        exact
          { gateCount := prior.gateCount
            result := prior.result
            wireMap := prior.wireMap.skipLast
              (Wire.gate (n := n) representative)
            trace_eq := compacted.trace_eq
            injective_gateFunction := prior.injective_gateFunction
            gateCount_le := compacted.gateCount_le
            cost_le := compacted.cost_le }
      · exact
          let compacted := priorCompaction.copy line
          { gateCount := prior.gateCount + 1
            result := prior.result.gate mappedLine
            wireMap := prior.wireMap.appendLast
            trace_eq := compacted.trace_eq
            injective_gateFunction := by
              intro left right equal
              revert equal
              refine Fin.lastCases ?_ (fun leftPrior => ?_) left <;>
                refine Fin.lastCases ?_ (fun rightPrior => ?_) right
              · intro _
                rfl
              · intro equal
                exfalso
                apply duplicate
                refine ⟨rightPrior, ?_⟩
                simpa [freshFunction] using equal.symm
              · intro equal
                exfalso
                apply duplicate
                refine ⟨leftPrior, ?_⟩
                simpa [freshFunction] using equal
              · intro equal
                have same := prior.injective_gateFunction (by simpa using equal)
                subst rightPrior
                rfl
            gateCount_le := compacted.gateCount_le
            cost_le := compacted.cost_le }

/-! ## Circuit normalization -/

export Cslib.Circuits (Program.normalize)

/-- A semantics-preserving circuit normalization with pairwise distinct internal
gate functions. -/
structure _root_.Cslib.Circuits.Circuit.Normalization
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U) where
  /-- Number of internal gates after normalization. -/
  gateCount : Nat
  /-- The normalized circuit. -/
  result : Circuit σ n gateCount m
  eval_eq : result.eval interpretation = circuit.eval interpretation
  injective_gateFunction :
    Function.Injective (result.program.gateFunction interpretation)
  gateCount_le : gateCount ≤ g
  /-- Normalization does not increase any nonnegative operation cost. -/
  cost_le : ∀ operationCost : OperationCost σ,
    result.cost operationCost ≤ circuit.cost operationCost

export Cslib.Circuits (Circuit.Normalization)

/-- Normalize the program and rename the designated output wires. -/
noncomputable def _root_.Cslib.Circuits.Circuit.normalize
    [Fintype U]
    (circuit : Circuit σ n g m)
    (interpretation : Interpretation σ U) :
    Circuit.Normalization circuit interpretation := by
  classical
  let normalized := circuit.program.normalize interpretation
  let result : Circuit σ n normalized.gateCount m :=
    { program := normalized.result
      outputs := fun output =>
        normalized.wireMap (circuit.outputs output) }
  have outputEval (input : Fin n → U) (output : Fin m) :
      result.eval interpretation input output =
        circuit.eval interpretation input output := by
    exact normalized.trace_eq input (circuit.outputs output)
  exact
    { gateCount := normalized.gateCount
      result := result
      eval_eq := by
        funext input output
        exact outputEval input output
      injective_gateFunction := normalized.injective_gateFunction
      gateCount_le := normalized.gateCount_le
      cost_le := by
        intro operationCost
        exact normalized.cost_le operationCost }

/-! ## Irredundant function families -/

export Cslib.Circuits (Circuit.normalize)

export Cslib.Circuits (Circuit.Irredundant)

/-- Functions computed by irredundant circuits with exactly `g` internal gates. -/
noncomputable def _root_.Cslib.Circuits.Circuit.irredundantFunctions
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n g m : Nat) : Finset (Target U n m) := by
  classical
  exact
    (Finset.univ.filter fun circuit : Circuit σ n g m =>
      circuit.Irredundant interpretation).image fun circuit =>
        circuit.eval interpretation

export Cslib.Circuits (Circuit.irredundantFunctions)

theorem _root_.Cslib.Circuits.Circuit.mem_irredundantFunctions_iff
    [Fintype σ.Op] [Fintype U]
    {interpretation : Interpretation σ U}
    {target : Target U n m} :
    target ∈ Circuit.irredundantFunctions interpretation n g m ↔
      ∃ circuit : Circuit σ n g m,
        circuit.Irredundant interpretation ∧
          circuit.eval interpretation = target := by
  classical
  simp [Circuit.irredundantFunctions]

export Cslib.Circuits (Circuit.mem_irredundantFunctions_iff)

/-- Functions computed by irredundant circuits with at most `G` internal gates. -/
noncomputable def _root_.Cslib.Circuits.Circuit.irredundantFunctionsAtMost
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) : Finset (Target U n m) := by
  classical
  exact (Finset.range (G + 1)).biUnion fun g =>
    Circuit.irredundantFunctions interpretation n g m

export Cslib.Circuits (Circuit.irredundantFunctionsAtMost)

theorem _root_.Cslib.Circuits.Circuit.functionsAtMost_subset_irredundantFunctionsAtMost
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) :
    Circuit.functionsAtMost interpretation n m G ⊆
      Circuit.irredundantFunctionsAtMost interpretation n m G := by
  classical
  intro target present
  obtain ⟨g, bounded, circuit, computes⟩ :=
    Circuit.mem_functionsAtMost_iff.mp present
  obtain ⟨k, gateCountLe, normalized, evalEq, injective⟩ :=
    circuit.exists_irredundant interpretation
  rw [Circuit.irredundantFunctionsAtMost, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_of_le (gateCountLe.trans bounded)
  rw [Circuit.mem_irredundantFunctions_iff]
  refine ⟨normalized, injective, ?_⟩
  rw [evalEq]
  exact computes.eval_eq

export Cslib.Circuits (Circuit.functionsAtMost_subset_irredundantFunctionsAtMost)

theorem _root_.Cslib.Circuits.Circuit.card_functionsAtMost_le_sum_irredundant
    [Fintype σ.Op] [Fintype U]
    (interpretation : Interpretation σ U)
    (n m G : Nat) :
    (Circuit.functionsAtMost interpretation n m G).card ≤
      ∑ g ∈ Finset.range (G + 1),
        (Circuit.irredundantFunctions interpretation n g m).card := by
  classical
  exact
    (Finset.card_le_card
      (Circuit.functionsAtMost_subset_irredundantFunctionsAtMost
        interpretation n m G)).trans
      (by simpa [Circuit.irredundantFunctionsAtMost] using
        (Finset.card_biUnion_le
          (s := Finset.range (G + 1))
          (t := fun g => Circuit.irredundantFunctions interpretation n g m)))

export Cslib.Circuits (Circuit.card_functionsAtMost_le_sum_irredundant)

end Algebraic
