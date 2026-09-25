/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Substitution
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Input reindexing and parallel circuits

This file provides the structural circuit operations used by simultaneous
evaluation arguments. `Circuit.mapInputs` rewires the original inputs without
adding gates, `Circuit.mapOutputs` selects or repeats designated outputs, and
`Circuit.parallel` places two circuits with the same input namespace side by
side. Parallel composition preserves sharing within each operand and has
exactly additive cost.
-/

@[expose] public section

namespace Algebraic

open scoped BigOperators

/-- Transport a circuit along equalities of its input and output counts. This
is a structural cast; it changes no gate or wire. -/
def _root_.Cslib.Circuits.Circuit.castCounts
    {n m n' m' : Nat}
    (inputCount : n = n')
    (outputCount : m = m')
    (circuit : Circuit σ n m) : Circuit σ n' m' := by
  subst n'
  subst m'
  exact circuit

export Cslib.Circuits (Circuit.castCounts)

/-- Casting circuit counts transports inputs and outputs by the corresponding
finite-index equalities and otherwise preserves evaluation. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_castCounts
    {n m n' m' : Nat}
    (inputCount : n = n')
    (outputCount : m = m')
    (circuit : Circuit σ n m)
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (circuit.castCounts inputCount outputCount).eval
        interpretation input =
      fun output =>
        circuit.eval interpretation
          (input ∘ Fin.cast inputCount) (Fin.cast outputCount.symm output) := by
  subst n'
  subst m'
  rfl

export Cslib.Circuits (Circuit.eval_castCounts)

/-- Casting circuit counts preserves weighted cost. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_castCounts
    {n m n' m' : Nat}
    (inputCount : n = n')
    (outputCount : m = m')
    (circuit : Circuit σ n m)
    (operationCost : OperationCost σ) :
    (circuit.castCounts inputCount outputCount).cost operationCost =
      circuit.cost operationCost := by
  subst n'
  subst m'
  rfl

export Cslib.Circuits (Circuit.cost_castCounts)

/-- Casting circuit counts preserves the gate count exactly. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_castCounts
    {n m n' m' : Nat}
    (inputCount : n = n')
    (outputCount : m = m')
    (circuit : Circuit σ n m) :
    (circuit.castCounts inputCount outputCount).size =
      circuit.size := by
  subst n'
  subst m'
  rfl

export Cslib.Circuits (Circuit.size_castCounts)

/-- Reindex the original inputs of a wire while leaving its gate index
unchanged. -/
def _root_.Cslib.Circuits.Wire.mapInputs
    (inputMap : Fin n -> Fin n') : Wire n g -> Wire n' g :=
  Wire.elim (Wire.input ∘ inputMap) Wire.gate

export Cslib.Circuits (Wire.mapInputs)

@[simp] theorem _root_.Cslib.Circuits.Wire.mapInputs_input
    (inputMap : Fin n -> Fin n')
    (input : Fin n) :
    Wire.mapInputs (g := g) inputMap (Wire.input input) =
      Wire.input (inputMap input) := rfl

export Cslib.Circuits (Wire.mapInputs_input)

@[simp] theorem _root_.Cslib.Circuits.Wire.mapInputs_gate
    (inputMap : Fin n -> Fin n')
    (gate : Fin g) :
    Wire.mapInputs inputMap (Wire.gate gate) =
      (Wire.gate gate : Wire n' g) := rfl

export Cslib.Circuits (Wire.mapInputs_gate)

/-- Reindex every original input of a program without changing its gates. -/
def _root_.Cslib.Circuits.Program.mapInputs
    (inputMap : Fin n -> Fin n') :
    Program σ n g -> Program σ n' g
  | .empty => .empty
  | .gate program line =>
      .gate (program.mapInputs inputMap)
        (line.mapWires (Wire.mapInputs inputMap))

export Cslib.Circuits (Program.mapInputs)

/-- Input reindexing evaluates a program after precomposing its input. -/
theorem _root_.Cslib.Circuits.Program.eval_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (program.mapInputs inputMap).eval interpretation input =
      program.eval interpretation (input ∘ inputMap) := by
  induction program with
  | empty =>
      funext gate
      exact Fin.elim0 gate
  | @gate g program line ih =>
      funext gate
      refine Fin.lastCases ?_ (fun priorGate => ?_) gate
      · simp only [Program.mapInputs, Program.eval_gate_last]
        apply Line.eval_mapWires
        intro wire
        cases wire with
        | input sourceInput => rfl
        | gate sourceGate => simpa using congrFun ih sourceGate
      · simp only [Program.mapInputs, Program.eval_gate_castSucc]
        exact congrFun ih priorGate

export Cslib.Circuits (Program.eval_mapInputs)

/-- Input reindexing preserves the value of every mapped wire. -/
theorem _root_.Cslib.Circuits.Program.trace_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U)
    (wire : Wire n g) :
    (program.mapInputs inputMap).trace interpretation input
        (Wire.mapInputs inputMap wire) =
      program.trace interpretation (input ∘ inputMap) wire := by
  cases wire with
  | input sourceInput => rfl
  | gate sourceGate => simp [Program.trace, Program.eval_mapInputs]

export Cslib.Circuits (Program.trace_mapInputs)

/-- Input reindexing leaves every gate label, and hence every weighted cost,
unchanged. -/
@[simp] theorem _root_.Cslib.Circuits.Program.cost_mapInputs
    (program : Program σ n g)
    (inputMap : Fin n -> Fin n')
    (operationCost : OperationCost σ) :
    (program.mapInputs inputMap).cost operationCost =
      program.cost operationCost := by
  induction program with
  | empty => rfl
  | gate program line ih =>
      simp [Program.mapInputs, Program.cost, ih]

export Cslib.Circuits (Program.cost_mapInputs)

/-- Rewire the original inputs of a circuit without adding gates. The map may
identify, duplicate, permute, or discard inputs. -/
def _root_.Cslib.Circuits.Circuit.mapInputs
    (circuit : Circuit σ n m)
    (inputMap : Fin n -> Fin n') : Circuit σ n' m where
  program := circuit.program.mapInputs inputMap
  outputs := Wire.mapInputs inputMap ∘ circuit.outputs

export Cslib.Circuits (Circuit.mapInputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_mapInputs
    (circuit : Circuit σ n m)
    (inputMap : Fin n -> Fin n')
    (interpretation : Interpretation σ U)
    (input : Fin n' -> U) :
    (circuit.mapInputs inputMap).eval interpretation input =
      circuit.eval interpretation (input ∘ inputMap) := by
  funext output
  exact circuit.program.trace_mapInputs inputMap interpretation input
    (circuit.outputs output)

export Cslib.Circuits (Circuit.eval_mapInputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_mapInputs
    (circuit : Circuit σ n m)
    (inputMap : Fin n -> Fin n')
    (operationCost : OperationCost σ) :
    (circuit.mapInputs inputMap).cost operationCost =
      circuit.cost operationCost := by
  exact circuit.program.cost_mapInputs inputMap operationCost

export Cslib.Circuits (Circuit.cost_mapInputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.size_mapInputs
    (circuit : Circuit σ n m)
    (inputMap : Fin n -> Fin n') :
    (circuit.mapInputs inputMap).size = circuit.size := rfl

export Cslib.Circuits (Circuit.size_mapInputs)

/-- Select, reorder, or repeat the designated outputs of a circuit without
changing its gates. -/
def _root_.Cslib.Circuits.Circuit.mapOutputs
    (circuit : Circuit σ n m)
    (outputMap : Fin m' -> Fin m) : Circuit σ n m' where
  program := circuit.program
  outputs := circuit.outputs ∘ outputMap

export Cslib.Circuits (Circuit.mapOutputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_mapOutputs
    (circuit : Circuit σ n m)
    (outputMap : Fin m' -> Fin m)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (circuit.mapOutputs outputMap).eval interpretation input =
      circuit.eval interpretation input ∘ outputMap := rfl

export Cslib.Circuits (Circuit.eval_mapOutputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_mapOutputs
    (circuit : Circuit σ n m)
    (outputMap : Fin m' -> Fin m)
    (operationCost : OperationCost σ) :
    (circuit.mapOutputs outputMap).cost operationCost =
      circuit.cost operationCost := rfl

export Cslib.Circuits (Circuit.cost_mapOutputs)

@[simp] theorem _root_.Cslib.Circuits.Circuit.size_mapOutputs
    (circuit : Circuit σ n m)
    (outputMap : Fin m' -> Fin m) :
    (circuit.mapOutputs outputMap).size = circuit.size := rfl

export Cslib.Circuits (Circuit.size_mapOutputs)

/-- Place two circuits with the same original inputs side by side and
concatenate their designated outputs. -/
def _root_.Cslib.Circuits.Circuit.parallel
    (left : Circuit σ n m)
    (right : Circuit σ n k) : Circuit σ n (m + k) where
  program := right.program.instantiate left.program Wire.input
  outputs := Fin.addCases
    (fun output => Wire.Renaming.castAdd right.size (left.outputs output))
    (fun output =>
      Wire.Substitution.append (fun input => Wire.input input) right.size
        (right.outputs output))

export Cslib.Circuits (Circuit.parallel)

/-- Parallel composition concatenates the two output vectors. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_parallel
    (left : Circuit σ n m)
    (right : Circuit σ n k)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U) :
    (left.parallel right).eval interpretation input =
      Fin.append (left.eval interpretation input)
        (right.eval interpretation input) := by
  funext output
  refine Fin.addCases (fun leftOutput => ?_) (fun rightOutput => ?_) output
  · simp only [Fin.append_left, Circuit.eval, Circuit.parallel,
      Function.comp_apply, Fin.addCases_left]
    exact right.program.instantiate_trace_ambient left.program Wire.input
      interpretation input (left.outputs leftOutput)
  · simp only [Fin.append_right, Circuit.eval, Circuit.parallel,
      Function.comp_apply, Fin.addCases_right]
    change
      (right.program.instantiate left.program Wire.input).trace
          interpretation input
          (Wire.Substitution.append Wire.input right.size
            (right.outputs rightOutput)) =
        right.program.trace interpretation input (right.outputs rightOutput)
    rw [right.program.instantiate_trace left.program Wire.input
      interpretation input (right.outputs rightOutput)]
    have mappedInputs :
        left.program.trace interpretation input ∘
            (fun sourceInput : Fin n => Wire.input sourceInput) = input := by
      funext sourceInput
      simp [Function.comp_apply]
    rw [mappedInputs]

export Cslib.Circuits (Circuit.eval_parallel)

/-- Parallel composition has exactly additive weighted cost. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_parallel
    (left : Circuit σ n m)
    (right : Circuit σ n k)
    (operationCost : OperationCost σ) :
    (left.parallel right).cost operationCost =
      left.cost operationCost + right.cost operationCost := by
  exact right.program.cost_instantiate left.program Wire.input operationCost

export Cslib.Circuits (Circuit.cost_parallel)

/-- Parallel composition has exactly additive gate count. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_parallel
    (left : Circuit σ n m)
    (right : Circuit σ n k) :
    (left.parallel right).size = left.size + right.size := rfl

export Cslib.Circuits (Circuit.size_parallel)

/-- Put two equally wide output vectors into the row-major two-block layout
`Fin (2 * width)`. -/
def _root_.Cslib.Circuits.Circuit.parallelPair
    (left : Circuit σ n width)
    (right : Circuit σ n width) :
    Circuit σ n (2 * width) :=
  (left.parallel right).mapOutputs (Fin.cast (Nat.two_mul width))

export Cslib.Circuits (Circuit.parallelPair)

/-- The row-major pair has exactly additive gate count. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_parallelPair
    (left : Circuit σ n width)
    (right : Circuit σ n width) :
    (left.parallelPair right).size = left.size + right.size := rfl

export Cslib.Circuits (Circuit.size_parallelPair)

/-- Evaluation of `parallelPair` selects the indicated row-major block. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_parallelPair_apply
    (left : Circuit σ n width)
    (right : Circuit σ n width)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (side : Fin 2)
    (coordinate : Fin width) :
    (left.parallelPair right).eval interpretation input
        (finProdFinEquiv (side, coordinate)) =
      Fin.cases (left.eval interpretation input coordinate)
        (fun _ => right.eval interpretation input coordinate) side := by
  rw [Circuit.parallelPair, Circuit.eval_mapOutputs,
    Function.comp_apply, Circuit.eval_parallel]
  refine Fin.cases ?_ (fun finalSide => ?_) side
  · rw [show Fin.cast (Nat.two_mul width)
          (finProdFinEquiv ((0 : Fin 2), coordinate)) =
        Fin.castAdd width coordinate by
      apply Fin.ext
      simp [finProdFinEquiv]]
    rw [Fin.append_left]
    rfl
  · have finalSideZero : finalSide = 0 := Subsingleton.elim _ _
    subst finalSide
    rw [show Fin.cast (Nat.two_mul width)
          (finProdFinEquiv ((Fin.succ 0 : Fin 2), coordinate)) =
        Fin.natAdd width coordinate by
      apply Fin.ext
      simp [finProdFinEquiv]]
    rw [Fin.append_right]
    rfl

export Cslib.Circuits (Circuit.eval_parallelPair_apply)

@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_parallelPair
    (left : Circuit σ n width)
    (right : Circuit σ n width)
    (operationCost : OperationCost σ) :
    (left.parallelPair right).cost operationCost =
      left.cost operationCost + right.cost operationCost := by
  simp [Circuit.parallelPair]

export Cslib.Circuits (Circuit.cost_parallelPair)

/-- Place a finite family of scalar circuits with a common input namespace
side by side. Each member may have a different gate count; the resulting gate
count is their finite sum (`Circuit.size_parallelFin`). -/
def _root_.Cslib.Circuits.Circuit.parallelFin :
    (outputs : Nat) ->
    ((output : Fin outputs) -> Circuit σ n 1) ->
      Circuit σ n outputs
  | 0, _ => (Circuit.id σ n).mapOutputs Fin.elim0
  | outputs + 1, circuits =>
      let prefixCircuits : (output : Fin outputs) -> Circuit σ n 1 :=
        fun output => circuits output.castSucc
      let prefixCircuit :=
        Cslib.Circuits.Circuit.parallelFin outputs prefixCircuits
      let suffix := circuits (Fin.last outputs)
      prefixCircuit.parallel suffix

export Cslib.Circuits (Circuit.parallelFin)

/-- The gate count of a finite parallel family is the sum of its members'
gate counts. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_parallelFin
    (outputs : Nat)
    (circuits : (output : Fin outputs) -> Circuit σ n 1) :
    (Circuit.parallelFin outputs circuits).size =
      ∑ output, (circuits output).size := by
  induction outputs with
  | zero => rfl
  | succ outputs inductionHypothesis =>
      rw [Fin.sum_univ_castSucc, ← inductionHypothesis]
      rfl

export Cslib.Circuits (Circuit.size_parallelFin)

/-- `parallelFin` returns, at each output coordinate, the corresponding
member circuit's scalar value. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_parallelFin
    (outputs : Nat)
    (circuits : (output : Fin outputs) -> Circuit σ n 1)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (output : Fin outputs) :
    (Circuit.parallelFin outputs circuits).eval
        interpretation input output =
      (circuits output).eval interpretation input 0 := by
  induction outputs with
  | zero => exact Fin.elim0 output
  | succ outputs inductionHypothesis =>
      refine Fin.lastCases ?_ (fun prefixOutput => ?_) output
      · simp only [Circuit.parallelFin, Circuit.eval_parallel]
        rw [show Fin.last outputs = Fin.natAdd outputs (0 : Fin 1) by
          apply Fin.ext
          simp]
        rw [Fin.append_right]
      · simp only [Circuit.parallelFin, Circuit.eval_parallel]
        rw [show prefixOutput.castSucc = Fin.castAdd 1 prefixOutput by rfl]
        rw [Fin.append_left]
        exact inductionHypothesis
          (fun selected : Fin outputs => circuits selected.castSucc)
          prefixOutput

export Cslib.Circuits (Circuit.eval_parallelFin)

/-- Exact weighted cost of a finite parallel family. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_parallelFin
    (outputs : Nat)
    (circuits : (output : Fin outputs) -> Circuit σ n 1)
    (operationCost : OperationCost σ) :
    (Circuit.parallelFin outputs circuits).cost operationCost =
      ∑ output, (circuits output).cost operationCost := by
  induction outputs with
  | zero =>
      simp only [Circuit.parallelFin]
      rfl
  | succ outputs inductionHypothesis =>
      simp only [Circuit.parallelFin, Circuit.cost_parallel]
      rw [inductionHypothesis]
      exact (Fin.sum_univ_castSucc
        (fun output => (circuits output).cost operationCost)).symm

export Cslib.Circuits (Circuit.cost_parallelFin)

/-- Place a finite family of equally wide vector circuits side by side in
row-major `(member, coordinate)` order. The resulting gate count is the sum of
the members' gate counts (`Circuit.size_parallelFinVector`). -/
def _root_.Cslib.Circuits.Circuit.parallelFinVector :
    (members width : Nat) ->
    ((member : Fin members) -> Circuit σ n width) ->
      Circuit σ n (members * width)
  | 0, width, _ =>
      (Circuit.id σ n).mapOutputs fun output =>
        Fin.elim0 (Fin.cast (Nat.zero_mul width) output)
  | members + 1, width, circuits =>
      let prefixCircuits : (member : Fin members) -> Circuit σ n width :=
        fun member => circuits member.castSucc
      let prefixCircuit :=
        Cslib.Circuits.Circuit.parallelFinVector members width prefixCircuits
      let suffix := circuits (Fin.last members)
      (prefixCircuit.parallel suffix).castCounts rfl (Nat.succ_mul members width).symm

export Cslib.Circuits (Circuit.parallelFinVector)

/-- The gate count of a finite parallel vector family is the sum of its
members' gate counts. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.size_parallelFinVector
    (members width : Nat)
    (circuits : (member : Fin members) -> Circuit σ n width) :
    (Circuit.parallelFinVector members width circuits).size =
      ∑ member, (circuits member).size := by
  induction members with
  | zero => rfl
  | succ members inductionHypothesis =>
      simp only [Circuit.parallelFinVector, Circuit.size_castCounts,
        Circuit.size_parallel]
      rw [inductionHypothesis, Fin.sum_univ_castSucc]

export Cslib.Circuits (Circuit.size_parallelFinVector)

/-- `parallelFinVector` evaluates the indicated member and coordinate. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.eval_parallelFinVector
    (members width : Nat)
    (circuits : (member : Fin members) -> Circuit σ n width)
    (interpretation : Interpretation σ U)
    (input : Fin n -> U)
    (member : Fin members)
    (coordinate : Fin width) :
    (Circuit.parallelFinVector members width circuits).eval
        interpretation input (finProdFinEquiv (member, coordinate)) =
      (circuits member).eval interpretation input coordinate := by
  induction members with
  | zero => exact Fin.elim0 member
  | succ members inductionHypothesis =>
      refine Fin.lastCases ?_ (fun prefixMember => ?_) member
      · simp only [Circuit.parallelFinVector, Circuit.eval_castCounts,
          Fin.cast_refl, Function.comp_id, Circuit.eval_parallel]
        rw [show Fin.cast (Nat.succ_mul members width)
              (finProdFinEquiv (Fin.last members, coordinate)) =
            Fin.natAdd (members * width) coordinate by
          apply Fin.ext
          simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]]
        rw [Fin.append_right]
      · simp only [Circuit.parallelFinVector, Circuit.eval_castCounts,
          Fin.cast_refl, Function.comp_id, Circuit.eval_parallel]
        rw [show Fin.cast (Nat.succ_mul members width)
              (finProdFinEquiv (prefixMember.castSucc, coordinate)) =
            Fin.castAdd width (finProdFinEquiv
              (prefixMember, coordinate)) by
          apply Fin.ext
          simp [finProdFinEquiv]]
        rw [Fin.append_left]
        exact inductionHypothesis
          (fun selected : Fin members => circuits selected.castSucc)
          prefixMember

export Cslib.Circuits (Circuit.eval_parallelFinVector)

/-- Exact weighted cost of a finite parallel vector family. -/
@[simp] theorem _root_.Cslib.Circuits.Circuit.cost_parallelFinVector
    (members width : Nat)
    (circuits : (member : Fin members) -> Circuit σ n width)
    (operationCost : OperationCost σ) :
    (Circuit.parallelFinVector members width circuits).cost
        operationCost =
      ∑ member, (circuits member).cost operationCost := by
  induction members with
  | zero =>
      simp only [Circuit.parallelFinVector]
      rfl
  | succ members inductionHypothesis =>
      simp only [Circuit.parallelFinVector, Circuit.cost_castCounts,
        Circuit.cost_parallel]
      rw [inductionHypothesis]
      exact (Fin.sum_univ_castSucc
        (fun member => (circuits member).cost operationCost)).symm

export Cslib.Circuits (Circuit.cost_parallelFinVector)

end Algebraic
