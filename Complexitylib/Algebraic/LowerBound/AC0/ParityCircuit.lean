/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerIteration
public import Complexitylib.Algebraic.LowerBound.AC0.Parity

/-!
# The iterated switching contradiction for parity circuits

This module connects iterated semantic depth reduction to exact parity
resilience at a designated circuit output. If a one-output circuit computes
parity, any `ShallowUpTo` witness covering that output forces the restriction
to leave at most the common decision-tree allowance many variables live.

Combining that fact with `exists_shallowUpTo_with_liveCount` gives the central
parameterized contradiction: a survivor schedule satisfying the explicit
switching inequalities rules out the circuit whenever its final value exceeds
the tree-depth allowance. Closed-form parameter selection is intentionally a
separate arithmetic layer.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Program

/-- A shallow invariant covering a parity-computing wire forces the live count
below the common tree-depth allowance. -/
theorem ShallowUpTo.parity_liveCount_le
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (wire : Wire n g)
    (wireDepth : logicalWireDepths program wire <= level)
    (computes :
      program.wireFunction interpretation wire = Parity.function n) :
    rho.liveCount <= bound := by
  have bounded := shallow wire wireDepth
  rw [computes] at bounded
  exact (Parity.depthAtMost_iff_liveCount_le rho bound).1 bounded

end Program

namespace Circuit

open scoped ENNReal

/-- Every designated output depth is at most the circuit's maximum logical
output depth. -/
theorem logicalOutputDepth_le_logicalDepth
    (circuit : Algebraic.Circuit signature n g m)
    (output : Fin m) :
    logicalOutputDepths circuit output <= logicalDepth circuit := by
  exact Fin.le_foldl_max (logicalOutputDepths circuit) 0 output

/-- A circuit logical-depth bound covers each designated output wire in the
underlying program. -/
theorem logicalWireDepth_output_le
    (circuit : Algebraic.Circuit signature n g m)
    (output : Fin m)
    (level : Nat)
    (depthBound : logicalDepth circuit <= level) :
    Program.logicalWireDepths circuit.program (circuit.outputs output) <=
      level := by
  exact (logicalOutputDepth_le_logicalDepth circuit output).trans depthBound

/-- Exact circuit computation of parity identifies the scalar function on its
unique designated output wire. -/
theorem wireFunction_output_eq_parity_of_computes
    {circuit : Algebraic.Circuit signature n g 1}
    (computes : circuit.ComputesWith interpretation (Parity.target n)) :
    circuit.program.wireFunction interpretation (circuit.outputs 0) =
      Parity.function n := by
  funext input
  exact congrFun (computes input) 0

/-- A shallow invariant covering a parity circuit's output leaves at most the
tree-depth allowance many variables live. -/
theorem liveCount_le_of_shallowUpTo_computes_parity
    {circuit : Algebraic.Circuit signature n g 1}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depthBound : logicalDepth circuit <= level)
    (shallow : Program.ShallowUpTo circuit.program rho level bound) :
    rho.liveCount <= bound := by
  exact shallow.parity_liveCount_le
    (circuit.outputs 0)
    (logicalWireDepth_output_le circuit 0 level depthBound)
    (wireFunction_output_eq_parity_of_computes computes)

/-- Any parity circuit satisfying the iterated switching premises forces the
final survivor schedule below the common tree-depth allowance, with arbitrary
internal NOT gates. -/
theorem retained_le_bound_of_iterated_parity_raw
    (circuit : Algebraic.Circuit signature n g 1)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth bound : Nat)
    (circuitDepth : logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    retained depth <= bound := by
  obtain ⟨rho, shallow, survivors⟩ :=
    Program.exists_shallowUpTo_with_liveCount_raw circuit.program
      depth bound oneLeBound p atMostOne retained initial failureLe room
  exact survivors.trans
    (liveCount_le_of_shallowUpTo_computes_parity
      computes circuitDepth shallow)

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem retained_le_bound_of_iterated_parity
    (circuit : Algebraic.Circuit signature n g 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depth bound : Nat)
    (circuitDepth : logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    retained depth <= bound :=
  retained_le_bound_of_iterated_parity_raw circuit computes depth bound
    circuitDepth oneLeBound p atMostOne retained initial failureLe room

/-- Parameterized iterated-switching lower bound: if the survivor schedule
ends above the tree allowance, the circuit cannot compute parity, even with
arbitrary internal NOT gates. -/
theorem not_computes_parity_of_iterated_switching_raw
    (circuit : Algebraic.Circuit signature n g 1)
    (depth bound : Nat)
    (circuitDepth : logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal))
    (tooMany : bound < retained depth) :
    Not (circuit.ComputesWith interpretation (Parity.target n)) := by
  intro computes
  exact (Nat.not_lt_of_ge
    (retained_le_bound_of_iterated_parity_raw
      circuit computes depth bound circuitDepth oneLeBound
      p atMostOne retained initial failureLe room)) tooMany

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem not_computes_parity_of_iterated_switching
    (circuit : Algebraic.Circuit signature n g 1)
    (_normal : Program.NegationsAtInputs circuit.program)
    (depth bound : Nat)
    (circuitDepth : logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal))
    (tooMany : bound < retained depth) :
    Not (circuit.ComputesWith interpretation (Parity.target n)) :=
  not_computes_parity_of_iterated_switching_raw circuit depth bound
    circuitDepth oneLeBound p atMostOne retained initial failureLe room
    tooMany

end Circuit
end AC0
end Algebraic
