/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.BottomGate
public import Complexitylib.Algebraic.LowerBound.AC0.TreeNormalForm
public import Mathlib.Data.Finset.Card

/-!
# Semantic AC0 layer invariants

The standard switching-lemma application advances a semantic invariant: after
a cumulative restriction, every wire through logical layer `i` is computed by
a decision tree of a common shallow depth. This module defines that invariant,
proves its restriction stability and its depth-zero literal base case, and
shows that every argument of a connective gate comes from a strictly earlier
logical layer.

It also identifies the finite set of AND/OR gates with the source-facing AC0
cost exactly. Later union bounds can therefore charge the mathematical circuit
size rather than the raw program gate count, which may include free input
negations.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Program

/-- The internal gates charged by the source AC0 size measure. -/
def connectiveGates
    (program : Algebraic.Program signature n g) : Finset (Fin g) :=
  Finset.univ.filter fun gate =>
    (program.lines gate).op.connective ≠ none

@[simp] theorem mem_connectiveGates
    (program : Algebraic.Program signature n g)
    (gate : Fin g) :
    gate ∈ connectiveGates program ↔
      (program.lines gate).op.connective ≠ none := by
  simp [connectiveGates]

/-- AC0 operation cost is the indicator of being an AND or OR gate. -/
theorem andOrCost_eq_indicator (operation : Op) :
    andOrCost operation =
      if operation.connective ≠ none then 1 else 0 := by
  cases operation <;> simp [andOrCost, Op.connective]

/-- The charged AC0 cost is exactly the number of connective gates. -/
theorem card_connectiveGates
    (program : Algebraic.Program signature n g) :
    (connectiveGates program).card = program.cost andOrCost := by
  rw [program.cost_eq_sum_lines]
  simp only [connectiveGates, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro gate _
  rw [andOrCost_eq_indicator]

end Program

namespace Literal

/-- The one-query decision tree computing a literal. -/
def decisionTree (literal : Literal n) : DecisionTree n :=
  .query literal.index (.leaf (!literal.value)) (.leaf literal.value)

/-- The literal tree has exactly the expected Boolean semantics. -/
@[simp] theorem decisionTree_eval
    (literal : Literal n)
    (input : Fin n -> Bool) :
    literal.decisionTree.eval input = literal.eval input := by
  cases literal with
  | mk index value =>
      cases value <;> cases inputValue : input index <;>
        simp [decisionTree, DecisionTree.eval, eval, inputValue]

/-- A literal decision tree has depth one. -/
@[simp] theorem decisionTree_depth (literal : Literal n) :
    literal.decisionTree.depth = 1 := by
  simp [decisionTree, DecisionTree.depth]

/-- Every literal function has semantic decision-tree depth at most one. -/
theorem depthAtMost_eval (literal : Literal n) :
    DecisionTree.DepthAtMost literal.eval 1 :=
  ⟨literal.decisionTree, literal.decisionTree_eval,
    by simp⟩

end Literal

namespace Program

/-- After `rho`, every wire up through `level` has a decision tree of depth at
most `bound`. This is the semantic induction invariant used in the standard
switching-lemma application. -/
def ShallowUpTo
    (program : Algebraic.Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat) : Prop :=
  forall wire : Wire n g,
    logicalWireDepths program wire ≤ level ->
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.wireFunction interpretation wire) rho)
        bound

/-- Further restricting inputs preserves a semantic layer-depth bound. -/
theorem ShallowUpTo.restrict
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (extension : PartialAssignment n) :
    ShallowUpTo program (rho.refine extension) level bound := by
  intro wire depthBound
  have restricted := (shallow wire depthBound).restrict extension
  simpa only [ScalarFunction.restrict_refine] using restricted

/-- Original inputs and arbitrary chains of NOT gates establish the
depth-zero base of the semantic layer invariant. -/
theorem shallowUpTo_zero_raw
    (program : Algebraic.Program signature n g)
    (rho : PartialAssignment n) :
    ShallowUpTo program rho 0 1 := by
  intro wire depthBound
  have depthZero : logicalWireDepths program wire = 0 :=
    Nat.eq_zero_of_le_zero depthBound
  obtain ⟨literal, computes⟩ :=
    exists_literal_of_logicalWireDepth_zero_raw program wire depthZero
  rw [computes]
  exact literal.depthAtMost_eval.restrict rho

/-- Original inputs and checked input negations establish the depth-zero base
of the semantic layer invariant. -/
theorem shallowUpTo_zero
    (program : Algebraic.Program signature n g)
    (_normal : NegationsAtInputs program)
    (rho : PartialAssignment n) :
    ShallowUpTo program rho 0 1 :=
  shallowUpTo_zero_raw program rho

/-- Each argument of an AND or OR gate has strictly smaller source logical
depth than the gate itself. -/
theorem argument_logicalWireDepth_lt_gateDepth
    (program : Algebraic.Program signature n g)
    (gate : Fin g)
    (connective : (program.lines gate).op.connective ≠ none)
    (argument : Fin (arity (program.lines gate).op)) :
    logicalWireDepths program ((program.lines gate).wires argument) <
      logicalGateDepths program gate := by
  have lineDepth := lines_logicalDepth program gate
  generalize lineEqual : program.lines gate = line at lineDepth connective argument ⊢
  cases line with
  | mk operation wires =>
      cases operation with
      | not => simp [Op.connective] at connective
      | and argumentCount =>
          change Nat.succ
              (Fin.foldl argumentCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0) =
            logicalGateDepths program gate at lineDepth
          rw [← lineDepth]
          change
            (Wire.elim (fun _ : Fin n => 0)
              (logicalGateDepths program))
                (wires argument) <
              Nat.succ
                (Fin.foldl argumentCount
                  (fun depth current => max depth
                    ((Wire.elim (fun _ : Fin n => 0)
                      (logicalGateDepths program))
                      (wires current))) 0)
          exact Nat.lt_succ_of_le
            (Fin.le_foldl_max
              (fun current =>
                (Wire.elim (fun _ : Fin n => 0)
                  (logicalGateDepths program))
                  (wires current)) 0 argument)
      | or argumentCount =>
          change Nat.succ
              (Fin.foldl argumentCount
                (fun depth current => max depth
                  ((Wire.elim (fun _ : Fin n => 0)
                    (logicalGateDepths program))
                    (wires current))) 0) =
            logicalGateDepths program gate at lineDepth
          rw [← lineDepth]
          change
            (Wire.elim (fun _ : Fin n => 0)
              (logicalGateDepths program))
                (wires argument) <
              Nat.succ
                (Fin.foldl argumentCount
                  (fun depth current => max depth
                    ((Wire.elim (fun _ : Fin n => 0)
                      (logicalGateDepths program))
                      (wires current))) 0)
          exact Nat.lt_succ_of_le
            (Fin.le_foldl_max
              (fun current =>
                (Wire.elim (fun _ : Fin n => 0)
                  (logicalGateDepths program))
                  (wires current)) 0 argument)

/-- If a connective gate is in the next logical layer, each argument lies in
the current layer or below. -/
theorem argument_logicalWireDepth_le_of_gateDepth_le_succ
    (program : Algebraic.Program signature n g)
    (gate : Fin g)
    (level : Nat)
    (connective : (program.lines gate).op.connective ≠ none)
    (gateDepth : logicalGateDepths program gate ≤ level + 1)
    (argument : Fin (arity (program.lines gate).op)) :
    logicalWireDepths program ((program.lines gate).wires argument) ≤
      level := by
  have strict := argument_logicalWireDepth_lt_gateDepth
    program gate connective argument
  omega

/-- A layer invariant supplies a shallow tree for every argument of a
connective gate in the next layer. -/
theorem ShallowUpTo.argument
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    (connective : (program.lines gate).op.connective ≠ none)
    (gateDepth : logicalGateDepths program gate ≤ level + 1)
    (argument : Fin (arity (program.lines gate).op)) :
    DecisionTree.DepthAtMost
      (ScalarFunction.restrict
        (program.wireFunction interpretation
          ((program.lines gate).wires argument)) rho)
      bound :=
  shallow _ (argument_logicalWireDepth_le_of_gateDepth_le_succ
    program gate level connective gateDepth argument)

/-- The invariant specializes to any internal gate in the covered layers. -/
theorem ShallowUpTo.gate
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    (gateDepth : logicalGateDepths program gate ≤ level) :
    DecisionTree.DepthAtMost
      (ScalarFunction.restrict
        (program.gateFunction interpretation gate) rho)
      bound := by
  simpa using shallow (Wire.gate gate) (by simpa using gateDepth)

end Program

end AC0
end Algebraic
