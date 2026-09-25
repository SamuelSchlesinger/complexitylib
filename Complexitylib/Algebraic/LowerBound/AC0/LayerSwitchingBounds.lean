/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerSwitching

/-!
# AC0 layer switching with separate source and target bounds

The first restriction in the standard parity lower-bound argument starts from
the width-one literal layer but aims for decision-tree depth `t`. Later rounds
start and end at depth `t`. This module therefore separates the incoming
normal-form width `sourceBound` from the desired outgoing decision-tree depth
`targetBound`.

For `sourceBound <= targetBound`, one logical layer advances except with
probability at most

`andOrCost(program) * (5 * p * sourceBound)^(targetBound + 1)`.

Keeping these parameters distinct is quantitatively essential: charging the
first round as though its source width were already `t` would introduce an
artificial extra factor of `t` and lose the standard depth exponent. The proof
uses the same exact semantic switching and finite union bounds as the
equal-bound theorem; it performs no circuit search or finite experiment.
-/

@[expose] public section

namespace Algebraic
namespace AC0
namespace Program

open scoped ENNReal

/-- Advance the shallow invariant when old layers have a possibly smaller
bound than the newly exposed layer. Arbitrary internal NOT gates are handled
by the raw one-bound successor theorem. -/
theorem ShallowUpTo.succ_of_connective_bounds_raw
    {program : Algebraic.Program signature n g}
    {rho extension : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (shallow : ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (next : ∀ gate,
      gate ∈ connectiveGates program →
      logicalGateDepths program gate ≤ level + 1 →
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) targetBound) :
    ShallowUpTo program (rho.refine extension) (level + 1) targetBound := by
  have widened : ShallowUpTo program rho level targetBound := by
    intro wire wireDepth
    exact (shallow wire wireDepth).mono sourceLeTarget
  exact widened.succ_of_connective_raw next

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem ShallowUpTo.succ_of_connective_bounds
    {program : Algebraic.Program signature n g}
    {rho extension : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (_normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (next : ∀ gate,
      gate ∈ connectiveGates program →
      logicalGateDepths program gate ≤ level + 1 →
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) targetBound) :
    ShallowUpTo program (rho.refine extension) (level + 1) targetBound :=
  shallow.succ_of_connective_bounds_raw sourceLeTarget next

/-- A gate represented by source-width normal form fails the target tree-depth
bound with the two-parameter switching-lemma estimate. -/
theorem ShallowUpTo.probability_gate_not_depthAtMost_refine_le_five_bounds
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (shallow : ShallowUpTo program rho level sourceBound)
    (gate : Fin g)
    (connective : gate ∈ connectiveGates program)
    (gateDepth : logicalGateDepths program gate ≤ level + 1)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬DecisionTree.DepthAtMost
            (ScalarFunction.restrict
              (program.gateFunction interpretation gate)
              (rho.refine extension)) targetBound) ≤
      (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
        (targetBound + 1)) := by
  have connectiveOperation :
      (program.lines gate).op.connective ≠ none :=
    (mem_connectiveGates program gate).1 connective
  cases operation : (program.lines gate).op with
  | not => simp [Op.connective, operation] at connectiveOperation
  | and fanIn =>
      obtain ⟨formula, bounded, computes⟩ :=
        shallow.exists_cnf_for_and_gate gate operation gateDepth
      calc
        RandomRestriction.probability n p atMostOne
            (fun extension =>
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) targetBound) =
            RandomRestriction.probability n p atMostOne
              (fun extension =>
                ¬DecisionTree.DepthAtMost
                  ((formula.restrict extension).eval) targetBound) := by
              congr 1
              funext extension
              rw [formula.restrict_eval_eq_refine_of_eval_eq
                (program.gateFunction interpretation gate) rho extension
                computes]
        _ ≤ (((5 : ENNReal) * (p : ENNReal) *
                (sourceBound : ENNReal)) ^ (targetBound + 1)) :=
          RandomRestriction.probability_cnf_not_depthAtMost_restrict_le_five
            formula bounded targetBound p atMostOne
  | or fanIn =>
      obtain ⟨formula, bounded, computes⟩ :=
        shallow.exists_dnf_for_or_gate gate operation gateDepth
      calc
        RandomRestriction.probability n p atMostOne
            (fun extension =>
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) targetBound) =
            RandomRestriction.probability n p atMostOne
              (fun extension =>
                ¬DecisionTree.DepthAtMost
                  ((formula.restrict extension).eval) targetBound) := by
              congr 1
              funext extension
              rw [formula.restrict_eval_eq_refine_of_eval_eq
                (program.gateFunction interpretation gate) rho extension
                computes]
        _ ≤ (((5 : ENNReal) * (p : ENNReal) *
                (sourceBound : ENNReal)) ^ (targetBound + 1)) :=
          RandomRestriction.probability_not_depthAtMost_restrict_le_five
            formula bounded targetBound p atMostOne

/-- The next-layer event for one charged gate satisfies the two-parameter
bound; gates outside that layer contribute the empty event. -/
theorem ShallowUpTo.probability_gate_in_nextLayer_not_depthAtMost_refine_le_five_bounds
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (shallow : ShallowUpTo program rho level sourceBound)
    (gate : Fin g)
    (connective : gate ∈ connectiveGates program)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          logicalGateDepths program gate ≤ level + 1 ∧
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate)
                (rho.refine extension)) targetBound) ≤
      (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
        (targetBound + 1)) := by
  by_cases gateDepth : logicalGateDepths program gate ≤ level + 1
  · calc
      RandomRestriction.probability n p atMostOne
          (fun extension =>
            logicalGateDepths program gate ≤ level + 1 ∧
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) targetBound) ≤
        RandomRestriction.probability n p atMostOne
          (fun extension =>
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate)
                (rho.refine extension)) targetBound) := by
          apply RandomRestriction.probability_mono n p atMostOne
          exact fun _ failure => failure.2
      _ ≤ (((5 : ENNReal) * (p : ENNReal) *
              (sourceBound : ENNReal)) ^ (targetBound + 1)) :=
        shallow.probability_gate_not_depthAtMost_refine_le_five_bounds
          gate connective gateDepth p atMostOne
  · simp [gateDepth]

/-- Union bound over the connective gates in the next layer, retaining
separate source-width and target-depth parameters. -/
theorem ShallowUpTo.probability_exists_connective_in_nextLayer_not_depthAtMost_refine_le_five_bounds
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (shallow : ShallowUpTo program rho level sourceBound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension => Exists fun gate : Fin g =>
          gate ∈ connectiveGates program ∧
            logicalGateDepths program gate ≤ level + 1 ∧
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) targetBound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
          (targetBound + 1)) := by
  let event (gate : Fin g) (extension : PartialAssignment n) : Prop :=
    logicalGateDepths program gate ≤ level + 1 ∧
      ¬DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) targetBound
  calc
    RandomRestriction.probability n p atMostOne
          (fun extension => Exists fun gate : Fin g =>
            gate ∈ connectiveGates program ∧ event gate extension) ≤
        ∑ gate ∈ connectiveGates program,
          RandomRestriction.probability n p atMostOne (event gate) := by
      simpa [event, and_assoc] using
        RandomRestriction.probability_exists_mem_le_sum n p atMostOne
          (connectiveGates program) event
    _ ≤ ∑ _gate ∈ connectiveGates program,
          (((5 : ENNReal) * (p : ENNReal) *
              (sourceBound : ENNReal)) ^ (targetBound + 1)) := by
      apply Finset.sum_le_sum
      intro gate connective
      exact shallow.probability_gate_in_nextLayer_not_depthAtMost_refine_le_five_bounds
        gate connective p atMostOne
    _ = (program.cost andOrCost : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
              (sourceBound : ENNReal)) ^ (targetBound + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_connectiveGates]

/-- One random restriction advances the semantic invariant from source bound
`sourceBound` to target bound `targetBound`, except with the standard charged
two-parameter switching probability. This raw form permits arbitrary internal
NOT gates. -/
theorem ShallowUpTo.probability_not_succ_refine_le_five_bounds_raw
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (shallow : ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬ShallowUpTo program (rho.refine extension)
            (level + 1) targetBound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
          (targetBound + 1)) := by
  calc
    RandomRestriction.probability n p atMostOne
          (fun extension =>
            ¬ShallowUpTo program (rho.refine extension)
              (level + 1) targetBound) ≤
        RandomRestriction.probability n p atMostOne
          (fun extension => Exists fun gate : Fin g =>
            gate ∈ connectiveGates program ∧
              logicalGateDepths program gate ≤ level + 1 ∧
                ¬DecisionTree.DepthAtMost
                  (ScalarFunction.restrict
                    (program.gateFunction interpretation gate)
                    (rho.refine extension)) targetBound) := by
      apply RandomRestriction.probability_mono n p atMostOne
      intro extension failure
      by_contra noGateFailure
      apply failure
      apply shallow.succ_of_connective_bounds_raw sourceLeTarget
      intro gate connective gateDepth
      by_contra gateFailure
      exact noGateFailure ⟨gate, connective, gateDepth, gateFailure⟩
    _ ≤ (program.cost andOrCost : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
              (sourceBound : ENNReal)) ^ (targetBound + 1)) :=
      shallow.probability_exists_connective_in_nextLayer_not_depthAtMost_refine_le_five_bounds
        p atMostOne

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem ShallowUpTo.probability_not_succ_refine_le_five_bounds
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level sourceBound targetBound : Nat}
    (_normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level sourceBound)
    (sourceLeTarget : sourceBound ≤ targetBound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬ShallowUpTo program (rho.refine extension)
            (level + 1) targetBound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (sourceBound : ENNReal)) ^
          (targetBound + 1)) :=
  shallow.probability_not_succ_refine_le_five_bounds_raw
    sourceLeTarget p atMostOne

end Program
end AC0
end Algebraic
