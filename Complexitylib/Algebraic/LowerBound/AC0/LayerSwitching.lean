/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.LayerFormula
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Family

/-!
# One-step probabilistic AC0 layer advancement

This module packages the standard circuit-level application of the switching
lemma. If every wire through logical layer `i` has decision-tree depth at most
`t` after a base restriction `rho`, then a fresh independent `p`-restriction
advances the same invariant through layer `i + 1`, except with probability at
most

`andOrCost(program) * (5 * p * t)^(t + 1)`.

The proof composes exact bounded DNFs through OR gates and exact bounded CNFs
through AND gates, applies the single-formula switching lemma at each charged
gate, and takes an ordinary finite union bound over exactly the AND/OR gates.
Input negations contribute neither probability loss nor source size. All
events are semantic decision-tree predicates. Their decidability is classical
and noncomputable solely so the exact finite probability can be formed; no
tree optimizer, circuit search, or finite lower-bound experiment is defined.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Op

/-- The only AC0 operation that is not a connective is NOT. -/
theorem eq_not_of_connective_eq_none
    {operation : Op}
    (notConnective : operation.connective = none) :
    operation = .not := by
  cases operation <;> simp [connective] at notConnective ⊢

end Op

namespace Program

/-- Proof-level decidability of the semantic layer invariant. This instance is
used only to form exact finite restriction events; it does not search for
decision trees. -/
noncomputable instance shallowUpToDecidable
    (program : Algebraic.Program signature n g)
    (rho : PartialAssignment n)
    (level bound : Nat) :
    Decidable (ShallowUpTo program rho level bound) := by
  classical
  exact Classical.propDecidable _

/-- Under checked input-negation normal form, a NOT gate has logical depth
zero. -/
theorem logicalGateDepth_eq_zero_of_op_eq_not
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    (operation : (program.lines gate).op = .not) :
    logicalGateDepths program gate = 0 := by
  have lineNormal := normal.line gate
  have lineDepth := lines_logicalDepth program gate
  generalize lineEqual : program.lines gate = line at operation lineNormal lineDepth
  cases line with
  | mk actualOperation wires =>
      cases actualOperation with
      | not =>
          obtain ⟨input, source⟩ := lineNormal
          rw [← lineDepth]
          simp [Algebraic.Line.eval, logicalDepthInterpretation, source]
      | and fanIn => contradiction
      | or fanIn => contradiction

/-- Under checked input-negation normal form, every non-connective gate has
logical depth zero. -/
theorem logicalGateDepth_eq_zero_of_not_connective
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (gate : Fin g)
    (notConnective : (program.lines gate).op.connective = none) :
    logicalGateDepths program gate = 0 :=
  logicalGateDepth_eq_zero_of_op_eq_not program normal gate
    (Op.eq_not_of_connective_eq_none notConnective)

/-- If every charged gate in the next layer is shallow after an extension,
then the semantic shallow-layer invariant advances by one. Arbitrary internal
NOT chains are handled directly by topological induction and negating the
tree for their source wire. -/
theorem ShallowUpTo.succ_of_connective_raw
    {program : Algebraic.Program signature n g}
    {rho extension : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (next : forall gate,
      gate ∈ connectiveGates program ->
      logicalGateDepths program gate ≤ level + 1 ->
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) bound) :
    ShallowUpTo program (rho.refine extension) (level + 1) bound := by
  induction program generalizing rho extension level bound with
  | empty =>
      intro wire _
      cases wire with
      | input input =>
          apply shallow.restrict extension (Wire.input input)
          rw [logicalWireDepths_input]
          exact Nat.zero_le level
      | gate gate => exact Fin.elim0 gate
  | @gate gateCount prior line inductionHypothesis =>
      have priorShallow : ShallowUpTo prior rho level bound := by
        intro wire wireDepth
        have widenedDepth :
            logicalWireDepths (prior.gate line) wire.castSucc ≤ level := by
          simpa [logicalWireDepths] using wireDepth
        have widened := shallow wire.castSucc widenedDepth
        have functionEq :
            (prior.gate line).wireFunction interpretation wire.castSucc =
              prior.wireFunction interpretation wire := by
          funext input
          exact Algebraic.Program.trace_gate_castSucc
            prior line interpretation input wire
        rw [functionEq] at widened
        exact widened
      have priorNext : forall gate,
          gate ∈ connectiveGates prior ->
          logicalGateDepths prior gate ≤ level + 1 ->
          DecisionTree.DepthAtMost
            (ScalarFunction.restrict
              (prior.gateFunction interpretation gate)
              (rho.refine extension)) bound := by
        intro gate connective gateDepth
        have widenedConnective :
            gate.castSucc ∈ connectiveGates (prior.gate line) := by
          rw [mem_connectiveGates, Algebraic.Program.lines_gate_castSucc]
          simpa using (mem_connectiveGates prior gate).1 connective
        have widenedDepth :
            logicalGateDepths (prior.gate line) gate.castSucc ≤ level + 1 := by
          simpa [logicalGateDepths] using gateDepth
        have widened := next gate.castSucc widenedConnective widenedDepth
        simpa [Algebraic.Program.gateFunction] using widened
      have priorResult :
          ShallowUpTo prior (rho.refine extension) (level + 1) bound :=
        inductionHypothesis priorShallow priorNext
      intro wire wireDepth
      revert wireDepth
      cases wire with
      | input input => exact fun _ => shallow.restrict extension (Wire.input input) (by simp)
      | gate gate =>
        intro wireDepth
        rw [logicalWireDepths_gate] at wireDepth
        rw [Algebraic.Program.wireFunction_gate]
        revert wireDepth
        refine Fin.lastCases (fun wireDepth => ?_)
          (fun priorGate wireDepth => ?_) gate
        · have gateDepth :
              logicalGateDepths (prior.gate line) (Fin.last gateCount) ≤
                level + 1 := by
            exact wireDepth
          cases line with
          | mk operation wires =>
              cases operation with
              | not =>
                  have sourceDepth :
                      logicalWireDepths prior (wires 0) ≤ level + 1 := by
                    unfold logicalGateDepths at gateDepth
                    rw [Algebraic.Program.eval_gate_last] at gateDepth
                    simpa [Algebraic.Line.eval, logicalDepthInterpretation,
                      logicalWireDepths, Algebraic.Program.trace] using gateDepth
                  have sourceBounded := priorResult (wires 0) sourceDepth
                  have gateFunctionEq :
                      ScalarFunction.restrict
                          ((prior.gate ⟨.not, wires⟩).gateFunction
                            interpretation (Fin.last gateCount))
                          (rho.refine extension) =
                        fun input => !((ScalarFunction.restrict
                          (prior.wireFunction interpretation (wires 0))
                          (rho.refine extension)) input) := by
                    funext input
                    simp only [ScalarFunction.restrict_apply,
                      Algebraic.Program.gateFunction_gate_last,
                      Algebraic.Line.eval, interpretation_not,
                      Function.comp_apply]
                    rfl
                  rw [gateFunctionEq]
                  exact sourceBounded.negate
              | and fanIn =>
                  have connective :
                      Fin.last gateCount ∈
                        connectiveGates (prior.gate ⟨.and fanIn, wires⟩) := by
                    rw [mem_connectiveGates,
                      Algebraic.Program.lines_gate_last]
                    simp [Op.connective]
                  exact next (Fin.last gateCount) connective gateDepth
              | or fanIn =>
                  have connective :
                      Fin.last gateCount ∈
                        connectiveGates (prior.gate ⟨.or fanIn, wires⟩) := by
                    rw [mem_connectiveGates,
                      Algebraic.Program.lines_gate_last]
                    simp [Op.connective]
                  exact next (Fin.last gateCount) connective gateDepth
        · have priorDepth :
              logicalWireDepths prior (Wire.gate priorGate) ≤ level + 1 := by
            unfold logicalGateDepths at wireDepth
            rw [Algebraic.Program.eval_gate_castSucc] at wireDepth
            rw [logicalWireDepths_gate]
            unfold logicalGateDepths
            exact wireDepth
          have bounded := priorResult (Wire.gate priorGate) priorDepth
          simpa only [Algebraic.Program.wireFunction_gate,
            Algebraic.Program.gateFunction_gate_castSucc] using bounded

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem ShallowUpTo.succ_of_connective
    {program : Algebraic.Program signature n g}
    {rho extension : PartialAssignment n}
    {level bound : Nat}
    (_normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level bound)
    (next : forall gate,
      gate ∈ connectiveGates program ->
      logicalGateDepths program gate ≤ level + 1 ->
      DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) bound) :
    ShallowUpTo program (rho.refine extension) (level + 1) bound :=
  shallow.succ_of_connective_raw next

end Program

namespace DNF

/-- Restricting a represented DNF composes exactly with the base
restriction. -/
theorem restrict_eval_eq_refine_of_eval_eq
    (formula : DNF n)
    (function : ScalarFunction Bool n)
    (rho extension : PartialAssignment n)
    (computes : forall input,
      formula.eval input = function.restrict rho input) :
    (formula.restrict extension).eval =
      function.restrict (rho.refine extension) := by
  funext input
  rw [DNF.restrict_sound, computes,
    ScalarFunction.restrict_apply, ScalarFunction.restrict_apply,
    PartialAssignment.apply_refine]

end DNF

namespace CNF

/-- Restricting a represented CNF composes exactly with the base
restriction. -/
theorem restrict_eval_eq_refine_of_eval_eq
    (formula : CNF n)
    (function : ScalarFunction Bool n)
    (rho extension : PartialAssignment n)
    (computes : forall input,
      formula.eval input = function.restrict rho input) :
    (formula.restrict extension).eval =
      function.restrict (rho.refine extension) := by
  funext input
  rw [CNF.restrict_sound, computes,
    ScalarFunction.restrict_apply, ScalarFunction.restrict_apply,
    PartialAssignment.apply_refine]

end CNF

namespace Program

/-- One charged gate in the next logical layer fails the common shallow-tree
bound with probability at most the switching-lemma estimate. -/
theorem ShallowUpTo.probability_gate_not_depthAtMost_refine_le_five
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
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
              (rho.refine extension)) bound) ≤
      (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
        (bound + 1)) := by
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
                  (rho.refine extension)) bound) =
            RandomRestriction.probability n p atMostOne
              (fun extension =>
                ¬DecisionTree.DepthAtMost
                  ((formula.restrict extension).eval) bound) := by
              congr 1
              funext extension
              rw [formula.restrict_eval_eq_refine_of_eval_eq
                (program.gateFunction interpretation gate) rho extension
                computes]
        _ ≤ (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
              (bound + 1)) :=
          RandomRestriction.probability_cnf_not_depthAtMost_restrict_le_five
            formula bounded bound p atMostOne
  | or fanIn =>
      obtain ⟨formula, bounded, computes⟩ :=
        shallow.exists_dnf_for_or_gate gate operation gateDepth
      calc
        RandomRestriction.probability n p atMostOne
            (fun extension =>
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) bound) =
            RandomRestriction.probability n p atMostOne
              (fun extension =>
                ¬DecisionTree.DepthAtMost
                  ((formula.restrict extension).eval) bound) := by
              congr 1
              funext extension
              rw [formula.restrict_eval_eq_refine_of_eval_eq
                (program.gateFunction interpretation gate) rho extension
                computes]
        _ ≤ (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
              (bound + 1)) :=
          RandomRestriction.probability_not_depthAtMost_restrict_le_five
            formula bounded bound p atMostOne

/-- The next-layer failure event for one charged gate obeys the same bound;
gates outside the layer contribute the empty event. -/
theorem ShallowUpTo.probability_gate_in_nextLayer_not_depthAtMost_refine_le_five
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
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
                (rho.refine extension)) bound) ≤
      (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
        (bound + 1)) := by
  by_cases gateDepth : logicalGateDepths program gate ≤ level + 1
  · calc
      RandomRestriction.probability n p atMostOne
          (fun extension =>
            logicalGateDepths program gate ≤ level + 1 ∧
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) bound) ≤
        RandomRestriction.probability n p atMostOne
          (fun extension =>
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate)
                (rho.refine extension)) bound) := by
          apply RandomRestriction.probability_mono n p atMostOne
          exact fun _ failure => failure.2
      _ ≤ (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
            (bound + 1)) :=
        shallow.probability_gate_not_depthAtMost_refine_le_five
          gate connective gateDepth p atMostOne
  · simp [gateDepth]

/-- Union bound over exactly the charged gates in the next logical layer. -/
theorem ShallowUpTo.probability_exists_connective_in_nextLayer_not_depthAtMost_refine_le_five
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension => Exists fun gate : Fin g =>
          gate ∈ connectiveGates program ∧
            logicalGateDepths program gate ≤ level + 1 ∧
              ¬DecisionTree.DepthAtMost
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate)
                  (rho.refine extension)) bound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
          (bound + 1)) := by
  let event (gate : Fin g) (extension : PartialAssignment n) : Prop :=
    logicalGateDepths program gate ≤ level + 1 ∧
      ¬DecisionTree.DepthAtMost
        (ScalarFunction.restrict
          (program.gateFunction interpretation gate)
          (rho.refine extension)) bound
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
          (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
            (bound + 1)) := by
      apply Finset.sum_le_sum
      intro gate connective
      exact shallow.probability_gate_in_nextLayer_not_depthAtMost_refine_le_five
        gate connective p atMostOne
    _ = (program.cost andOrCost : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
            (bound + 1)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_connectiveGates]

/-- One random switching step advances the semantic shallow-tree invariant by
one logical layer, except on an event of charged-size times the standard
switching-lemma failure probability. This raw form permits arbitrary internal
NOT gates. -/
theorem ShallowUpTo.probability_not_succ_refine_le_five_raw
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬ShallowUpTo program (rho.refine extension)
            (level + 1) bound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
          (bound + 1)) := by
  calc
    RandomRestriction.probability n p atMostOne
          (fun extension =>
            ¬ShallowUpTo program (rho.refine extension)
              (level + 1) bound) ≤
        RandomRestriction.probability n p atMostOne
          (fun extension => Exists fun gate : Fin g =>
            gate ∈ connectiveGates program ∧
              logicalGateDepths program gate ≤ level + 1 ∧
                ¬DecisionTree.DepthAtMost
                  (ScalarFunction.restrict
                    (program.gateFunction interpretation gate)
                    (rho.refine extension)) bound) := by
      apply RandomRestriction.probability_mono n p atMostOne
      intro extension failure
      by_contra noGateFailure
      apply failure
      apply shallow.succ_of_connective_raw
      intro gate connective gateDepth
      by_contra gateFailure
      exact noGateFailure ⟨gate, connective, gateDepth, gateFailure⟩
    _ ≤ (program.cost andOrCost : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
            (bound + 1)) :=
      shallow.probability_exists_connective_in_nextLayer_not_depthAtMost_refine_le_five
        p atMostOne

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem ShallowUpTo.probability_not_succ_refine_le_five
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (_normal : NegationsAtInputs program)
    (shallow : ShallowUpTo program rho level bound)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun extension =>
          ¬ShallowUpTo program (rho.refine extension)
            (level + 1) bound) ≤
      (program.cost andOrCost : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (bound : ENNReal)) ^
          (bound + 1)) :=
  shallow.probability_not_succ_refine_le_five_raw p atMostOne

end Program

end AC0
end Algebraic
