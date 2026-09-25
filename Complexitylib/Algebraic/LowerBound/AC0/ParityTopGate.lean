/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.ParityCircuit
public import Complexitylib.Algebraic.LowerBound.AC0.ParityNormalForm

/-!
# The top-gate obstruction for parity circuits

Standard AC0 depth reduction stops one layer below the circuit output. If the
output already lies in the reduced layers, restricted parity's exact
decision-tree depth gives the contradiction. Otherwise the output is a genuine
next-layer connective: an OR has a bounded-width DNF and an AND has a
bounded-width CNF, so the restricted-parity normal-form lower bound applies.

This module packages that case split without assuming that the designated
output is syntactically a top AND or OR. Input outputs and input negations are
handled by their logical depth. Thus a depth-`i+1` parity circuit whose wires
through depth `i` are shallow leaves at most the common tree bound many
variables live.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Program

/-- A shallow invariant covering a wire that computes parity or complemented
parity forces the live count below the common tree-depth allowance. -/
theorem ShallowUpTo.parityUpToNegation_liveCount_le
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (wire : Wire n g)
    (wireDepth : logicalWireDepths program wire ≤ level)
    (phase : Parity.UpToNegation
      (program.wireFunction interpretation wire)) :
    rho.liveCount ≤ bound := by
  have bounded := shallow wire wireDepth
  rcases phase with parity | complement
  · rw [parity] at bounded
    exact (Parity.depthAtMost_iff_liveCount_le rho bound).1 bounded
  · rw [complement] at bounded
    have parityBounded := bounded.negate
    simp only [ScalarFunction.restrict_apply, Bool.not_not] at parityBounded
    exact (Parity.depthAtMost_iff_liveCount_le rho bound).1 parityBounded

/-- If a wire at most one logical layer above a shallow prefix computes
parity up to output negation, then at most the tree bound many variables are
live. The proof follows arbitrary NOT chains backwards until it reaches an
input, an already-shallow wire, or a connective gate. -/
theorem liveCount_le_of_shallowBelow_computes_parityUpToNegation
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (wire : Wire n g)
    (wireDepth : logicalWireDepths program wire ≤ level + 1)
    (phase : Parity.UpToNegation
      (program.wireFunction interpretation wire)) :
    rho.liveCount ≤ bound := by
  induction program generalizing rho level bound with
  | empty =>
      let input : Fin n := ⟨wire.val, by omega⟩
      have wireEq : wire = Wire.input (g := 0) input := by
        apply Fin.ext
        rfl
      apply shallow.parityUpToNegation_liveCount_le wire
      · rw [wireEq, logicalWireDepths_input]
        exact Nat.zero_le level
      · exact phase
  | @gate gateCount prior line inductionHypothesis =>
      have priorShallow : ShallowUpTo prior rho level bound := by
        intro priorWire priorDepth
        have widenedDepth :
            logicalWireDepths (prior.gate line) priorWire.castSucc ≤ level := by
          simpa [logicalWireDepths] using priorDepth
        have widened := shallow priorWire.castSucc widenedDepth
        have functionEq :
            (prior.gate line).wireFunction interpretation priorWire.castSucc =
              prior.wireFunction interpretation priorWire := by
          funext input
          exact Algebraic.Program.trace_gate_castSucc
            prior line interpretation input priorWire
        rw [functionEq] at widened
        exact widened
      revert wireDepth phase
      refine Fin.addCases (fun input _ phase => ?_)
        (fun gate wireDepth phase => ?_) wire
      · exact shallow.parityUpToNegation_liveCount_le
          (Wire.input input) (by simp) phase
      · rw [logicalWireDepths_gate] at wireDepth
        rw [Algebraic.Program.wireFunction_gate] at phase
        revert wireDepth phase
        refine Fin.lastCases (fun gateDepth phase => ?_)
          (fun priorGate gateDepth phase => ?_) gate
        · cases line with
          | mk operation wires =>
              cases operation with
              | not =>
                  have sourceDepth :
                      logicalWireDepths prior (wires 0) ≤ level + 1 := by
                    unfold logicalGateDepths at gateDepth
                    rw [Algebraic.Program.eval_gate_last] at gateDepth
                    simpa [Algebraic.Line.eval, logicalDepthInterpretation,
                      logicalWireDepths, Algebraic.Program.trace] using gateDepth
                  have gateFunctionEq :
                      (prior.gate ⟨.not, wires⟩).gateFunction
                          interpretation (Fin.last gateCount) =
                        fun input => !(prior.wireFunction
                          interpretation (wires 0) input) := by
                    funext input
                    simp only [Algebraic.Program.gateFunction_gate_last,
                      Algebraic.Line.eval, interpretation_not,
                      Function.comp_apply]
                    rfl
                  rw [gateFunctionEq] at phase
                  exact inductionHypothesis priorShallow (wires 0)
                    sourceDepth
                    ((Parity.upToNegation_negate_iff _).1 phase)
              | and fanIn =>
                  obtain ⟨formula, bounded, represents⟩ :=
                    shallow.exists_cnf_for_and_gate
                      (fanIn := fanIn) (Fin.last gateCount)
                      (by simp [Algebraic.Program.lines_gate_last]) gateDepth
                  exact formula.liveCount_le_width_of_computes_parityUpToNegation
                    rho bound bounded
                    ((prior.gate ⟨.and fanIn, wires⟩).gateFunction
                      interpretation (Fin.last gateCount))
                    phase represents
              | or fanIn =>
                  obtain ⟨formula, bounded, represents⟩ :=
                    shallow.exists_dnf_for_or_gate
                      (fanIn := fanIn) (Fin.last gateCount)
                      (by simp [Algebraic.Program.lines_gate_last]) gateDepth
                  exact formula.liveCount_le_width_of_computes_parityUpToNegation
                    rho bound bounded
                    ((prior.gate ⟨.or fanIn, wires⟩).gateFunction
                      interpretation (Fin.last gateCount))
                    phase represents
        · have priorDepth :
              logicalWireDepths prior (Wire.gate priorGate) ≤ level + 1 := by
            unfold logicalGateDepths at gateDepth
            rw [Algebraic.Program.eval_gate_castSucc] at gateDepth
            rw [logicalWireDepths_gate]
            unfold logicalGateDepths
            exact gateDepth
          have priorPhase : Parity.UpToNegation
              (prior.wireFunction interpretation (Wire.gate priorGate)) := by
            simpa only [Algebraic.Program.wireFunction_gate,
              Algebraic.Program.gateFunction_gate_castSucc] using phase
          exact inductionHypothesis priorShallow (Wire.gate priorGate)
            priorDepth priorPhase

end Program

namespace Circuit

/-- Reducing all but the possible top logical layer of a parity circuit is
enough to bound its remaining live variables, even with arbitrary internal
NOT gates. -/
theorem liveCount_le_of_shallowBelowTop_computes_parity_raw
    {circuit : Algebraic.Circuit signature n g 1}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depthBound : logicalDepth circuit ≤ level + 1)
    (shallow : Program.ShallowUpTo circuit.program rho level bound) :
    rho.liveCount ≤ bound := by
  have outputDepth :
      Program.logicalWireDepths circuit.program (circuit.outputs 0) ≤
        level + 1 :=
    logicalWireDepth_output_le circuit 0 (level + 1) depthBound
  have outputComputes :
      circuit.program.wireFunction interpretation (circuit.outputs 0) =
        Parity.function n :=
    wireFunction_output_eq_parity_of_computes computes
  apply Program.liveCount_le_of_shallowBelow_computes_parityUpToNegation
    shallow (circuit.outputs 0) outputDepth
  exact Or.inl outputComputes

/-- Compatibility wrapper for the checked input-negation presentation. -/
theorem liveCount_le_of_shallowBelowTop_computes_parity
    {circuit : Algebraic.Circuit signature n g 1}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (_normal : Program.NegationsAtInputs circuit.program)
    (computes : circuit.ComputesWith interpretation (Parity.target n))
    (depthBound : logicalDepth circuit ≤ level + 1)
    (shallow : Program.ShallowUpTo circuit.program rho level bound) :
    rho.liveCount ≤ bound :=
  liveCount_le_of_shallowBelowTop_computes_parity_raw
    computes depthBound shallow

end Circuit
end AC0
end Algebraic
