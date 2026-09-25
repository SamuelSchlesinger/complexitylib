/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.Layer
public import Mathlib.Data.List.OfFn

/-!
# Bounded normal forms for the next AC0 layer

Suppose every wire through logical depth `i` has a decision tree of depth at
most `t` after a restriction. The tree-to-normal-form theorem gives every
argument of a connective gate in layer `i + 1` an exact width-`t` DNF and CNF.
Flattening the argument DNFs through an OR, or the argument CNFs through an
AND, preserves that common width bound regardless of the gate's fan-in.

This is the deterministic composition step in the standard layer-by-layer
switching-lemma application. It traverses supplied formulas and stored gate
arguments structurally; it neither expands a truth table nor searches for an
optimal representation.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace DNF

/-- Disjoin a finite indexed family of DNFs by flattening their ordered term
lists. -/
def disjoinFamily (formulas : Fin count -> DNF n) : DNF n :=
  ⟨(List.ofFn formulas).flatMap DNF.terms⟩

/-- Finite DNF disjunction agrees with the unbounded OR interpretation. -/
theorem eval_disjoinFamily
    (formulas : Fin count -> DNF n)
    (input : Fin n -> Bool) :
    (disjoinFamily formulas).eval input =
      interpretation (.or count) (fun index => (formulas index).eval input) := by
  apply Bool.eq_iff_iff.mpr
  rw [DNF.eval_eq_true, interpretation_or_eq_true]
  constructor
  · rintro ⟨term, termPresent, satisfied⟩
    obtain ⟨formula, formulaPresent, termPresent⟩ :=
      List.mem_flatMap.mp termPresent
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp formulaPresent
    exact ⟨index, (DNF.eval_eq_true _ _).2 ⟨term, termPresent, satisfied⟩⟩
  · rintro ⟨index, formulaTrue⟩
    obtain ⟨term, termPresent, satisfied⟩ :=
      (DNF.eval_eq_true _ _).1 formulaTrue
    refine ⟨term, List.mem_flatMap.mpr ⟨formulas index, ?_, termPresent⟩,
      satisfied⟩
    exact List.mem_ofFn.mpr ⟨index, rfl⟩

/-- Flattening a finite family preserves a common DNF width bound. -/
theorem WidthAtMost.disjoinFamily
    {formulas : Fin count -> DNF n}
    {bound : Nat}
    (bounded : forall index, (formulas index).WidthAtMost bound) :
    (disjoinFamily formulas).WidthAtMost bound := by
  intro term termPresent
  obtain ⟨formula, formulaPresent, termPresent⟩ :=
    List.mem_flatMap.mp termPresent
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp formulaPresent
  exact bounded index term termPresent

end DNF

namespace CNF

/-- Conjoin a finite indexed family of CNFs by flattening their ordered clause
lists. -/
def conjoinFamily (formulas : Fin count -> CNF n) : CNF n :=
  ⟨(List.ofFn formulas).flatMap CNF.clauses⟩

/-- Finite CNF conjunction agrees with the unbounded AND interpretation. -/
theorem eval_conjoinFamily
    (formulas : Fin count -> CNF n)
    (input : Fin n -> Bool) :
    (conjoinFamily formulas).eval input =
      interpretation (.and count) (fun index => (formulas index).eval input) := by
  apply Bool.eq_iff_iff.mpr
  rw [CNF.eval_eq_true, interpretation_and_eq_true]
  constructor
  · intro allClauses index
    apply (CNF.eval_eq_true _ _).2
    intro clause clausePresent
    apply allClauses clause
    exact List.mem_flatMap.mpr
      ⟨formulas index, List.mem_ofFn.mpr ⟨index, rfl⟩, clausePresent⟩
  · intro allFormulas clause clausePresent
    obtain ⟨formula, formulaPresent, clausePresent⟩ :=
      List.mem_flatMap.mp clausePresent
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp formulaPresent
    exact (CNF.eval_eq_true _ _).1 (allFormulas index) clause clausePresent

/-- Flattening a finite family preserves a common CNF width bound. -/
theorem WidthAtMost.conjoinFamily
    {formulas : Fin count -> CNF n}
    {bound : Nat}
    (bounded : forall index, (formulas index).WidthAtMost bound) :
    (conjoinFamily formulas).WidthAtMost bound := by
  intro clause clausePresent
  obtain ⟨formula, formulaPresent, clausePresent⟩ :=
    List.mem_flatMap.mp clausePresent
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp formulaPresent
  exact bounded index clause clausePresent

end CNF

namespace Line

/-- Evaluation of a line known to be an OR, with its dependent argument type
transported to the declared fan-in. -/
theorem eval_eq_or
    (line : Algebraic.Line signature n g)
    (inputs : Fin n -> Bool)
    (gates : Fin g -> Bool)
    {fanIn : Nat}
    (operation : line.op = .or fanIn) :
    line.eval interpretation inputs gates =
      interpretation (.or fanIn) (fun argument =>
        Wire.elim inputs gates
          (line.wires
            (Fin.cast (congrArg arity operation).symm argument))) := by
  cases line with
  | mk actualOperation wires =>
      cases actualOperation with
      | not => contradiction
      | and actualFanIn => contradiction
      | or actualFanIn =>
          cases operation
          rfl

/-- Evaluation of a line known to be an AND, with its dependent argument type
transported to the declared fan-in. -/
theorem eval_eq_and
    (line : Algebraic.Line signature n g)
    (inputs : Fin n -> Bool)
    (gates : Fin g -> Bool)
    {fanIn : Nat}
    (operation : line.op = .and fanIn) :
    line.eval interpretation inputs gates =
      interpretation (.and fanIn) (fun argument =>
        Wire.elim inputs gates
          (line.wires
            (Fin.cast (congrArg arity operation).symm argument))) := by
  cases line with
  | mk actualOperation wires =>
      cases actualOperation with
      | not => contradiction
      | and actualFanIn =>
          cases operation
          rfl
      | or actualFanIn => contradiction

end Line

namespace Program

/-- Choose exact bounded DNFs for all arguments of a connective gate in the
next logical layer. -/
theorem ShallowUpTo.exists_argumentDNFs
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    (connective : (program.lines gate).op.connective ≠ none)
    (gateDepth : logicalGateDepths program gate ≤ level + 1) :
    Exists fun formulas :
        Fin (arity (program.lines gate).op) -> DNF n =>
      (forall argument, (formulas argument).WidthAtMost bound) /\
        forall argument input,
          (formulas argument).eval input =
            ScalarFunction.restrict
              (program.wireFunction interpretation
                ((program.lines gate).wires argument)) rho input := by
  classical
  let representation (argument : Fin (arity (program.lines gate).op)) :=
    DecisionTree.exists_dnf_widthAtMost_of_depthAtMost
      (shallow.argument gate connective gateDepth argument)
  let formulas (argument : Fin (arity (program.lines gate).op)) : DNF n :=
    Classical.choose (representation argument)
  refine ⟨formulas, ?_, ?_⟩
  · intro argument
    exact (Classical.choose_spec (representation argument)).1
  · intro argument input
    exact (Classical.choose_spec (representation argument)).2 input

/-- Choose exact bounded CNFs for all arguments of a connective gate in the
next logical layer. -/
theorem ShallowUpTo.exists_argumentCNFs
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    (connective : (program.lines gate).op.connective ≠ none)
    (gateDepth : logicalGateDepths program gate ≤ level + 1) :
    Exists fun formulas :
        Fin (arity (program.lines gate).op) -> CNF n =>
      (forall argument, (formulas argument).WidthAtMost bound) /\
        forall argument input,
          (formulas argument).eval input =
            ScalarFunction.restrict
              (program.wireFunction interpretation
                ((program.lines gate).wires argument)) rho input := by
  classical
  let representation (argument : Fin (arity (program.lines gate).op)) :=
    DecisionTree.exists_cnf_widthAtMost_of_depthAtMost
      (shallow.argument gate connective gateDepth argument)
  let formulas (argument : Fin (arity (program.lines gate).op)) : CNF n :=
    Classical.choose (representation argument)
  refine ⟨formulas, ?_, ?_⟩
  · intro argument
    exact (Classical.choose_spec (representation argument)).1
  · intro argument input
    exact (Classical.choose_spec (representation argument)).2 input

/-- An OR gate in the next layer has an exact DNF of the current common
decision-tree width. -/
theorem ShallowUpTo.exists_dnf_for_or_gate
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (gateDepth : logicalGateDepths program gate ≤ level + 1) :
    Exists fun formula : DNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input =
          ScalarFunction.restrict
            (program.gateFunction interpretation gate) rho input := by
  have connective : (program.lines gate).op.connective ≠ none := by
    rw [operation]
    simp [Op.connective]
  obtain ⟨argumentFormulas, argumentBounded, argumentComputes⟩ :=
    shallow.exists_argumentDNFs gate connective gateDepth
  let formulas : Fin fanIn -> DNF n := fun argument =>
    argumentFormulas
      (Fin.cast (congrArg arity operation).symm argument)
  refine ⟨DNF.disjoinFamily formulas, ?_, ?_⟩
  · apply DNF.WidthAtMost.disjoinFamily
    intro argument
    exact argumentBounded _
  · intro input
    rw [DNF.eval_disjoinFamily, ScalarFunction.restrict_apply]
    rw [Algebraic.Program.gateFunction_apply]
    rw [← program.lines_eval interpretation (rho.apply input) gate]
    rw [AC0.Line.eval_eq_or _ _ _ operation]
    congr 1
    funext argument
    simp only [formulas]
    rw [argumentComputes]
    rfl

/-- An AND gate in the next layer has an exact CNF of the current common
decision-tree width. -/
theorem ShallowUpTo.exists_cnf_for_and_gate
    {program : Algebraic.Program signature n g}
    {rho : PartialAssignment n}
    {level bound : Nat}
    (shallow : ShallowUpTo program rho level bound)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (gateDepth : logicalGateDepths program gate ≤ level + 1) :
    Exists fun formula : CNF n =>
      formula.WidthAtMost bound /\
        forall input, formula.eval input =
          ScalarFunction.restrict
            (program.gateFunction interpretation gate) rho input := by
  have connective : (program.lines gate).op.connective ≠ none := by
    rw [operation]
    simp [Op.connective]
  obtain ⟨argumentFormulas, argumentBounded, argumentComputes⟩ :=
    shallow.exists_argumentCNFs gate connective gateDepth
  let formulas : Fin fanIn -> CNF n := fun argument =>
    argumentFormulas
      (Fin.cast (congrArg arity operation).symm argument)
  refine ⟨CNF.conjoinFamily formulas, ?_, ?_⟩
  · apply CNF.WidthAtMost.conjoinFamily
    intro argument
    exact argumentBounded _
  · intro input
    rw [CNF.eval_conjoinFamily, ScalarFunction.restrict_apply]
    rw [Algebraic.Program.gateFunction_apply]
    rw [← program.lines_eval interpretation (rho.apply input) gate]
    rw [AC0.Line.eval_eq_and _ _ _ operation]
    congr 1
    funext argument
    simp only [formulas]
    rw [argumentComputes]
    rfl

end Program

end AC0
end Algebraic
