/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.AC0.BottomGate
public import Complexitylib.Algebraic.LowerBound.AC0.Switching.Family

/-!
# Simultaneous switching for bounded bottom gates

This module connects shared AC0 programs to the finite-family switching lemma.
It indexes by all `g` internal gates. Each eligible depth-one gate of fan-in at
most `t` is represented by its exact bounded DNF or CNF; every other index is
padded by a constant formula. Thus the union bound costs at most `g`, without
enumerating a subtype of gates or unfolding the shared circuit into a formula.

The public endpoint bounds the probability that any eligible internal gate's
restricted scalar function lacks a shallow decision tree. This is the
simultaneous bottom-layer estimate needed before an explicit gate-replacement
construction.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Program

/-- The indexed gate is a logical-depth-one AND of fan-in at most the stated
bound. -/
def IsBoundedBottomAnd
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : Prop :=
  match (program.lines gate).op with
  | .and fanIn =>
      logicalGateDepths program gate = 1 ∧ fanIn ≤ widthBound
  | .not | .or _ => False

/-- The indexed gate is a logical-depth-one OR of fan-in at most the stated
bound. -/
def IsBoundedBottomOr
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : Prop :=
  match (program.lines gate).op with
  | .or fanIn =>
      logicalGateDepths program gate = 1 ∧ fanIn ≤ widthBound
  | .not | .and _ => False

/-- Bounded bottom-AND membership is decidable from the stored line. -/
instance isBoundedBottomAndDecidable
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : Decidable (IsBoundedBottomAnd program widthBound gate) := by
  unfold IsBoundedBottomAnd
  split <;> infer_instance

/-- Bounded bottom-OR membership is decidable from the stored line. -/
instance isBoundedBottomOrDecidable
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : Decidable (IsBoundedBottomOr program widthBound gate) := by
  unfold IsBoundedBottomOr
  split <;> infer_instance

/-- Existential fan-in characterization of a bounded bottom AND gate. -/
theorem isBoundedBottomAnd_iff_exists
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) :
    IsBoundedBottomAnd program widthBound gate ↔
      Exists fun fanIn =>
        (program.lines gate).op = .and fanIn ∧
          logicalGateDepths program gate = 1 ∧
          fanIn ≤ widthBound := by
  cases operation : (program.lines gate).op <;>
    simp [IsBoundedBottomAnd, operation]

/-- Existential fan-in characterization of a bounded bottom OR gate. -/
theorem isBoundedBottomOr_iff_exists
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) :
    IsBoundedBottomOr program widthBound gate ↔
      Exists fun fanIn =>
        (program.lines gate).op = .or fanIn ∧
          logicalGateDepths program gate = 1 ∧
          fanIn ≤ widthBound := by
  cases operation : (program.lines gate).op <;>
    simp [IsBoundedBottomOr, operation]

/-- A bounded DNF represents an eligible bottom AND gate exactly. -/
def RepresentsBoundedBottomAnd
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g)
    (formula : DNF n) : Prop :=
  IsBoundedBottomAnd program widthBound gate ∧
    formula.WidthAtMost widthBound ∧
    forall input,
      formula.eval input =
        program.gateFunction interpretation gate input

/-- A bounded CNF represents an eligible bottom OR gate exactly. -/
def RepresentsBoundedBottomOr
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g)
    (formula : CNF n) : Prop :=
  IsBoundedBottomOr program widthBound gate ∧
    formula.WidthAtMost widthBound ∧
    forall input,
      formula.eval input =
        program.gateFunction interpretation gate input

/-- Every eligible bottom AND gate has a bounded DNF representation. -/
theorem exists_representsBoundedBottomAnd
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound) :
    Exists fun formula : DNF n =>
      RepresentsBoundedBottomAnd program widthBound gate formula := by
  let formula := andGateFormula program normal gate operation depthOne
  refine ⟨formula, (isBoundedBottomAnd_iff_exists
    program widthBound gate).2 ⟨fanIn, operation, depthOne, bounded⟩, ?_, ?_⟩
  · exact (andGateFormula_widthAtMost program normal gate
      operation depthOne).mono bounded
  · exact andGateFormula_eval program normal gate operation depthOne

/-- Every eligible bottom OR gate has a bounded CNF representation. -/
theorem exists_representsBoundedBottomOr
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound) :
    Exists fun formula : CNF n =>
      RepresentsBoundedBottomOr program widthBound gate formula := by
  let formula := orGateFormula program normal gate operation depthOne
  refine ⟨formula, (isBoundedBottomOr_iff_exists
    program widthBound gate).2 ⟨fanIn, operation, depthOne, bounded⟩, ?_, ?_⟩
  · exact (orGateFormula_widthAtMost program normal gate
      operation depthOne).mono bounded
  · exact orGateFormula_eval program normal gate operation depthOne

/-- Choose an exact bounded DNF for an eligible gate, and use constant false
at every other program index. -/
noncomputable def paddedAndBottomFormula
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : DNF n := by
  letI : Decidable (Exists fun formula : DNF n =>
      RepresentsBoundedBottomAnd program widthBound gate formula) :=
    Classical.propDecidable _
  exact if represented : Exists fun formula : DNF n =>
      RepresentsBoundedBottomAnd program widthBound gate formula then
    Classical.choose represented
  else
    DNF.bottom

/-- Choose an exact bounded CNF for an eligible gate, and use constant true at
every other program index. -/
noncomputable def paddedOrBottomFormula
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) : CNF n := by
  letI : Decidable (Exists fun formula : CNF n =>
      RepresentsBoundedBottomOr program widthBound gate formula) :=
    Classical.propDecidable _
  exact if represented : Exists fun formula : CNF n =>
      RepresentsBoundedBottomOr program widthBound gate formula then
    Classical.choose represented
  else
    CNF.top

/-- Every member of the padded AND family has the common width bound. -/
theorem paddedAndBottomFormula_widthAtMost
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) :
    (paddedAndBottomFormula program widthBound gate).WidthAtMost
      widthBound := by
  classical
  unfold paddedAndBottomFormula
  split
  next represented =>
    exact (Classical.choose_spec represented).2.1
  next notRepresented =>
    intro term present
    simp [DNF.bottom] at present

/-- Every member of the padded OR family has the common width bound. -/
theorem paddedOrBottomFormula_widthAtMost
    (program : Algebraic.Program signature n g)
    (widthBound : Nat)
    (gate : Fin g) :
    (paddedOrBottomFormula program widthBound gate).WidthAtMost
      widthBound := by
  classical
  unfold paddedOrBottomFormula
  split
  next represented =>
    exact (Classical.choose_spec represented).2.1
  next notRepresented =>
    intro clause present
    simp [CNF.top] at present

/-- At an eligible AND gate, the padded formula computes the internal gate
function. -/
theorem paddedAndBottomFormula_eval_of_bottom
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound)
    (input : Fin n -> Bool) :
    (paddedAndBottomFormula program widthBound gate).eval input =
      program.gateFunction interpretation gate input := by
  classical
  have represented := exists_representsBoundedBottomAnd
    program normal widthBound gate operation depthOne bounded
  unfold paddedAndBottomFormula
  rw [dite_eq_left represented]
  exact (Classical.choose_spec represented).2.2 input

/-- At an eligible OR gate, the padded formula computes the internal gate
function. -/
theorem paddedOrBottomFormula_eval_of_bottom
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound)
    (input : Fin n -> Bool) :
    (paddedOrBottomFormula program widthBound gate).eval input =
      program.gateFunction interpretation gate input := by
  classical
  have represented := exists_representsBoundedBottomOr
    program normal widthBound gate operation depthOne bounded
  unfold paddedOrBottomFormula
  rw [dite_eq_left represented]
  exact (Classical.choose_spec represented).2.2 input

/-- Restricting the padded AND formula agrees with semantic restriction of the
internal gate function. -/
theorem paddedAndBottomFormula_restrict_eval_of_bottom
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .and fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound)
    (rho : PartialAssignment n) :
    ((paddedAndBottomFormula program widthBound gate).restrict rho).eval =
      ScalarFunction.restrict
        (program.gateFunction interpretation gate) rho := by
  funext input
  rw [DNF.restrict_sound, ScalarFunction.restrict_apply,
    paddedAndBottomFormula_eval_of_bottom program normal widthBound gate
      operation depthOne bounded]

/-- Restricting the padded OR formula agrees with semantic restriction of the
internal gate function. -/
theorem paddedOrBottomFormula_restrict_eval_of_bottom
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound : Nat)
    (gate : Fin g)
    {fanIn : Nat}
    (operation : (program.lines gate).op = .or fanIn)
    (depthOne : logicalGateDepths program gate = 1)
    (bounded : fanIn ≤ widthBound)
    (rho : PartialAssignment n) :
    ((paddedOrBottomFormula program widthBound gate).restrict rho).eval =
      ScalarFunction.restrict
        (program.gateFunction interpretation gate) rho := by
  funext input
  rw [CNF.restrict_sound, ScalarFunction.restrict_apply,
    paddedOrBottomFormula_eval_of_bottom program normal widthBound gate
      operation depthOne bounded]

/-- Simultaneous switching bound for all bounded bottom AND gates in a shared
program. -/
theorem probability_exists_boundedBottomAnd_depthAtLeast_restrict_le_five
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          IsBoundedBottomAnd program widthBound gate ∧
            DecisionTree.DepthAtLeast
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              pathLength) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) := by
  let formulas : Fin g -> DNF n :=
    paddedAndBottomFormula program widthBound
  calc
    RandomRestriction.probability n p atMostOne
          (fun rho => Exists fun gate : Fin g =>
            IsBoundedBottomAnd program widthBound gate ∧
              DecisionTree.DepthAtLeast
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate) rho)
                pathLength) ≤
        RandomRestriction.probability n p atMostOne
          (fun rho => ∃ gate, DecisionTree.DepthAtLeast
            ((formulas gate).restrict rho).eval pathLength) := by
      apply RandomRestriction.probability_mono n p atMostOne
      rintro rho ⟨gate, bottom, lower⟩
      obtain ⟨fanIn, operation, depthOne, bounded⟩ :=
        (isBoundedBottomAnd_iff_exists program widthBound gate).1 bottom
      refine ⟨gate, ?_⟩
      rw [paddedAndBottomFormula_restrict_eval_of_bottom program normal
        widthBound gate operation depthOne bounded]
      exact lower
    _ ≤ (g : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength) :=
      RandomRestriction.probability_exists_dnf_depthAtLeast_restrict_le_five
        formulas (paddedAndBottomFormula_widthAtMost program widthBound)
          pathLength p atMostOne

/-- Simultaneous switching bound for all bounded bottom OR gates in a shared
program. -/
theorem probability_exists_boundedBottomOr_depthAtLeast_restrict_le_five
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound pathLength : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          IsBoundedBottomOr program widthBound gate ∧
            DecisionTree.DepthAtLeast
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              pathLength) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          pathLength) := by
  let formulas : Fin g -> CNF n :=
    paddedOrBottomFormula program widthBound
  calc
    RandomRestriction.probability n p atMostOne
          (fun rho => Exists fun gate : Fin g =>
            IsBoundedBottomOr program widthBound gate ∧
              DecisionTree.DepthAtLeast
                (ScalarFunction.restrict
                  (program.gateFunction interpretation gate) rho)
                pathLength) ≤
        RandomRestriction.probability n p atMostOne
          (fun rho => ∃ gate, DecisionTree.DepthAtLeast
            ((formulas gate).restrict rho).eval pathLength) := by
      apply RandomRestriction.probability_mono n p atMostOne
      rintro rho ⟨gate, bottom, lower⟩
      obtain ⟨fanIn, operation, depthOne, bounded⟩ :=
        (isBoundedBottomOr_iff_exists program widthBound gate).1 bottom
      refine ⟨gate, ?_⟩
      rw [paddedOrBottomFormula_restrict_eval_of_bottom program normal
        widthBound gate operation depthOne bounded]
      exact lower
    _ ≤ (g : ENNReal) *
          (((5 : ENNReal) * (p : ENNReal) *
            (widthBound : ENNReal)) ^ pathLength) :=
      RandomRestriction.probability_exists_cnf_depthAtLeast_restrict_le_five
        formulas (paddedOrBottomFormula_widthAtMost program widthBound)
          pathLength p atMostOne

/-- Off-by-one shallow-tree form for all bounded bottom AND gates. -/
theorem probability_exists_boundedBottomAnd_not_depthAtMost_restrict_le_five
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          IsBoundedBottomAnd program widthBound gate ∧
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              depthBound) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_exists_boundedBottomAnd_depthAtLeast_restrict_le_five
      program normal widthBound (depthBound + 1) p atMostOne

/-- Off-by-one shallow-tree form for all bounded bottom OR gates. -/
theorem probability_exists_boundedBottomOr_not_depthAtMost_restrict_le_five
    (program : Algebraic.Program signature n g)
    (normal : NegationsAtInputs program)
    (widthBound depthBound : Nat)
    (p : NNReal)
    (atMostOne : p ≤ 1) :
    RandomRestriction.probability n p atMostOne
        (fun rho => Exists fun gate : Fin g =>
          IsBoundedBottomOr program widthBound gate ∧
            ¬DecisionTree.DepthAtMost
              (ScalarFunction.restrict
                (program.gateFunction interpretation gate) rho)
              depthBound) ≤
      (g : ENNReal) *
        (((5 : ENNReal) * (p : ENNReal) * (widthBound : ENNReal)) ^
          (depthBound + 1)) := by
  simpa only [DecisionTree.depthAtLeast_succ_iff_not_depthAtMost] using
    probability_exists_boundedBottomOr_depthAtLeast_restrict_le_five
      program normal widthBound (depthBound + 1) p atMostOne

end Program
end AC0
end Algebraic
