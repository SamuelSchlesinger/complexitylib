/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.AC0
public import Complexitylib.Algebraic.Fin
public import Complexitylib.Algebraic.PartialAssignment
public import Mathlib.Data.List.OfFn

/-!
# Partial evaluation of AC0 circuits

This module rebuilds arbitrary-fan-in AC0 programs after a Boolean partial
assignment. Fixed inputs and forced gates are represented as residual Boolean
constants, while genuinely live values are represented by wires over the
compact namespace of live variables.

The local connective simplifier is deliberately algebraic. An absorbing
constant forces an AND or OR gate; otherwise neutral constants are discarded
and the remaining wires feed one residual gate. No truth-table search or
finite-circuit optimization is involved.
-/

@[expose] public section

namespace Algebraic
namespace AC0

namespace Connective

/-- The arbitrary-fan-in operation associated with a connective. -/
def operation : Connective -> Nat -> Op
  | .and => .and
  | .or => .or

/-- The neutral Boolean for a connective. -/
def neutral : Connective -> Bool
  | .and => true
  | .or => false

/-- The Boolean which forces a connective independently of other inputs. -/
def absorbing : Connective -> Bool
  | .and => false
  | .or => true

/-- Boolean semantics of an arbitrary-fan-in connective. -/
def eval : (connective : Connective) -> (Fin r -> Bool) -> Bool
  | .and, input => interpretation (.and r) input
  | .or, input => interpretation (.or r) input

/-- Source logical depth of an arbitrary-fan-in connective. -/
def logicalDepth : (connective : Connective) -> (Fin r -> Nat) -> Nat
  | .and, input => logicalDepthInterpretation (.and r) input
  | .or, input => logicalDepthInterpretation (.or r) input

@[simp] theorem operation_cost
    (connective : Connective)
    (arity : Nat) :
    andOrCost (connective.operation arity) = 1 := by
  cases connective <;> rfl

end Connective

/-- A Boolean constant or a wire in a partially evaluated AC0 program. -/
inductive ResidualValue (n g : Nat)
  | constant (value : Bool)
  | wire (wire : Wire n g)
  deriving DecidableEq

namespace ResidualValue

/-- Evaluate a residual value in a residual program. -/
def eval
    (program : Program signature n g)
    (input : Fin n -> Bool) : ResidualValue n g -> Bool
  | .constant value => value
  | .wire sourceWire => program.trace interpretation input sourceWire

/-- Transport a residual value through a wire map. -/
def mapWires
    (wireMap : Wire n g -> Wire k h) :
    ResidualValue n g -> ResidualValue k h
  | .constant value => .constant value
  | .wire sourceWire => .wire (wireMap sourceWire)

/-- Return the represented wire, if the value is nonconstant. -/
def wire? : ResidualValue n g -> Option (Wire n g)
  | .constant _ => none
  | .wire sourceWire => some sourceWire

/-- Logical depth of a residual value, assigning depth zero to constants. -/
def logicalDepth
    (program : Program signature n g) : ResidualValue n g -> Nat
  | .constant _ => 0
  | .wire sourceWire =>
      program.trace logicalDepthInterpretation (fun _ => 0) sourceWire

@[simp] theorem eval_constant
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (value : Bool) :
    (constant value : ResidualValue n g).eval program input = value := rfl

@[simp] theorem eval_wire
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (wire : Wire n g) :
    (ResidualValue.wire wire).eval program input =
      program.trace interpretation input wire := rfl

@[simp] theorem mapWires_constant
    (wireMap : Wire n g -> Wire k h)
    (value : Bool) :
    (constant value : ResidualValue n g).mapWires wireMap =
      .constant value := rfl

@[simp] theorem mapWires_wire
    (wireMap : Wire n g -> Wire k h)
    (wire : Wire n g) :
    (ResidualValue.wire wire).mapWires wireMap =
      .wire (wireMap wire) := rfl

/-- Mapping residual wires preserves evaluation when the wire map preserves
the preceding program trace. -/
theorem eval_mapWires
    (value : ResidualValue n g)
    (wireMap : Wire.Renaming n g h)
    (source : Program signature n g)
    (result : Program signature n h)
    (input : Fin n -> Bool)
    (preserves : forall sourceWire,
      result.trace interpretation input (wireMap sourceWire) =
        source.trace interpretation input sourceWire) :
    (value.mapWires wireMap).eval result input =
      value.eval source input := by
  cases value with
  | constant value => rfl
  | wire sourceWire =>
      exact preserves sourceWire

/-- Mapping residual wires preserves logical depth when the wire map preserves
the preceding depth trace. -/
theorem logicalDepth_mapWires
    (value : ResidualValue n g)
    (wireMap : Wire.Renaming n g h)
    (source : Program signature n g)
    (result : Program signature n h)
    (preserves : forall sourceWire,
      result.trace logicalDepthInterpretation (fun _ => 0)
          (wireMap sourceWire) =
        source.trace logicalDepthInterpretation (fun _ => 0) sourceWire) :
    (value.mapWires wireMap).logicalDepth result =
      value.logicalDepth source := by
  cases value with
  | constant value => rfl
  | wire sourceWire => exact preserves sourceWire

end ResidualValue

/-- The nonconstant arguments of a gate, in their original order. -/
def residualWires
    (values : Fin r -> ResidualValue n g) : List (Wire n g) :=
  (List.ofFn values).filterMap ResidualValue.wire?

@[simp] theorem mem_residualWires
    (values : Fin r -> ResidualValue n g)
    (wire : Wire n g) :
    wire ∈ residualWires values <->
      Exists fun argument => values argument = .wire wire := by
  simp only [residualWires, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨argument, rfl⟩, present⟩
    cases value_eq : values argument with
    | constant value => simp [ResidualValue.wire?, value_eq] at present
    | wire sourceWire =>
      simp [ResidualValue.wire?, value_eq] at present
      subst sourceWire
      exact ⟨argument, value_eq⟩
  · rintro ⟨argument, value_eq⟩
    exact ⟨values argument, ⟨argument, rfl⟩, by
      simp [ResidualValue.wire?, value_eq]⟩

/-- A connective gate whose constant arguments have been removed. -/
def residualLine
    (connective : Connective)
    (wires : List (Wire n g)) : Line signature n g :=
  match connective with
  | .and =>
      { op := .and wires.length
        wires := wires.get }
  | .or =>
      { op := .or wires.length
        wires := wires.get }

/-- Result of locally simplifying one charged connective gate. -/
inductive GateReduction (n g : Nat)
  | value (result : ResidualValue n g)
  | line (result : Line signature n g)

namespace GateReduction

/-- Evaluate a local gate reduction against its preceding program. -/
def eval
    (program : Program signature n g)
    (input : Fin n -> Bool) : GateReduction n g -> Bool
  | .value result => result.eval program input
  | .line result =>
      result.eval interpretation input (program.eval interpretation input)

/-- Whether the reduction retains one charged gate. -/
def cost : GateReduction n g -> Nat
  | .value _ => 0
  | .line _ => 1

/-- Charged AND/OR cost contributed by a local gate reduction. -/
def chargedCost : GateReduction n g -> Nat
  | .value _ => 0
  | .line result => andOrCost result.op

/-- Logical depth contributed by a local gate reduction. -/
def logicalDepth
    (program : Program signature n g) : GateReduction n g -> Nat
  | .value result => result.logicalDepth program
  | .line result =>
      result.eval logicalDepthInterpretation (fun _ => 0)
        (program.eval logicalDepthInterpretation (fun _ => 0))

@[simp] theorem cost_le_one (result : GateReduction n g) :
    result.cost <= 1 := by
  cases result <;> simp [cost]

end GateReduction

/-- Simplify one arbitrary-fan-in AND or OR from already restricted arguments. -/
noncomputable def simplifyConnective
    (connective : Connective)
    (values : Fin r -> ResidualValue n g) :
    GateReduction n g :=
  if _forced : Exists fun argument =>
      values argument = .constant connective.absorbing then
    .value (.constant connective.absorbing)
  else
    let wires := residualWires values
    if _noWires : wires = [] then
      .value (.constant connective.neutral)
    else
      .line (residualLine connective wires)

/-- If a gate is not forced, every constant argument is its connective's
neutral value. -/
theorem argument_eval_eq_neutral_of_not_forced_of_not_wire
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing))
    (argument : Fin r)
    (notWire : Not (Exists fun sourceWire =>
      values argument = .wire sourceWire)) :
    (values argument).eval program input = connective.neutral := by
  cases value_eq : values argument with
  | wire sourceWire => exact False.elim (notWire ⟨sourceWire, value_eq⟩)
  | constant value =>
      have notAbsorbing :
          values argument ≠ .constant connective.absorbing :=
        fun equal => notForced ⟨argument, equal⟩
      cases connective <;> cases value <;>
        simp_all [Connective.absorbing, Connective.neutral]

/-- Removing neutral constants from a non-forced connective preserves its
Boolean value. -/
theorem residualLine_eval_of_not_forced
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing)) :
    (residualLine connective (residualWires values)).eval interpretation input
        (program.eval interpretation input) =
      connective.eval (fun argument =>
        (values argument).eval program input) := by
  cases connective with
  | and =>
      change interpretation (.and (residualWires values).length)
          (fun argument => program.trace interpretation input
            ((residualWires values).get argument)) =
        interpretation (.and r) (fun argument =>
          (values argument).eval program input)
      rw [Bool.eq_iff_iff, interpretation_and_eq_true,
        interpretation_and_eq_true]
      constructor
      · intro residualTrue argument
        cases value_eq : values argument with
        | constant value =>
            simpa [value_eq, Connective.neutral] using
              (argument_eval_eq_neutral_of_not_forced_of_not_wire
                .and values program input notForced argument (by
                  rintro ⟨sourceWire, impossible⟩
                  simp [value_eq] at impossible))
        | wire sourceWire =>
            have present : sourceWire ∈ residualWires values :=
              (mem_residualWires values sourceWire).2
                ⟨argument, value_eq⟩
            obtain ⟨residualArgument, selected⟩ :=
              List.mem_iff_get.mp present
            have selectedTrue := residualTrue residualArgument
            change program.trace interpretation input
              ((residualWires values).get residualArgument) = true at selectedTrue
            rw [selected] at selectedTrue
            exact selectedTrue
      · intro sourceTrue residualArgument
        have present := List.get_mem (residualWires values) residualArgument
        obtain ⟨argument, value_eq⟩ :=
          (mem_residualWires values _).1 present
        have argumentTrue := sourceTrue argument
        change program.trace interpretation input
          ((residualWires values).get residualArgument) = true
        simpa [value_eq] using argumentTrue
  | or =>
      change interpretation (.or (residualWires values).length)
          (fun argument => program.trace interpretation input
            ((residualWires values).get argument)) =
        interpretation (.or r) (fun argument =>
          (values argument).eval program input)
      rw [Bool.eq_iff_iff, interpretation_or_eq_true,
        interpretation_or_eq_true]
      constructor
      · rintro ⟨residualArgument, residualTrue⟩
        have present := List.get_mem (residualWires values) residualArgument
        obtain ⟨argument, value_eq⟩ :=
          (mem_residualWires values _).1 present
        refine ⟨argument, ?_⟩
        change program.trace interpretation input
          ((residualWires values).get residualArgument) = true at residualTrue
        simpa [value_eq] using residualTrue
      · rintro ⟨argument, argumentTrue⟩
        cases value_eq : values argument with
        | constant value =>
            have neutral :=
              argument_eval_eq_neutral_of_not_forced_of_not_wire
                .or values program input notForced argument (by
                  rintro ⟨sourceWire, impossible⟩
                  simp [value_eq] at impossible)
            rw [value_eq] at argumentTrue
            simp_all [Connective.neutral]
        | wire sourceWire =>
            have present : sourceWire ∈ residualWires values :=
              (mem_residualWires values sourceWire).2
                ⟨argument, value_eq⟩
            obtain ⟨residualArgument, selected⟩ :=
              List.mem_iff_get.mp present
            refine ⟨residualArgument, ?_⟩
            rw [selected]
            simpa [value_eq] using argumentTrue

/-- An absorbing residual constant forces the original connective. -/
theorem connective_eval_eq_absorbing_of_forced
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (forced : Exists fun argument =>
      values argument = .constant connective.absorbing) :
    connective.eval (fun argument =>
      (values argument).eval program input) = connective.absorbing := by
  cases connective with
  | and =>
      change interpretation (.and r) (fun argument =>
        (values argument).eval program input) = false
      apply Bool.eq_false_iff.mpr
      intro resultTrue
      obtain ⟨argument, value_eq⟩ := forced
      have argumentTrue :=
        (interpretation_and_eq_true _).1 resultTrue argument
      rw [value_eq] at argumentTrue
      contradiction
  | or =>
      change interpretation (.or r) (fun argument =>
        (values argument).eval program input) = true
      apply (interpretation_or_eq_true _).2
      obtain ⟨argument, value_eq⟩ := forced
      exact ⟨argument, by simp [value_eq, Connective.absorbing]⟩

/-- If no argument is a wire and the connective is not forced, all arguments
are neutral and so is the gate output. -/
theorem connective_eval_eq_neutral_of_no_wires
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool)
    (notForced : Not (Exists fun argument =>
      values argument = .constant connective.absorbing))
    (noWires : residualWires values = []) :
    connective.eval (fun argument =>
      (values argument).eval program input) = connective.neutral := by
  have noWire (argument : Fin r) :
      Not (Exists fun sourceWire => values argument = .wire sourceWire) := by
    rintro ⟨sourceWire, value_eq⟩
    have present : sourceWire ∈ residualWires values :=
      (mem_residualWires values sourceWire).2 ⟨argument, value_eq⟩
    rw [noWires] at present
    simp at present
  cases connective with
  | and =>
      change interpretation (.and r) (fun argument =>
        (values argument).eval program input) = true
      apply (interpretation_and_eq_true _).2
      intro argument
      exact argument_eval_eq_neutral_of_not_forced_of_not_wire
        .and values program input notForced argument (noWire argument)
  | or =>
      change interpretation (.or r) (fun argument =>
        (values argument).eval program input) = false
      apply Bool.eq_false_iff.mpr
      intro resultTrue
      obtain ⟨argument, argumentTrue⟩ :=
        (interpretation_or_eq_true _).1 resultTrue
      have neutral := argument_eval_eq_neutral_of_not_forced_of_not_wire
        .or values program input notForced argument (noWire argument)
      rw [neutral] at argumentTrue
      contradiction

/-- The local simplifier exactly preserves the value of an arbitrary-fan-in
AND or OR gate. -/
theorem simplifyConnective_eval
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool) :
    (simplifyConnective connective values).eval program input =
      connective.eval (fun argument =>
        (values argument).eval program input) := by
  unfold simplifyConnective
  split
  · rename_i forced
    exact (connective_eval_eq_absorbing_of_forced
      connective values program input forced).symm
  · rename_i notForced
    dsimp only
    split
    · rename_i noWires
      exact (connective_eval_eq_neutral_of_no_wires
        connective values program input notForced noWires).symm
    · exact residualLine_eval_of_not_forced
        connective values program input notForced

/-- Local connective simplification never contributes more than one charged
gate. -/
theorem simplifyConnective_chargedCost_le
    (connective : Connective)
    (values : Fin r -> ResidualValue n g) :
    (simplifyConnective connective values).chargedCost <= 1 := by
  unfold simplifyConnective
  split
  · simp [GateReduction.chargedCost]
  · dsimp only
    split
    · simp [GateReduction.chargedCost]
    · cases connective <;>
        simp [GateReduction.chargedCost, residualLine, andOrCost]

/-- Local connective simplification does not increase logical depth when each
residual argument is no deeper than its source argument. -/
theorem simplifyConnective_logicalDepth_le
    (connective : Connective)
    (values : Fin r -> ResidualValue n g)
    (program : Program signature n g)
    (sourceDepths : Fin r -> Nat)
    (bounds : forall argument,
      (values argument).logicalDepth program <= sourceDepths argument) :
    (simplifyConnective connective values).logicalDepth program <=
      connective.logicalDepth sourceDepths := by
  unfold simplifyConnective
  split
  · cases connective <;>
      simp [GateReduction.logicalDepth, ResidualValue.logicalDepth,
        Connective.logicalDepth, logicalDepthInterpretation]
  · dsimp only
    split
    · cases connective <;>
        simp [GateReduction.logicalDepth, ResidualValue.logicalDepth,
          Connective.logicalDepth, logicalDepthInterpretation]
    · have residualBound (residualArgument :
          Fin (residualWires values).length) :
          program.trace logicalDepthInterpretation (fun _ => 0)
              ((residualWires values).get residualArgument) <=
            Fin.foldl r
              (fun depth argument => max depth (sourceDepths argument)) 0 := by
        have present := List.get_mem (residualWires values) residualArgument
        obtain ⟨sourceArgument, value_eq⟩ :=
          (mem_residualWires values _).1 present
        calc
          program.trace logicalDepthInterpretation (fun _ => 0)
              ((residualWires values).get residualArgument) =
            (values sourceArgument).logicalDepth program := by
              rw [value_eq]
              rfl
          _ <= sourceDepths sourceArgument := bounds sourceArgument
          _ <= Fin.foldl r
                (fun depth argument => max depth (sourceDepths argument)) 0 :=
            Fin.le_foldl_max sourceDepths 0 sourceArgument
      cases connective <;>
        change Nat.succ
            (Fin.foldl (residualWires values).length
              (fun depth argument => max depth
                (program.trace logicalDepthInterpretation (fun _ => 0)
                  ((residualWires values).get argument))) 0) <=
          Nat.succ
            (Fin.foldl r
              (fun depth argument => max depth (sourceDepths argument)) 0) <;>
        exact Nat.succ_le_succ
          (Fin.foldl_max_le _ _ _ (Nat.zero_le _) residualBound)

/-- A unary NOT gate on a residual value: constants are folded and wires
retain one zero-cost NOT line. -/
def simplifyNot (value : ResidualValue n g) : GateReduction n g :=
  match value with
  | .constant result => .value (.constant (!result))
  | .wire sourceWire =>
      .line
        { op := .not
          wires := fun _ => sourceWire }

@[simp] theorem simplifyNot_eval
    (value : ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n -> Bool) :
    (simplifyNot value).eval program input =
      !(value.eval program input) := by
  cases value <;> rfl

@[simp] theorem simplifyNot_logicalDepth
    (value : ResidualValue n g)
    (program : Program signature n g) :
    (simplifyNot value).logicalDepth program =
      value.logicalDepth program := by
  cases value <;> rfl

/-- Simplify an AC0 line after assigning a residual value to every wire it
reads. -/
noncomputable def simplifyLine :
    (line : Line signature n g) ->
    (Wire n g -> ResidualValue k h) -> GateReduction k h
  | ⟨.not, wires⟩, values => simplifyNot (values (wires 0))
  | ⟨.and _r, wires⟩, values =>
      simplifyConnective .and (fun argument => values (wires argument))
  | ⟨.or _r, wires⟩, values =>
      simplifyConnective .or (fun argument => values (wires argument))

/-- Line simplification preserves the operation's value under the residual
wire valuation. -/
theorem simplifyLine_eval
    (line : Line signature n g)
    (values : Wire n g -> ResidualValue k h)
    (program : Program signature k h)
    (input : Fin k -> Bool) :
    (simplifyLine line values).eval program input =
      interpretation line.op (fun argument =>
        (values (line.wires argument)).eval program input) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | not => exact simplifyNot_eval (values (wires 0)) program input
  | and r =>
      simpa [simplifyLine, Connective.eval] using
        (simplifyConnective_eval .and
          (fun argument => values (wires argument)) program input)
  | or r =>
      simpa [simplifyLine, Connective.eval] using
        (simplifyConnective_eval .or
          (fun argument => values (wires argument)) program input)

/-- A simplified line costs no more charged gates than its source line. -/
theorem simplifyLine_chargedCost_le
    (line : Line signature n g)
    (values : Wire n g -> ResidualValue k h) :
    (simplifyLine line values).chargedCost <= andOrCost line.op := by
  rcases line with ⟨op, wires⟩
  cases op with
  | not =>
      cases value_eq : values (wires 0) <;>
        simp [simplifyLine, simplifyNot, value_eq,
          GateReduction.chargedCost, andOrCost]
  | and r =>
      exact simplifyConnective_chargedCost_le .and
        (fun argument => values (wires argument))
  | or r =>
      exact simplifyConnective_chargedCost_le .or
        (fun argument => values (wires argument))

/-- A simplified line is no deeper than its source line when every represented
wire is no deeper than the corresponding source wire. -/
theorem simplifyLine_logicalDepth_le
    (source : Program signature n g)
    (line : Line signature n g)
    (values : Wire n g -> ResidualValue k h)
    (result : Program signature k h)
    (bounds : forall sourceWire,
      (values sourceWire).logicalDepth result <=
        source.trace logicalDepthInterpretation (fun _ => 0) sourceWire) :
    (simplifyLine line values).logicalDepth result <=
      line.eval logicalDepthInterpretation (fun _ => 0)
        (source.eval logicalDepthInterpretation (fun _ => 0)) := by
  rcases line with ⟨op, wires⟩
  cases op with
  | not =>
      simpa [simplifyLine, Line.eval, logicalDepthInterpretation,
        Program.trace] using bounds (wires 0)
  | and r =>
      change (simplifyConnective .and
          (fun argument => values (wires argument))).logicalDepth result <=
        Connective.logicalDepth .and (fun argument =>
          source.trace logicalDepthInterpretation (fun _ => 0)
            (wires argument))
      exact simplifyConnective_logicalDepth_le .and
        (fun argument => values (wires argument)) result
        (fun argument => source.trace logicalDepthInterpretation
          (fun _ => 0) (wires argument))
        (fun argument => bounds (wires argument))
  | or r =>
      change (simplifyConnective .or
          (fun argument => values (wires argument))).logicalDepth result <=
        Connective.logicalDepth .or (fun argument =>
          source.trace logicalDepthInterpretation (fun _ => 0)
            (wires argument))
      exact simplifyConnective_logicalDepth_le .or
        (fun argument => values (wires argument)) result
        (fun argument => source.trace logicalDepthInterpretation
          (fun _ => 0) (wires argument))
        (fun argument => bounds (wires argument))

/-! ## Whole-program restriction -/

/-- The residual representation of one original input. -/
noncomputable def inputResidual
    (rho : PartialAssignment n)
    (sourceInput : Fin n) : ResidualValue rho.liveCount 0 :=
  if live : rho sourceInput = none then
    .wire (Wire.input (rho.liveIndex sourceInput live))
  else
    .constant ((rho sourceInput).getD false)

@[simp] theorem inputResidual_eval
    (rho : PartialAssignment n)
    (sourceInput : Fin n)
    (input : Fin rho.liveCount -> Bool) :
    (inputResidual rho sourceInput).eval Program.empty input =
      rho.toLiveInputSubstitution.apply input sourceInput := by
  by_cases live : rho sourceInput = none
  · simp [inputResidual, live, ResidualValue.eval, Program.trace,
      PartialAssignment.toLiveInputSubstitution, InputSubstitution.apply]
  · simp [inputResidual, live, ResidualValue.eval,
      PartialAssignment.toLiveInputSubstitution, InputSubstitution.apply]

/-- A proof-carrying partial evaluation of every wire in an AC0 program. -/
structure ProgramRestriction
    (source : Program signature n g)
    (rho : PartialAssignment n) where
  /-- Number of gates in the residual program. -/
  gateCount : Nat
  /-- Residual program over exactly the live variables. -/
  result : Program signature rho.liveCount gateCount
  /-- Constant-or-wire representation of every source wire. -/
  values : Wire n g -> ResidualValue rho.liveCount gateCount
  /-- Every represented wire has its exact restricted semantics. -/
  trace_eq : forall input sourceWire,
    (values sourceWire).eval result input =
      source.trace interpretation
        (rho.toLiveInputSubstitution.apply input) sourceWire
  /-- Every residual wire is no deeper than the source wire it represents. -/
  logicalDepth_le : forall sourceWire,
    (values sourceWire).logicalDepth result <=
      source.trace logicalDepthInterpretation (fun _ => 0) sourceWire
  /-- Partial evaluation does not increase the total gate count. -/
  gateCount_le : gateCount <= g
  /-- Partial evaluation does not increase charged AND/OR cost. -/
  cost_le : result.cost andOrCost <= source.cost andOrCost

namespace ProgramRestriction

/-- Restriction of the empty program compactly reindexes its live inputs. -/
noncomputable def empty
    (rho : PartialAssignment n) :
    ProgramRestriction (Program.empty : Program signature n 0) rho where
  gateCount := 0
  result := .empty
  values := Fin.addCases (inputResidual rho) Fin.elim0
  trace_eq := by
    intro input sourceWire
    refine Fin.addCases (fun sourceInput => ?_)
      (fun impossible => Fin.elim0 impossible) sourceWire
    rw [Fin.addCases_left, Program.trace_input]
    exact inputResidual_eval rho sourceInput input
  logicalDepth_le := by
    intro sourceWire
    refine Fin.addCases (fun sourceInput => ?_)
      (fun impossible => Fin.elim0 impossible) sourceWire
    rw [Fin.addCases_left, Program.trace_input]
    by_cases live : rho sourceInput = none <;>
      simp [inputResidual, live, ResidualValue.logicalDepth, Program.trace]
  gateCount_le := Nat.le_refl 0
  cost_le := Nat.le_refl 0

/-- Evaluate a source line through a restriction of its preceding program. -/
theorem line_eval
    {source : Program signature n g}
    {rho : PartialAssignment n}
    (restriction : ProgramRestriction source rho)
    (line : Line signature n g)
    (input : Fin rho.liveCount -> Bool) :
    line.eval interpretation
        (rho.toLiveInputSubstitution.apply input)
        (source.eval interpretation
          (rho.toLiveInputSubstitution.apply input)) =
      interpretation line.op (fun argument =>
        (restriction.values (line.wires argument)).eval
          restriction.result input) := by
  unfold Line.eval
  congr 1
  funext argument
  exact (restriction.trace_eq input (line.wires argument)).symm

/-- Delete the new last source gate because its residual value is already
available. -/
def reuseLast
    {source : Program signature n g}
    {rho : PartialAssignment n}
    (prior : ProgramRestriction source rho)
    (line : Line signature n g)
    (value : ResidualValue rho.liveCount prior.gateCount)
    (value_eq : forall input,
      value.eval prior.result input =
        line.eval interpretation
          (rho.toLiveInputSubstitution.apply input)
          (source.eval interpretation
            (rho.toLiveInputSubstitution.apply input)))
    (logicalDepthBound :
      value.logicalDepth prior.result <=
        line.eval logicalDepthInterpretation (fun _ => 0)
          (source.eval logicalDepthInterpretation (fun _ => 0))) :
    ProgramRestriction (source.gate line) rho where
  gateCount := prior.gateCount
  result := prior.result
  values := Fin.lastCases value prior.values
  trace_eq := by
    intro input sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last]
      calc
        value.eval prior.result input =
            line.eval interpretation
              (rho.toLiveInputSubstitution.apply input)
              (source.eval interpretation
                (rho.toLiveInputSubstitution.apply input)) :=
          value_eq input
        _ = (source.gate line).trace interpretation
              (rho.toLiveInputSubstitution.apply input)
              (Fin.last (n + g)) :=
          (Program.trace_gate_last source line interpretation _).symm
    · rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc]
      exact prior.trace_eq input oldWire
  logicalDepth_le := by
    intro sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last]
      exact logicalDepthBound.trans_eq
        (Program.trace_gate_last source line logicalDepthInterpretation _).symm
    · rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc]
      exact prior.logicalDepth_le oldWire
  gateCount_le := prior.gateCount_le.trans (Nat.le_succ g)
  cost_le := prior.cost_le.trans (Nat.le_add_right _ (andOrCost line.op))

/-- Retain the new last source gate as one residual line. Earlier residual
wires are embedded into the extended program. -/
def retainLast
    {source : Program signature n g}
    {rho : PartialAssignment n}
    (prior : ProgramRestriction source rho)
    (line : Line signature n g)
    (residualLine : Line signature rho.liveCount prior.gateCount)
    (line_eq : forall input,
      residualLine.eval interpretation input
          (prior.result.eval interpretation input) =
        line.eval interpretation
          (rho.toLiveInputSubstitution.apply input)
          (source.eval interpretation
            (rho.toLiveInputSubstitution.apply input)))
    (logicalDepthBound :
      residualLine.eval logicalDepthInterpretation (fun _ => 0)
          (prior.result.eval logicalDepthInterpretation (fun _ => 0)) <=
        line.eval logicalDepthInterpretation (fun _ => 0)
          (source.eval logicalDepthInterpretation (fun _ => 0)))
    (costBound : andOrCost residualLine.op <= andOrCost line.op) :
    ProgramRestriction (source.gate line) rho where
  gateCount := prior.gateCount + 1
  result := prior.result.gate residualLine
  values := Fin.lastCases
    (.wire (Fin.last (rho.liveCount + prior.gateCount)))
    (fun oldWire =>
      (prior.values oldWire).mapWires Wire.Renaming.castSucc)
  trace_eq := by
    intro input sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last, ResidualValue.eval_wire,
        Program.trace_gate_last]
      calc
        residualLine.eval interpretation input
            (prior.result.eval interpretation input) =
          line.eval interpretation
            (rho.toLiveInputSubstitution.apply input)
            (source.eval interpretation
              (rho.toLiveInputSubstitution.apply input)) :=
          line_eq input
        _ = (source.gate line).trace interpretation
              (rho.toLiveInputSubstitution.apply input)
              (Fin.last (n + g)) :=
          (Program.trace_gate_last source line interpretation _).symm
    · rw [Fin.lastCases_castSucc]
      calc
        ((prior.values oldWire).mapWires Wire.Renaming.castSucc).eval
            (prior.result.gate residualLine) input =
          (prior.values oldWire).eval prior.result input :=
            ResidualValue.eval_mapWires (prior.values oldWire)
              Wire.Renaming.castSucc prior.result
              (prior.result.gate residualLine) input (fun targetWire =>
                by simpa only [Wire.Renaming.castSucc_apply] using
                  Program.trace_gate_castSucc prior.result residualLine
                    interpretation input targetWire)
        _ = source.trace interpretation
              (rho.toLiveInputSubstitution.apply input) oldWire :=
          prior.trace_eq input oldWire
        _ = (source.gate line).trace interpretation
              (rho.toLiveInputSubstitution.apply input) oldWire.castSucc :=
          (Program.trace_gate_castSucc source line interpretation _ _).symm
  logicalDepth_le := by
    intro sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last, ResidualValue.logicalDepth,
        Program.trace_gate_last]
      exact logicalDepthBound.trans_eq
        (Program.trace_gate_last source line logicalDepthInterpretation _).symm
    · rw [Fin.lastCases_castSucc]
      calc
        ((prior.values oldWire).mapWires
            Wire.Renaming.castSucc).logicalDepth
            (prior.result.gate residualLine) =
          (prior.values oldWire).logicalDepth prior.result :=
            ResidualValue.logicalDepth_mapWires (prior.values oldWire)
              Wire.Renaming.castSucc prior.result
              (prior.result.gate residualLine) (fun targetWire => by
                simpa only [Wire.Renaming.castSucc_apply] using
                  Program.trace_gate_castSucc prior.result residualLine
                    logicalDepthInterpretation (fun _ => 0) targetWire)
        _ <= source.trace logicalDepthInterpretation (fun _ => 0) oldWire :=
          prior.logicalDepth_le oldWire
        _ = (source.gate line).trace logicalDepthInterpretation
              (fun _ => 0) oldWire.castSucc :=
          (Program.trace_gate_castSucc source line
            logicalDepthInterpretation (fun _ => 0) oldWire).symm
  gateCount_le := Nat.add_le_add_right prior.gateCount_le 1
  cost_le := by
    rw [Program.cost_gate, Program.cost_gate]
    exact Nat.add_le_add prior.cost_le costBound

/-- Simplify and append one source line to a restricted prefix. -/
noncomputable def append
    {source : Program signature n g}
    {rho : PartialAssignment n}
    (prior : ProgramRestriction source rho)
    (line : Line signature n g) :
    ProgramRestriction (source.gate line) rho := by
  let reduction := simplifyLine line prior.values
  cases reduction_eq : reduction with
  | value value =>
      have result_eq :
          simplifyLine line prior.values = .value value := by
        simpa [reduction] using reduction_eq
      apply reuseLast prior line value
      · intro input
        have simplified := simplifyLine_eval line prior.values
          prior.result input
        rw [result_eq] at simplified
        exact simplified.trans (prior.line_eval line input).symm
      · have depthBound := simplifyLine_logicalDepth_le source line
          prior.values prior.result prior.logicalDepth_le
        rw [result_eq] at depthBound
        exact depthBound
  | line residualLine =>
      have result_eq :
          simplifyLine line prior.values = .line residualLine := by
        simpa [reduction] using reduction_eq
      apply retainLast prior line residualLine
      · intro input
        have simplified := simplifyLine_eval line prior.values
          prior.result input
        rw [result_eq] at simplified
        exact simplified.trans (prior.line_eval line input).symm
      · have depthBound := simplifyLine_logicalDepth_le source line
          prior.values prior.result prior.logicalDepth_le
        rw [result_eq] at depthBound
        exact depthBound
      · have costBound := simplifyLine_chargedCost_le line prior.values
        rw [result_eq] at costBound
        exact costBound

end ProgramRestriction

/-- Partially evaluate every gate of an AC0 program under `rho`, rebuilding it
over exactly the live input coordinates. -/
noncomputable def restrictProgram
    (rho : PartialAssignment n) :
    (source : Program signature n g) -> ProgramRestriction source rho
  | .empty => ProgramRestriction.empty rho
  | .gate source line =>
      (restrictProgram rho source).append line

/-! ## Residual circuits -/

/-- An AC0 program whose designated outputs may be Boolean constants. Keeping
constants explicit is necessary for exact cost monotonicity: restricting a
zero-gate projection can produce a constant function. -/
structure ResidualCircuit (n g m : Nat) where
  /-- Internal residual program. -/
  program : Program signature n g
  /-- Constant-or-wire representative of each designated output. -/
  outputs : Fin m -> ResidualValue n g

namespace ResidualCircuit

/-- Evaluate all designated residual outputs. -/
def eval
    (circuit : ResidualCircuit n g m)
    (input : Fin n -> Bool) : Fin m -> Bool :=
  fun output => (circuit.outputs output).eval circuit.program input

/-- Charged AND/OR cost of a residual circuit. -/
def cost (circuit : ResidualCircuit n g m) : Nat :=
  circuit.program.cost andOrCost

/-- Logical depth of every residual output, with constant outputs at depth
zero. -/
def logicalOutputDepths
    (circuit : ResidualCircuit n g m) : Fin m -> Nat :=
  fun output => (circuit.outputs output).logicalDepth circuit.program

/-- Maximum logical depth of a residual output. -/
def logicalDepth (circuit : ResidualCircuit n g m) : Nat :=
  Fin.foldl m
    (fun depth output => max depth (circuit.logicalOutputDepths output)) 0

/-- A one-output residual circuit's depth is its sole output depth. -/
theorem logicalDepth_one_output
    (circuit : ResidualCircuit n g 1) :
    circuit.logicalDepth = circuit.logicalOutputDepths 0 := by
  simp [logicalDepth, Fin.foldl_succ]

end ResidualCircuit

/-- A circuit-level partial evaluation over the compact namespace of live
variables. -/
structure CircuitRestriction
    (source : Circuit signature n g m)
    (rho : PartialAssignment n) where
  /-- Number of gates in the residual circuit. -/
  gateCount : Nat
  /-- Residual circuit, including explicit constant outputs. -/
  result : ResidualCircuit rho.liveCount gateCount m
  /-- Exact pointwise semantics under the compact input substitution. -/
  eval_eq : forall input,
    result.eval input =
      source.eval interpretation
        (rho.toLiveInputSubstitution.apply input)
  /-- Every residual output is no deeper than its source output. -/
  logicalOutputDepths_le : forall output,
    result.logicalOutputDepths output <=
      Circuit.logicalOutputDepths source output
  /-- Partial evaluation does not increase total gate count. -/
  gateCount_le : gateCount <= g
  /-- Partial evaluation does not increase charged AND/OR cost. -/
  cost_le : result.cost <= source.cost andOrCost

/-- Partially evaluate an arbitrary-output AC0 circuit under `rho`. -/
noncomputable def restrictCircuit
    (source : Circuit signature n g m)
    (rho : PartialAssignment n) : CircuitRestriction source rho := by
  let restricted := restrictProgram rho source.program
  let result : ResidualCircuit rho.liveCount restricted.gateCount m :=
    { program := restricted.result
      outputs := fun output => restricted.values (source.outputs output) }
  exact
    { gateCount := restricted.gateCount
      result := result
      eval_eq := by
        intro input
        funext output
        exact restricted.trace_eq input (source.outputs output)
      logicalOutputDepths_le := fun output =>
        restricted.logicalDepth_le (source.outputs output)
      gateCount_le := restricted.gateCount_le
      cost_le := restricted.cost_le }

namespace CircuitRestriction

/-- Exact residual-circuit restriction does not increase logical depth. -/
theorem logicalDepth_le
    {source : Circuit signature n g m}
    {rho : PartialAssignment n}
    (restriction : CircuitRestriction source rho) :
    restriction.result.logicalDepth <= Circuit.logicalDepth source := by
  apply Fin.foldl_max_le
  · exact Nat.zero_le _
  · intro output
    exact (restriction.logicalOutputDepths_le output).trans
      (Fin.le_foldl_max (Circuit.logicalOutputDepths source) 0 output)

end CircuitRestriction

/-- The compact residual circuit also realizes the original same-width
restriction after projecting a complete input to its live coordinates. -/
theorem restrictCircuit_eval_projectLive
    (source : Circuit signature n g m)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (restrictCircuit source rho).result.eval (rho.projectLive input) =
      source.eval interpretation (rho.apply input) := by
  rw [(restrictCircuit source rho).eval_eq]
  rw [PartialAssignment.toLiveInputSubstitution_projectLive]

/-! ## Materializing a one-output residual circuit -/

/-- A nullary gate realizing a Boolean constant. -/
def constantLine (value : Bool) : Line signature n g :=
  match value with
  | false =>
      { op := .or 0
        wires := Fin.elim0 }
  | true =>
      { op := .and 0
        wires := Fin.elim0 }

@[simp] theorem constantLine_eval
    (value : Bool)
    (program : Program signature n g)
    (input : Fin n -> Bool) :
    (constantLine (n := n) (g := g) value).eval interpretation input
      (program.eval interpretation input) = value := by
  cases value <;> rfl

/-- Materializing the sole output of a residual circuit as an ordinary wire
requires at most one nullary constant gate. -/
structure ResidualCircuit.Materialization
    (source : ResidualCircuit n g 1) where
  /-- Gate count of the ordinary circuit. -/
  gateCount : Nat
  /-- Ordinary one-output circuit. -/
  result : Circuit signature n gateCount 1
  /-- Materialization preserves the residual output. -/
  eval_eq : forall input, result.eval interpretation input = source.eval input
  /-- Materializing a constant output adds at most one logical level. -/
  logicalDepth_le :
    Circuit.logicalDepth result <= source.logicalDepth + 1
  /-- At most one gate is added. -/
  gateCount_le : gateCount <= g + 1
  /-- At most one charged constant gate is added. -/
  cost_le : result.cost andOrCost <= source.cost + 1

namespace ResidualCircuit

/-- Convert a one-output residual circuit into an ordinary circuit. Wire
outputs are free; constant outputs receive one nullary AND or OR gate. -/
def materialize
    (source : ResidualCircuit n g 1) : source.Materialization := by
  cases output_eq : source.outputs 0 with
  | wire sourceWire =>
      let result : Circuit signature n g 1 :=
        { program := source.program
          outputs := fun _ => sourceWire }
      exact
        { gateCount := g
          result := result
          eval_eq := by
            intro input
            funext output
            have output_zero : output = 0 := Fin.eq_zero output
            subst output
            change source.program.trace interpretation input sourceWire =
              (source.outputs 0).eval source.program input
            rw [output_eq]
            exact (ResidualValue.eval_wire
              source.program input sourceWire).symm
          logicalDepth_le := by
            rw [Circuit.logicalDepth_one_output,
              ResidualCircuit.logicalDepth_one_output]
            change source.program.trace logicalDepthInterpretation
                (fun _ => 0) sourceWire <=
              (source.outputs 0).logicalDepth source.program + 1
            rw [output_eq]
            exact Nat.le_add_right _ 1
          gateCount_le := Nat.le_succ g
          cost_le := Nat.le_add_right _ 1 }
  | constant value =>
      let line := constantLine (n := n) (g := g) value
      let result : Circuit signature n (g + 1) 1 :=
        { program := source.program.gate line
          outputs := fun _ => Fin.last (n + g) }
      exact
        { gateCount := g + 1
          result := result
          eval_eq := by
            intro input
            funext output
            have output_zero : output = 0 := Fin.eq_zero output
            subst output
            change (source.program.gate line).trace interpretation input
                (Fin.last (n + g)) =
              (source.outputs 0).eval source.program input
            rw [Program.trace_gate_last, constantLine_eval, output_eq,
              ResidualValue.eval_constant]
          logicalDepth_le := by
            rw [Circuit.logicalDepth_one_output,
              ResidualCircuit.logicalDepth_one_output]
            change (source.program.gate line).trace
                logicalDepthInterpretation (fun _ => 0)
                (Fin.last (n + g)) <=
              (source.outputs 0).logicalDepth source.program + 1
            rw [Program.trace_gate_last, output_eq]
            cases value <;>
              simp [line, constantLine, Line.eval,
                logicalDepthInterpretation, ResidualValue.logicalDepth]
          gateCount_le := Nat.le_refl (g + 1)
          cost_le := by
            cases value <;>
              simp [result, ResidualCircuit.cost, Circuit.cost, line,
                constantLine, andOrCost] }

end ResidualCircuit

/-- An ordinary one-output circuit obtained by partial evaluation. The single
unit of possible overhead is exactly the cost of materializing a constant
output as a wire. -/
structure OrdinaryCircuitRestriction
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n) where
  /-- Gate count of the materialized restricted circuit. -/
  gateCount : Nat
  /-- Ordinary circuit over exactly the live variables. -/
  result : Circuit signature rho.liveCount gateCount 1
  /-- Exact pointwise semantics under the compact input substitution. -/
  eval_eq : forall input,
    result.eval interpretation input =
      source.eval interpretation
        (rho.toLiveInputSubstitution.apply input)
  /-- Restriction plus constant-output materialization adds at most one
  logical level. -/
  logicalDepth_le :
    Circuit.logicalDepth result <= Circuit.logicalDepth source + 1
  /-- Restriction and output materialization add at most one gate overall. -/
  gateCount_le : gateCount <= g + 1
  /-- Charged AND/OR cost grows by at most the one constant-output gate. -/
  cost_le : result.cost andOrCost <= source.cost andOrCost + 1

/-- Partially evaluate a one-output AC0 circuit and materialize its output as
an ordinary circuit wire. -/
noncomputable def restrictOneOutputCircuit
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n) :
    OrdinaryCircuitRestriction source rho := by
  let restricted := restrictCircuit source rho
  let materialized := restricted.result.materialize
  exact
    { gateCount := materialized.gateCount
      result := materialized.result
      eval_eq := by
        intro input
        exact (materialized.eval_eq input).trans (restricted.eval_eq input)
      logicalDepth_le := materialized.logicalDepth_le.trans
        (Nat.add_le_add_right restricted.logicalDepth_le 1)
      gateCount_le := materialized.gateCount_le.trans
        (Nat.add_le_add_right restricted.gateCount_le 1)
      cost_le := materialized.cost_le.trans
        (Nat.add_le_add_right restricted.cost_le 1) }

/-- Same-width semantics of the materialized restricted circuit. -/
theorem restrictOneOutputCircuit_eval_projectLive
    (source : Circuit signature n g 1)
    (rho : PartialAssignment n)
    (input : Fin n -> Bool) :
    (restrictOneOutputCircuit source rho).result.eval interpretation
        (rho.projectLive input) =
      source.eval interpretation (rho.apply input) := by
  rw [(restrictOneOutputCircuit source rho).eval_eq]
  rw [PartialAssignment.toLiveInputSubstitution_projectLive]

end AC0
end Algebraic
