/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan.Origin
public import Complexitylib.Algebraic.Reduction
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Card

/-!
# De Morgan circuit restriction

This module partially evaluates a De Morgan circuit after fixing one input.
Every old wire is represented by a Boolean constant or by a possibly-negated
wire of the residual circuit. Binary gates made constant, projections, or
tautologies are deleted; every other binary gate is retained. The construction
tracks the exact number of deleted charged gates.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-! ## Restricting a whole program -/

/--
Result of restricting a program. `deleted` records exactly the charged source
gates removed by partial evaluation.
-/
structure ProgramRestriction
    (source : Program signature (n + 1) g)
    (selected : Fin (n + 1))
    (fixedValue : Bool) where
  /-- Number of residual internal gates, including free materialization gates. -/
  gateCount : Nat
  /-- Residual program on the remaining inputs. -/
  result : Program signature n gateCount
  /-- Residual constant or signed wire representing every source wire. -/
  values : Wire (n + 1) g → ResidualValue n gateCount
  /-- Every represented source wire has the correct restricted semantics. -/
  trace_eq : ∀ input sourceWire,
    (values sourceWire).eval result input =
      source.trace interpretation
        ((InputSubstitution.fix selected fixedValue).apply input) sourceWire
  /-- The selected source input is represented by its fixed Boolean value. -/
  selected_eq :
    values (Wire.input selected) = .constant fixedValue
  /-- Partial evaluation follows every chain of zero-cost origin gates. -/
  followsOrigins : ∀ sourceWire,
    values sourceWire =
      (origins source sourceWire).bindWires values
  /-- Charged internal gates deleted during partial evaluation. -/
  deleted : Finset (Fin g)
  /-- Deleted gates account exactly for the charged-cost decrease. -/
  cost_eq : deleted.card + result.cost binaryCost = source.cost binaryCost

namespace ProgramRestriction

/-- Evaluate a source line through a restriction of its preceding program. -/
theorem line_eval
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : ProgramRestriction source selected fixedValue)
    (line : Line signature (n + 1) g)
    (input : Fin n → Bool) :
    line.eval interpretation
        ((InputSubstitution.fix selected fixedValue).apply input)
        (source.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)) =
      interpretation line.op (fun argument =>
        (restriction.values (line.wires argument)).eval restriction.result input) := by
  unfold Line.eval
  congr 1
  funext argument
  exact (restriction.trace_eq input (line.wires argument)).symm

/-- Evaluation of a binary source line from its residual arguments. -/
theorem binaryLine_eval
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (restriction : ProgramRestriction source selected fixedValue)
    (op : BinaryOp)
    (left right : Wire (n + 1) g)
    (input : Fin n → Bool) :
    op.eval
        ((restriction.values left).eval restriction.result input)
        ((restriction.values right).eval restriction.result input) =
      (DeMorgan.binaryLine op left right).eval interpretation
        ((InputSubstitution.fix selected fixedValue).apply input)
        (source.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)) := by
  let line := DeMorgan.binaryLine op left right
  calc
    op.eval
        ((restriction.values left).eval restriction.result input)
        ((restriction.values right).eval restriction.result input) =
        interpretation line.op (fun argument =>
          (restriction.values (line.wires argument)).eval
            restriction.result input) := by
      dsimp only [line]
      exact (DeMorgan.binaryLine_interpretation op left right
        (fun wire =>
          (restriction.values wire).eval restriction.result input)).symm
    _ = line.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (source.eval interpretation
            ((InputSubstitution.fix selected fixedValue).apply input)) :=
      (restriction.line_eval line input).symm

/-- Restriction of the empty program. -/
def empty
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    ProgramRestriction (Program.empty : Program signature (n + 1) 0)
      selected fixedValue where
  gateCount := 0
  result := .empty
  values := Fin.insertNth selected (.constant fixedValue)
    (fun remaining => .wire false (Wire.input remaining))
  trace_eq := by
    intro input sourceWire
    refine Fin.succAboveCases selected ?_ (fun remaining => ?_) sourceWire
    · simp only [Fin.insertNth_apply_same, ResidualValue.eval_constant]
      change fixedValue =
        (Program.empty : Program signature (n + 1) 0).trace interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (Wire.input (g := 0) selected)
      simp [Program.trace]
    · simp only [Fin.insertNth_apply_succAbove,
        ResidualValue.eval_wire_false]
      change
        (Program.empty : Program signature n 0).trace interpretation input
            (Wire.input (g := 0) remaining) =
        (Program.empty : Program signature (n + 1) 0).trace interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (Wire.input (g := 0) (selected.succAbove remaining))
      simp [Program.trace]
  selected_eq := by
    simp [Wire.input]
  followsOrigins := by
    intro sourceWire
    refine Fin.addCases (fun input => ?_)
      (fun impossible => Fin.elim0 impossible) sourceWire
    rw [origins_input, ResidualValue.bindWires_wire_false]
  deleted := ∅
  cost_eq := rfl

/--
Append a free source gate represented by an existing residual value. No
charged gate is added to either the result or the deletion set.
-/
def reuseLast
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (prior : ProgramRestriction source selected fixedValue)
    (line : Line signature (n + 1) g)
    (value : ResidualValue n prior.gateCount)
    (value_eq : ∀ input,
      value.eval prior.result input =
        line.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (source.eval interpretation
            ((InputSubstitution.fix selected fixedValue).apply input)))
    (value_origin_eq :
      value =
        (origins (source.gate line)
          (Wire.gate (Fin.last g))).bindWires
          ((Fin.lastCases value prior.values) :
            Wire (n + 1) (g + 1) → ResidualValue n prior.gateCount))
    (free : binaryCost line.op = 0) :
    ProgramRestriction (source.gate line) selected fixedValue where
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
              ((InputSubstitution.fix selected fixedValue).apply input)
              (source.eval interpretation
                ((InputSubstitution.fix selected fixedValue).apply input)) :=
          value_eq input
        _ = (source.gate line).trace interpretation
              ((InputSubstitution.fix selected fixedValue).apply input)
              (Fin.last ((n + 1) + g)) := by
          symm
          exact Program.trace_gate_last source line interpretation _
    · rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc]
      exact prior.trace_eq input oldWire
  selected_eq := by
    have inputCast :
        (Wire.input (g := g) selected).castSucc =
          Wire.input (g := g + 1) selected := Fin.castSucc_castAdd selected
    rw [← inputCast, Fin.lastCases_castSucc]
    exact prior.selected_eq
  followsOrigins := by
    intro sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last]
      simpa [Wire.gate, Fin.natAdd_last] using value_origin_eq
    · rw [Fin.lastCases_castSucc, origins_gate_castSucc,
        ResidualValue.bindWires_mapWires]
      simpa only [Wire.Renaming.castSucc_apply, Fin.lastCases_castSucc] using
        prior.followsOrigins oldWire
  deleted := prior.deleted.map Fin.castSuccEmb
  cost_eq := by
    simpa [Program.cost_gate, free] using prior.cost_eq

/--
Append a charged source gate whose restricted value is already available. The
new source gate is recorded as deleted.
-/
def deleteLast
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (prior : ProgramRestriction source selected fixedValue)
    (line : Line signature (n + 1) g)
    (value : ResidualValue n prior.gateCount)
    (value_eq : ∀ input,
      value.eval prior.result input =
        line.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (source.eval interpretation
            ((InputSubstitution.fix selected fixedValue).apply input)))
    (charged : binaryCost line.op = 1) :
    ProgramRestriction (source.gate line) selected fixedValue where
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
              ((InputSubstitution.fix selected fixedValue).apply input)
              (source.eval interpretation
                ((InputSubstitution.fix selected fixedValue).apply input)) :=
          value_eq input
        _ = (source.gate line).trace interpretation
              ((InputSubstitution.fix selected fixedValue).apply input)
              (Fin.last ((n + 1) + g)) := by
          symm
          exact Program.trace_gate_last source line interpretation _
    · rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc]
      exact prior.trace_eq input oldWire
  selected_eq := by
    have inputCast :
        (Wire.input (g := g) selected).castSucc =
          Wire.input (g := g + 1) selected := Fin.castSucc_castAdd selected
    rw [← inputCast, Fin.lastCases_castSucc]
    exact prior.selected_eq
  followsOrigins := by
    intro sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last]
      have originLast := origins_gateWire_last_of_charged source line charged
      have bound := congrArg (fun origin => origin.bindWires
        ((Fin.lastCases value prior.values) :
          Wire (n + 1) (g + 1) → ResidualValue n prior.gateCount)) originLast
      simpa [Wire.gate, Fin.natAdd_last] using bound.symm
    · rw [Fin.lastCases_castSucc, origins_gate_castSucc,
        ResidualValue.bindWires_mapWires]
      simpa only [Wire.Renaming.castSucc_apply, Fin.lastCases_castSucc] using
        prior.followsOrigins oldWire
  deleted := insert (Fin.last g) (prior.deleted.map Fin.castSuccEmb)
  cost_eq := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_map,
      Program.cost_gate, charged]
    have priorCost := prior.cost_eq
    omega

/--
Append a charged source gate retained by partial evaluation. The materializer's
wire embedding is propagated to all earlier residual values.
-/
def retainLast
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (prior : ProgramRestriction source selected fixedValue)
    (line : Line signature (n + 1) g)
    {op : BinaryOp}
    {left right : ResidualValue n prior.gateCount}
    (retained : RetainedGate prior.result op left right)
    (output_eq : ∀ input,
      retained.result.trace interpretation input retained.output =
        line.eval interpretation
          ((InputSubstitution.fix selected fixedValue).apply input)
          (source.eval interpretation
            ((InputSubstitution.fix selected fixedValue).apply input)))
    (charged : binaryCost line.op = 1) :
    ProgramRestriction (source.gate line) selected fixedValue where
  gateCount := retained.gateCount
  result := retained.result
  values := Fin.lastCases (.wire false retained.output) (fun oldWire =>
    (prior.values oldWire).mapWires retained.embedding)
  trace_eq := by
    intro input sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last, ResidualValue.eval_wire_false]
      calc
        retained.result.trace interpretation input retained.output =
            line.eval interpretation
              ((InputSubstitution.fix selected fixedValue).apply input)
              (source.eval interpretation
                ((InputSubstitution.fix selected fixedValue).apply input)) :=
          output_eq input
        _ = (source.gate line).trace interpretation
              ((InputSubstitution.fix selected fixedValue).apply input)
              (Fin.last ((n + 1) + g)) := by
          symm
          exact Program.trace_gate_last source line interpretation _
    · rw [Fin.lastCases_castSucc, Program.trace_gate_castSucc,
        ResidualValue.eval_mapWires]
      · exact prior.trace_eq input oldWire
      · intro residualWire
        exact retained.embedding_eq input residualWire
  selected_eq := by
    have inputCast :
        (Wire.input (g := g) selected).castSucc =
          Wire.input (g := g + 1) selected := Fin.castSucc_castAdd selected
    rw [← inputCast, Fin.lastCases_castSucc, prior.selected_eq]
    rfl
  followsOrigins := by
    intro sourceWire
    refine Fin.lastCases ?_ (fun oldWire => ?_) sourceWire
    · rw [Fin.lastCases_last]
      have originLast := origins_gateWire_last_of_charged source line charged
      have bound := congrArg (fun origin => origin.bindWires
        ((Fin.lastCases (.wire false retained.output) (fun oldWire =>
          (prior.values oldWire).mapWires retained.embedding)) :
          Wire (n + 1) (g + 1) → ResidualValue n retained.gateCount)) originLast
      simpa [Wire.gate, Fin.natAdd_last] using bound.symm
    · rw [Fin.lastCases_castSucc, origins_gate_castSucc,
        ResidualValue.bindWires_mapWires]
      rw [prior.followsOrigins, ResidualValue.mapWires_bindWires]
      simp only [Wire.Renaming.castSucc_apply, Fin.lastCases_castSucc]
  deleted := prior.deleted.map Fin.castSuccEmb
  cost_eq := by
    rw [Finset.card_map, retained.cost_eq, Program.cost_gate, charged]
    have priorCost := prior.cost_eq
    omega

/-- Restrict one charged binary gate after its preceding program. -/
noncomputable def appendBinary
    {source : Program signature (n + 1) g}
    {selected : Fin (n + 1)}
    {fixedValue : Bool}
    (prior : ProgramRestriction source selected fixedValue)
    (line : Line signature (n + 1) g)
    (op : BinaryOp)
    (leftWire rightWire : Wire (n + 1) g)
    (line_eq : line = binaryLine op leftWire rightWire) :
    ProgramRestriction (source.gate line) selected fixedValue := by
  let left := prior.values leftWire
  let right := prior.values rightWire
  match simplified : simplifyBinary op left right with
  | some value =>
      exact prior.deleteLast line value (by
        intro input
        rw [simplifyBinary_sound simplified]
        rw [line_eq]
        exact prior.binaryLine_eval op leftWire rightWire input) (by
            rw [line_eq]
            exact binaryLine_cost op leftWire rightWire)
  | none =>
      let retained := retainGate prior.result op left right
      exact prior.retainLast line retained (by
        intro input
        rw [retained.output_eq]
        rw [line_eq]
        exact prior.binaryLine_eval op leftWire rightWire input) (by
            rw [line_eq]
            exact binaryLine_cost op leftWire rightWire)

end ProgramRestriction

/-- Partial-evaluate every gate of a program after fixing one input. -/
noncomputable def restrictProgram
    (selected : Fin (n + 1))
    (fixedValue : Bool) :
    (source : Program signature (n + 1) g) →
      ProgramRestriction source selected fixedValue
  | .empty => ProgramRestriction.empty selected fixedValue
  | @Program.gate _ _ g source line => by
      let prior := restrictProgram selected fixedValue source
      rcases line with ⟨op, wires⟩
      cases op with
      | false =>
          change (Fin 0 → Wire (n + 1) g) at wires
          exact prior.reuseLast ⟨Op.false, wires⟩ (.constant false)
            (fun _ => rfl) (by
              let nextValues : Wire (n + 1) (g + 1) →
                  ResidualValue n prior.gateCount :=
                Fin.lastCases (.constant false) prior.values
              have originEq := origins_gateWire_last_false source wires
              calc
                ResidualValue.constant false =
                    (ResidualValue.constant false).bindWires nextValues := rfl
                _ = (origins (source.gate ⟨Op.false, wires⟩)
                      (Wire.gate (Fin.last g))).bindWires nextValues := by
                    rw [originEq]) rfl
      | true =>
          change (Fin 0 → Wire (n + 1) g) at wires
          exact prior.reuseLast ⟨Op.true, wires⟩ (.constant true)
            (fun _ => rfl) (by
              let nextValues : Wire (n + 1) (g + 1) →
                  ResidualValue n prior.gateCount :=
                Fin.lastCases (.constant true) prior.values
              have originEq := origins_gateWire_last_true source wires
              calc
                ResidualValue.constant true =
                    (ResidualValue.constant true).bindWires nextValues := rfl
                _ = (origins (source.gate ⟨Op.true, wires⟩)
                      (Wire.gate (Fin.last g))).bindWires nextValues := by
                    rw [originEq]) rfl
      | id =>
          change (Fin 1 → Wire (n + 1) g) at wires
          let argument := prior.values (wires ⟨0, by decide⟩)
          exact prior.reuseLast ⟨Op.id, wires⟩ argument (by
            intro input
            rw [prior.line_eval ⟨Op.id, wires⟩ input]
            rfl) (by
              let nextValues : Wire (n + 1) (g + 1) →
                  ResidualValue n prior.gateCount :=
                Fin.lastCases argument prior.values
              have originEq := origins_gateWire_last_id source wires
              calc
                argument =
                    (origins source (wires 0)).bindWires prior.values := by
                  simpa [argument] using prior.followsOrigins (wires 0)
                _ = ((origins source (wires 0)).mapWires
                      Wire.Renaming.castSucc).bindWires nextValues := by
                  rw [ResidualValue.bindWires_mapWires]
                  have valuesEq :
                      (fun wire => nextValues
                        (Wire.Renaming.castSucc wire)) = prior.values := by
                    funext wire
                    simp [nextValues]
                  rw [valuesEq]
                _ = (origins (source.gate ⟨Op.id, wires⟩)
                      (Wire.gate (Fin.last g))).bindWires nextValues := by
                  rw [originEq]) rfl
      | not =>
          change (Fin 1 → Wire (n + 1) g) at wires
          let argument := prior.values (wires ⟨0, by decide⟩)
          exact prior.reuseLast ⟨Op.not, wires⟩ argument.negate (by
            intro input
            rw [ResidualValue.eval_negate,
              prior.line_eval ⟨Op.not, wires⟩ input]
            rfl) (by
              let nextValues : Wire (n + 1) (g + 1) →
                  ResidualValue n prior.gateCount :=
                Fin.lastCases argument.negate prior.values
              have originEq := origins_gateWire_last_not source wires
              calc
                argument.negate =
                    ((origins source (wires 0)).bindWires
                      prior.values).negate := by
                  simpa [argument] using congrArg ResidualValue.negate
                    (prior.followsOrigins (wires 0))
                _ = (((origins source (wires 0)).mapWires
                      Wire.Renaming.castSucc).negate).bindWires nextValues := by
                  rw [ResidualValue.bindWires_negate,
                    ResidualValue.bindWires_mapWires]
                  have valuesEq :
                      (fun wire => nextValues
                        (Wire.Renaming.castSucc wire)) = prior.values := by
                    funext wire
                    simp [nextValues]
                  rw [valuesEq]
                _ = (origins (source.gate ⟨Op.not, wires⟩)
                      (Wire.gate (Fin.last g))).bindWires nextValues := by
                  rw [originEq]) rfl
      | and =>
          let leftWire := wires ⟨0, by decide⟩
          let rightWire := wires ⟨1, by decide⟩
          exact prior.appendBinary ⟨Op.and, wires⟩ .and leftWire rightWire
            (andLine_eq_binaryLine wires)
      | or =>
          let leftWire := wires ⟨0, by decide⟩
          let rightWire := wires ⟨1, by decide⟩
          exact prior.appendBinary ⟨Op.or, wires⟩ .or leftWire rightWire
            (orLine_eq_binaryLine wires)

end DeMorgan
end Algebraic
