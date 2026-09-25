/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan

/-!
# Residual values for De Morgan circuits

Partial evaluation represents a Boolean value by a constant or a possibly
negated wire.  This module contains the local Boolean simplifier and the small
proof-carrying constructions that realize such values inside a De Morgan
program.  Whole-program restriction is deliberately kept in a separate module.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

/-- A Boolean constant or a signed wire in a residual program. -/
inductive ResidualValue (n g : Nat)
  | constant (value : Bool)
  | wire (negated : Bool) (wire : Wire n g)
  deriving DecidableEq

namespace ResidualValue

/-- Evaluate a residual value in a residual program. -/
def eval
    (program : Program signature n g)
    (input : Fin n → Bool) : ResidualValue n g → Bool
  | .constant value => value
  | .wire negated residualWire =>
      if negated then !(program.trace interpretation input residualWire)
      else program.trace interpretation input residualWire

/-- Transport a residual value through a wire map. -/
def mapWires
    (wireMap : Wire n g → Wire n h) :
    ResidualValue n g → ResidualValue n h
  | .constant value => .constant value
  | .wire negated residualWire => .wire negated (wireMap residualWire)

/-- Boolean negation of a residual value. -/
def negate : ResidualValue n g → ResidualValue n g
  | .constant value => .constant (!value)
  | .wire negated residualWire => .wire (!negated) residualWire

@[simp] theorem negate_negate (value : ResidualValue n g) :
    value.negate.negate = value := by
  cases value with
  | constant value => cases value <;> rfl
  | wire negated wire => cases negated <;> rfl

/--
Replace every wire in a residual value by another residual value.  This is the
small substitution operation used to state that partial evaluation follows
zero-cost origin chains.
-/
def bindWires
    (value : ResidualValue n g)
    (values : Wire n g → ResidualValue k h) : ResidualValue k h :=
  match value with
  | .constant value => .constant value
  | .wire negated sourceWire =>
      if negated then (values sourceWire).negate else values sourceWire

@[simp] theorem bindWires_constant
    (values : Wire n g → ResidualValue k h)
    (value : Bool) :
    (constant value : ResidualValue n g).bindWires values = .constant value := rfl

@[simp] theorem bindWires_wire_false
    (values : Wire n g → ResidualValue k h)
    (wire : Wire n g) :
    (ResidualValue.wire false wire).bindWires values = values wire := by
  simp [bindWires]

@[simp] theorem bindWires_wire_true
    (values : Wire n g → ResidualValue k h)
    (wire : Wire n g) :
    (ResidualValue.wire true wire).bindWires values = (values wire).negate := by
  simp [bindWires]

@[simp] theorem mapWires_negate
    (value : ResidualValue n g)
    (wireMap : Wire n g → Wire n h) :
    value.negate.mapWires wireMap = (value.mapWires wireMap).negate := by
  cases value with
  | constant value => cases value <;> rfl
  | wire negated wire => cases negated <;> rfl

theorem mapWires_injective
    {wireMap : Wire n g → Wire n h}
    (injective : Function.Injective wireMap) :
    Function.Injective (fun value : ResidualValue n g =>
      value.mapWires wireMap) := by
  intro left right equal
  cases left with
  | constant leftValue =>
      cases right with
      | constant rightValue => simpa [mapWires] using equal
      | wire rightNegated rightWire => simp [mapWires] at equal
  | wire leftNegated leftWire =>
      cases right with
      | constant rightValue => simp [mapWires] at equal
      | wire rightNegated rightWire =>
          simp only [mapWires] at equal
          injection equal with signs wires
          have sourceWires := injective wires
          subst rightNegated
          subst rightWire
          rfl

@[simp] theorem bindWires_negate
    (value : ResidualValue n g)
    (values : Wire n g → ResidualValue k h) :
    value.negate.bindWires values = (value.bindWires values).negate := by
  cases value with
  | constant value => cases value <;> simp [negate, bindWires]
  | wire negated wire =>
      cases negated with
      | false => rfl
      | true => exact (negate_negate (values wire)).symm

@[simp] theorem mapWires_bindWires
    (value : ResidualValue n g)
    (values : Wire n g → ResidualValue k h)
    (wireMap : Wire k h → Wire k l) :
    (value.bindWires values).mapWires wireMap =
      value.bindWires (fun wire => (values wire).mapWires wireMap) := by
  cases value with
  | constant value => rfl
  | wire negated wire =>
      cases negated with
      | false => rfl
      | true => exact mapWires_negate (values wire) wireMap

@[simp] theorem bindWires_mapWires
    (value : ResidualValue n g)
    (wireMap : Wire n g → Wire n h)
    (values : Wire n h → ResidualValue k l) :
    (value.mapWires wireMap).bindWires values =
      value.bindWires (fun wire => values (wireMap wire)) := by
  cases value with
  | constant value => rfl
  | wire negated wire => cases negated <;> rfl

@[simp] theorem eval_constant
    (program : Program signature n g)
    (input : Fin n → Bool)
    (value : Bool) :
    (constant value : ResidualValue n g).eval program input = value := rfl

@[simp] theorem eval_wire_false
    (program : Program signature n g)
    (input : Fin n → Bool)
    (residualWire : Wire n g) :
    (ResidualValue.wire false residualWire).eval program input =
      program.trace interpretation input residualWire := rfl

@[simp] theorem eval_wire_true
    (program : Program signature n g)
    (input : Fin n → Bool)
    (residualWire : Wire n g) :
    (ResidualValue.wire true residualWire).eval program input =
      !(program.trace interpretation input residualWire) := rfl

@[simp] theorem eval_negate
    (value : ResidualValue n g)
    (program : Program signature n g)
    (input : Fin n → Bool) :
    value.negate.eval program input = !value.eval program input := by
  cases value with
  | constant value => cases value <;> rfl
  | wire negated residualWire =>
      cases negated <;> simp [negate, eval]

end ResidualValue

/-- The two charged De Morgan connectives. -/
inductive BinaryOp
  | and
  | or
  deriving DecidableEq

namespace BinaryOp

/-- Operation symbol corresponding to a charged connective. -/
def operation : BinaryOp → Op
  | .and => .and
  | .or => .or

/-- Boolean semantics of a charged connective. -/
def eval : BinaryOp → Bool → Bool → Bool
  | .and => (fun left right => left && right)
  | .or => (fun left right => left || right)

/-- The value which makes a binary operation independent of its other input. -/
def absorbing : BinaryOp → Bool
  | .and => false
  | .or => true

/-- Source-input value making a possibly-negated literal absorbing. -/
def inputForSignedAbsorbing (op : BinaryOp) (negated : Bool) : Bool :=
  if negated then !op.absorbing else op.absorbing

@[simp] theorem signed_inputForSignedAbsorbing
    (op : BinaryOp)
    (negated : Bool) :
    (if negated then !op.inputForSignedAbsorbing negated
      else op.inputForSignedAbsorbing negated) = op.absorbing := by
  cases op <;> cases negated <;> rfl

@[simp] theorem eval_absorbing_right
    (op : BinaryOp)
    (left : Bool) :
    op.eval left op.absorbing = op.absorbing := by
  cases op <;> cases left <;> rfl

@[simp] theorem cost_operation (op : BinaryOp) :
    binaryCost op.operation = 1 := by
  cases op <;> rfl

end BinaryOp

/--
Simplify a binary De Morgan gate. `none` means both signed inputs are genuinely
needed and the charged gate must be retained.
-/
def simplifyBinary
    (op : BinaryOp)
    (left right : ResidualValue n g) : Option (ResidualValue n g) :=
  match op, left, right with
  | .and, .constant false, _ => some (.constant false)
  | .and, _, .constant false => some (.constant false)
  | .and, .constant true, right => some right
  | .and, left, .constant true => some left
  | .or, .constant true, _ => some (.constant true)
  | .or, _, .constant true => some (.constant true)
  | .or, .constant false, right => some right
  | .or, left, .constant false => some left
  | .and, .wire leftNegated leftWire, .wire rightNegated rightWire =>
      if leftWire = rightWire then
        if leftNegated = rightNegated then
          some (.wire leftNegated leftWire)
        else
          some (.constant false)
      else none
  | .or, .wire leftNegated leftWire, .wire rightNegated rightWire =>
      if leftWire = rightWire then
        if leftNegated = rightNegated then
          some (.wire leftNegated leftWire)
        else
          some (.constant true)
      else none

/-- A false argument annihilates an AND gate, in either input position. -/
theorem simplifyBinary_and_of_argument_false
    (values : Fin 2 → ResidualValue n g)
    (argument : Fin 2)
    (constant : values argument = .constant false) :
    simplifyBinary .and (values 0) (values 1) =
      some (.constant false) := by
  revert constant
  refine Fin.cases ?_ (fun remaining => ?_) argument
  · intro constant
    rw [constant]
    rfl
  · intro constant
    have remaining_eq : remaining = 0 := Fin.eq_zero remaining
    subst remaining
    have rightConstant : values 1 = .constant false := by simpa using constant
    rw [rightConstant]
    cases values 0 with
    | constant value => cases value <;> rfl
    | wire negated wire => rfl

/-- A true argument annihilates an OR gate, in either input position. -/
theorem simplifyBinary_or_of_argument_true
    (values : Fin 2 → ResidualValue n g)
    (argument : Fin 2)
    (constant : values argument = .constant true) :
    simplifyBinary .or (values 0) (values 1) =
      some (.constant true) := by
  revert constant
  refine Fin.cases ?_ (fun remaining => ?_) argument
  · intro constant
    rw [constant]
    rfl
  · intro constant
    have remaining_eq : remaining = 0 := Fin.eq_zero remaining
    subst remaining
    have rightConstant : values 1 = .constant true := by simpa using constant
    rw [rightConstant]
    cases values 0 with
    | constant value => cases value <;> rfl
    | wire negated wire => rfl

/-- Any constant argument makes a binary De Morgan gate simplifiable. -/
theorem simplifyBinary_of_argument_constant
    (op : BinaryOp)
    (values : Fin 2 → ResidualValue n g)
    (argument : Fin 2)
    (value : Bool)
    (constant : values argument = .constant value) :
    ∃ result, simplifyBinary op (values 0) (values 1) = some result := by
  cases op <;> cases value
  · exact ⟨.constant false,
      simplifyBinary_and_of_argument_false values argument constant⟩
  · revert constant
    refine Fin.cases ?_ (fun remaining => ?_) argument
    · intro constant
      rw [constant]
      cases values 1 with
      | constant right => cases right <;> exact ⟨_, rfl⟩
      | wire negated wire => exact ⟨_, rfl⟩
    · intro constant
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      have rightConstant : values 1 = .constant true := by
        simpa using constant
      rw [rightConstant]
      exact ⟨values 0, by
        cases values 0 with
        | constant left => cases left <;> rfl
        | wire negated wire => rfl⟩
  · revert constant
    refine Fin.cases ?_ (fun remaining => ?_) argument
    · intro constant
      rw [constant]
      cases values 1 with
      | constant right => cases right <;> exact ⟨_, rfl⟩
      | wire negated wire => exact ⟨_, rfl⟩
    · intro constant
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      have rightConstant : values 1 = .constant false := by
        simpa using constant
      rw [rightConstant]
      exact ⟨values 0, by
        cases values 0 with
        | constant left => cases left <;> rfl
        | wire negated wire => rfl⟩
  · exact ⟨.constant true,
      simplifyBinary_or_of_argument_true values argument constant⟩

/-- Two signed forms of one residual value always make a binary gate simplify. -/
theorem simplifyBinary_of_common_value
    (op : BinaryOp)
    (value : ResidualValue n g)
    (leftNegated rightNegated : Bool) :
    ∃ result,
      simplifyBinary op
          (if leftNegated then value.negate else value)
          (if rightNegated then value.negate else value) = some result := by
  cases op <;> cases value with
  | constant value =>
      cases value <;> cases leftNegated <;> cases rightNegated <;>
        simp [ResidualValue.negate, simplifyBinary]
  | wire negated wire =>
      cases negated <;> cases leftNegated <;> cases rightNegated <;>
        simp [ResidualValue.negate, simplifyBinary]

/-- `simplifyBinary` preserves the value of a gate whenever it succeeds. -/
theorem simplifyBinary_sound
    {op : BinaryOp}
    {left right result : ResidualValue n g}
    (simplifies : simplifyBinary op left right = some result)
    (program : Program signature n g)
    (input : Fin n → Bool) :
    result.eval program input =
      op.eval (left.eval program input) (right.eval program input) := by
  symm at simplifies
  cases op <;> cases left with
  | constant leftValue =>
      cases leftValue <;> cases right with
      | constant rightValue =>
          cases rightValue <;>
            simp_all [simplifyBinary, ResidualValue.eval, BinaryOp.eval]
      | wire rightNegated rightWire =>
          cases rightNegated <;>
            simp_all [simplifyBinary, ResidualValue.eval, BinaryOp.eval]
  | wire leftNegated leftWire =>
      cases leftNegated <;> cases right with
      | constant rightValue =>
          cases rightValue <;>
            simp_all [simplifyBinary, ResidualValue.eval, BinaryOp.eval]
      | wire rightNegated rightWire =>
          cases rightNegated <;>
            by_cases sameWire : leftWire = rightWire <;>
              simp_all [simplifyBinary, ResidualValue.eval, BinaryOp.eval]

/-! ## Materialization -/

/-- A free constant line. -/
def constantLine (value : Bool) : Line signature n g :=
  match value with
  | false => { op := .false, wires := Fin.elim0 }
  | true => { op := .true, wires := Fin.elim0 }

/-- A free identity line. -/
def identityLine (sourceWire : Wire n g) : Line signature n g :=
  { op := .id
    wires := fun _ => sourceWire }

/-- A free negation line. -/
def notLine (sourceWire : Wire n g) : Line signature n g :=
  { op := .not
    wires := fun _ => sourceWire }

/-- A charged binary line. -/
def binaryLine
    (op : BinaryOp)
    (left right : Wire n g) : Line signature n g :=
  match op with
  | .and => { op := .and, wires := Fin.cases left (fun _ => right) }
  | .or => { op := .or, wires := Fin.cases left (fun _ => right) }

/-- Mapping the wires of a binary line maps its two named arguments. -/
theorem binaryLine_mapWires
    (op : BinaryOp)
    (left right : Wire n g)
    (wireMap : Wire n g → Wire n h) :
    (binaryLine op left right).mapWires wireMap =
      binaryLine op (wireMap left) (wireMap right) := by
  cases op with
  | and =>
      apply congrArg (fun wires : Fin 2 → Wire n h =>
        (⟨Op.and, wires⟩ : Line signature n h))
      funext argument
      refine Fin.cases rfl (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      rfl
  | or =>
      apply congrArg (fun wires : Fin 2 → Wire n h =>
        (⟨Op.or, wires⟩ : Line signature n h))
      funext argument
      refine Fin.cases rfl (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      rfl

/-- Every argument wire of a binary line is one of its two named inputs. -/
theorem binaryLine_wire_eq_left_or_right
    (op : BinaryOp)
    (left right : Wire n g)
    (argument : Fin (signature.Arity (binaryLine op left right).op)) :
    (binaryLine op left right).wires argument = left ∨
      (binaryLine op left right).wires argument = right := by
  cases op with
  | and =>
      change Fin 2 at argument
      refine Fin.cases (Or.inl rfl) (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      exact Or.inr rfl
  | or =>
      change Fin 2 at argument
      refine Fin.cases (Or.inl rfl) (fun remaining => ?_) argument
      have remaining_eq : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      exact Or.inr rfl
/-- Every binary AND line is determined by its two arguments. -/
theorem andLine_eq_binaryLine
    (wires : Fin 2 → Wire n g) :
    (⟨Op.and, wires⟩ : Line signature n g) =
      binaryLine .and (wires 0) (wires 1) := by
  have wires_eq : wires = Fin.cases (wires 0) (fun _ => wires 1) := by
    funext argument
    refine Fin.cases ?_ (fun remaining => ?_) argument
    · rfl
    · have : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      rfl
  rw [wires_eq]
  rfl

/-- Every binary OR line is determined by its two arguments. -/
theorem orLine_eq_binaryLine
    (wires : Fin 2 → Wire n g) :
    (⟨Op.or, wires⟩ : Line signature n g) =
      binaryLine .or (wires 0) (wires 1) := by
  have wires_eq : wires = Fin.cases (wires 0) (fun _ => wires 1) := by
    funext argument
    refine Fin.cases ?_ (fun remaining => ?_) argument
    · rfl
    · have : remaining = 0 := Fin.eq_zero remaining
      subst remaining
      rfl
  rw [wires_eq]
  rfl

@[simp] theorem constantLine_cost (value : Bool) :
    binaryCost (constantLine (n := n) (g := g) value).op = 0 := by
  cases value <;> rfl

@[simp] theorem identityLine_cost (sourceWire : Wire n g) :
    binaryCost (identityLine sourceWire).op = 0 := rfl

@[simp] theorem notLine_cost (sourceWire : Wire n g) :
    binaryCost (notLine sourceWire).op = 0 := rfl

@[simp] theorem binaryLine_cost
    (op : BinaryOp)
    (left right : Wire n g) :
    binaryCost (binaryLine op left right).op = 1 := by
  cases op <;> rfl

@[simp] theorem binaryLine_eval
    (op : BinaryOp)
    (left right : Wire n g)
    (program : Program signature n g)
    (input : Fin n → Bool) :
    (binaryLine op left right).eval interpretation input
        (program.eval interpretation input) =
      op.eval (program.trace interpretation input left)
        (program.trace interpretation input right) := by
  cases op <;> rfl

/-- Applying a binary line to an arbitrary wire valuation reads its two inputs. -/
@[simp] theorem binaryLine_interpretation
    (op : BinaryOp)
    (left right : Wire n g)
    (values : Wire n g → Bool) :
    interpretation (binaryLine op left right).op (fun argument =>
      values ((binaryLine op left right).wires argument)) =
        op.eval (values left) (values right) := by
  cases op <;> rfl

theorem ResidualValue.eval_mapWires
    (value : ResidualValue n g)
    (wireMap : Wire.Renaming n g h)
    (source : Program signature n g)
    (result : Program signature n h)
    (input : Fin n → Bool)
    (preserves : ∀ sourceWire,
      result.trace interpretation input (wireMap sourceWire) =
        source.trace interpretation input sourceWire) :
    (value.mapWires wireMap).eval result input = value.eval source input := by
  cases value with
  | constant value => rfl
  | wire negated sourceWire =>
      cases negated <;> simp [ResidualValue.mapWires, ResidualValue.eval,
        preserves sourceWire]

/--
Materialize a residual value as a wire, adding only zero-cost gates and
embedding every old wire into the extended program.
-/
structure Materialization
    (program : Program signature n g)
    (value : ResidualValue n g) where
  /-- Gate count of the extended program. -/
  gateCount : Nat
  /-- Extended program. -/
  result : Program signature n gateCount
  /-- Inclusion of all old wires. -/
  embedding : Wire.Renaming n g gateCount
  /-- Wire carrying the materialized value. -/
  output : Wire n gateCount
  /-- The embedding preserves every old wire. -/
  embedding_eq : ∀ input sourceWire,
    result.trace interpretation input (embedding sourceWire) =
      program.trace interpretation input sourceWire
  /-- The output wire realizes `value`. -/
  output_eq : ∀ input,
    result.trace interpretation input output = value.eval program input
  /-- Materialization has zero charged cost. -/
  cost_eq : result.cost binaryCost = program.cost binaryCost

/-- Materialize a constant or signed wire using at most one free gate. -/
def materialize
    (program : Program signature n g)
    (value : ResidualValue n g) : Materialization program value := by
  cases value with
  | constant value =>
      let line := constantLine (n := n) (g := g) value
      exact
        { gateCount := g + 1
          result := program.gate line
          embedding := Wire.Renaming.castSucc
          output := Fin.last (n + g)
          embedding_eq := by
            intro input sourceWire
            simpa only [Wire.Renaming.castSucc_apply] using
              Program.trace_gate_castSucc
                program line interpretation input sourceWire
          output_eq := by
            intro input
            rw [Program.trace_gate_last]
            cases value <;> rfl
          cost_eq := by
            simp [line] }
  | wire negated sourceWire =>
      cases negated with
      | false =>
          exact
            { gateCount := g
              result := program
              embedding := Wire.Renaming.id
              output := sourceWire
              embedding_eq := by
                intro input oldWire
                rw [Wire.Renaming.id_apply]
              output_eq := fun _ => rfl
              cost_eq := rfl }
      | true =>
          let line := notLine sourceWire
          exact
            { gateCount := g + 1
              result := program.gate line
              embedding := Wire.Renaming.castSucc
              output := Fin.last (n + g)
              embedding_eq := by
                intro input oldWire
                simpa only [Wire.Renaming.castSucc_apply] using
                  Program.trace_gate_castSucc
                    program line interpretation input oldWire
              output_eq := by
                intro input
                rw [Program.trace_gate_last]
                rfl
              cost_eq := by simp [line] }

/--
Retain a genuinely binary gate after materializing its signed arguments. The
extension adds exactly one unit of charged cost.
-/
structure RetainedGate
    (program : Program signature n g)
    (op : BinaryOp)
    (left right : ResidualValue n g) where
  /-- Gate count of the extended program. -/
  gateCount : Nat
  /-- Extended program ending in the retained charged gate. -/
  result : Program signature n gateCount
  /-- Inclusion of all old wires. -/
  embedding : Wire.Renaming n g gateCount
  /-- Output of the retained gate. -/
  output : Wire n gateCount
  /-- The embedding preserves every old wire. -/
  embedding_eq : ∀ input sourceWire,
    result.trace interpretation input (embedding sourceWire) =
      program.trace interpretation input sourceWire
  /-- The output has the requested binary semantics. -/
  output_eq : ∀ input,
    result.trace interpretation input output =
      op.eval (left.eval program input) (right.eval program input)
  /-- Retaining the gate adds exactly one unit of charged cost. -/
  cost_eq : result.cost binaryCost = program.cost binaryCost + 1

/-- Materialize two signed arguments and append their charged gate. -/
def retainGate
    (program : Program signature n g)
    (op : BinaryOp)
    (left right : ResidualValue n g) :
    RetainedGate program op left right := by
  let first := materialize program left
  let mappedRight := right.mapWires first.embedding
  let second := materialize first.result mappedRight
  let leftWire := second.embedding first.output
  let line := binaryLine op leftWire second.output
  let result := second.result.gate line
  exact
    { gateCount := second.gateCount + 1
      result := result
      embedding := Wire.Renaming.castSucc.comp
        (second.embedding.comp first.embedding)
      output := Fin.last (n + second.gateCount)
      embedding_eq := by
        intro input sourceWire
        rw [Wire.Renaming.comp_apply, Wire.Renaming.comp_apply,
          Wire.Renaming.castSucc_apply]
        rw [Program.trace_gate_castSucc]
        rw [second.embedding_eq, first.embedding_eq]
      output_eq := by
        intro input
        rw [Program.trace_gate_last]
        rw [binaryLine_eval]
        change op.eval
          (second.result.trace interpretation input
            (second.embedding first.output))
          (second.result.trace interpretation input second.output) = _
        rw [second.embedding_eq, second.output_eq, first.output_eq]
        have mappedRightEq := ResidualValue.eval_mapWires right
          first.embedding program first.result input
          (fun sourceWire => first.embedding_eq input sourceWire)
        rw [mappedRightEq]
      cost_eq := by
        simp only [result, Program.cost_gate]
        rw [second.cost_eq, first.cost_eq]
        simp [line] }

end DeMorgan
end Algebraic
