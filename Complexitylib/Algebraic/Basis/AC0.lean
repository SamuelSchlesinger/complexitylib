/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.CircuitFamily

/-!
# The unbounded-fan-in AC0 basis

This module models the source convention used by Hastad's small-depth lower
bound. AND and OR gates have arbitrary finite fan-in. NOT is explicit in the
generic circuit syntax, but the source-facing cost charges only AND/OR gates
and the source-facing logical depth gives NOT zero delay. The checked class
presentation requires every NOT to read an original input. A stronger
`Circuit.NormalForm` predicate additionally records alternation of adjacent
AND/OR gates.
-/

@[expose] public section

namespace Algebraic
namespace AC0

/-- Operations in the arbitrary-fan-in AND/OR/NOT basis. Zero-ary AND and OR
serve as the Boolean constants true and false. -/
inductive Op
  | not
  | and (arity : Nat)
  | or (arity : Nat)
  deriving DecidableEq

/-- Arity of an AC0 operation. -/
@[reducible] def arity : Op -> Nat
  | .not => 1
  | .and n | .or n => n

/-- Signature of the arbitrary-fan-in Boolean basis. -/
abbrev signature : Signature where
  Op := Op
  Arity := arity

/-- Standard Boolean semantics. Empty conjunction is true and empty
disjunction is false. -/
def interpretation : Interpretation signature Bool
  | .not, input => !(input 0)
  | .and _, input => decide (forall k, input k = true)
  | .or _, input => decide (Exists fun k => input k = true)

@[simp] theorem interpretation_not
    (input : Fin 1 -> Bool) :
    interpretation .not input = !(input 0) := rfl

@[simp] theorem interpretation_and_eq_true
    (input : Fin n -> Bool) :
    interpretation (.and n) input = true <->
      forall k, input k = true := by
  rw [interpretation, decide_eq_true_eq]

@[simp] theorem interpretation_or_eq_true
    (input : Fin n -> Bool) :
    interpretation (.or n) input = true <->
      Exists fun k => input k = true := by
  rw [interpretation, decide_eq_true_eq]

@[simp] theorem interpretation_and_zero :
    interpretation (.and 0) Fin.elim0 = true := by
  simp

@[simp] theorem interpretation_or_zero :
    interpretation (.or 0) Fin.elim0 = false := by
  simp [interpretation]

/-- Hastad's size convention: count AND and OR gates, not input negations. -/
def andOrCost : OperationCost signature
  | .not => 0
  | .and _ | .or _ => 1

@[simp] theorem andOrCost_not : andOrCost .not = 0 := rfl
@[simp] theorem andOrCost_and (n : Nat) : andOrCost (.and n) = 1 := rfl
@[simp] theorem andOrCost_or (n : Nat) : andOrCost (.or n) = 1 := rfl

/-- The two connectives whose adjacent levels are merged in normal form. -/
inductive Connective
  | and
  | or
  deriving DecidableEq

/-- Forget fan-in while retaining whether an operation is AND or OR. -/
def Op.connective : Op -> Option Connective
  | .not => none
  | .and _ => some .and
  | .or _ => some .or

namespace Line

/-- A NOT line is a source literal precisely when it reads an original input. -/
def NegationAtInput : Algebraic.Line signature n g -> Prop
  | ⟨.not, wires⟩ => Exists fun input => wires 0 = Wire.input input
  | ⟨.and _, _⟩ | ⟨.or _, _⟩ => True

/-- Every direct AND/OR predecessor has the opposite connective. NOT lines
are treated as input literals and impose no connective condition. -/
def AlternatesAfter
    (program : Algebraic.Program signature n g)
    (line : Algebraic.Line signature n g) : Prop :=
  forall argument source,
    line.wires argument = Wire.gate source ->
      match line.op.connective, (program.lines source).op.connective with
      | some outer, some inner => outer ≠ inner
      | _, _ => True

end Line

namespace Program

/-- Every NOT gate in a program reads an original input. -/
def NegationsAtInputs :
    (program : Algebraic.Program signature n g) -> Prop
  | .empty => True
  | .gate program line =>
      NegationsAtInputs program ∧ Line.NegationAtInput line

/-- No AND gate directly reads an AND gate and no OR gate directly reads an OR
gate. -/
def Alternating :
    (program : Algebraic.Program signature n g) -> Prop
  | .empty => True
  | .gate program line =>
      Alternating program ∧ Line.AlternatesAfter program line

end Program

/-- Arrival-time semantics for source gate levels. Input negations are
literal annotations and therefore have zero delay; AND and OR add one level. -/
def logicalDepthInterpretation : Interpretation signature Nat
  | .not, input => input 0
  | .and n, input | .or n, input =>
      Nat.succ <| Fin.foldl n
        (fun depth argument => max depth (input argument)) 0

private theorem foldl_max_zero (n : Nat) :
    Fin.foldl n (fun depth (_ : Fin n) => max depth 0) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [Fin.foldl_succ]
      simpa using inductionHypothesis

@[simp] theorem logicalDepthInterpretation_not_zero :
    logicalDepthInterpretation .not (fun _ => 0) = 0 := rfl

@[simp] theorem logicalDepthInterpretation_and_zero (n : Nat) :
    logicalDepthInterpretation (.and n) (fun _ => 0) = 1 := by
  change Nat.succ
    (Fin.foldl n (fun depth (_ : Fin n) => max depth 0) 0) = 1
  rw [foldl_max_zero]

@[simp] theorem logicalDepthInterpretation_or_zero (n : Nat) :
    logicalDepthInterpretation (.or n) (fun _ => 0) = 1 := by
  change Nat.succ
    (Fin.foldl n (fun depth (_ : Fin n) => max depth 0) 0) = 1
  rw [foldl_max_zero]

namespace Circuit

/-- Every NOT gate in the circuit is an input literal. -/
def NegationsAtInputs
    (circuit : Algebraic.Circuit signature n g m) : Prop :=
  Program.NegationsAtInputs circuit.program

/-- Logical depth of each designated output in Hastad's convention. -/
def logicalOutputDepths
    (circuit : Algebraic.Circuit signature n g m) : Fin m -> Nat :=
  circuit.eval logicalDepthInterpretation (fun _ => 0)

/-- Maximum number of AND/OR levels on a designated input-output path. -/
def logicalDepth
    (circuit : Algebraic.Circuit signature n g m) : Nat :=
  Fin.foldl m
    (fun depth output => max depth (logicalOutputDepths circuit output)) 0

/-- A one-output circuit's logical depth is the depth of its unique output. -/
theorem logicalDepth_one_output
    (circuit : Algebraic.Circuit signature n g 1) :
    logicalDepth circuit = logicalOutputDepths circuit 0 := by
  simp [logicalDepth, Fin.foldl_succ]

/-- Source-facing normal form: negations are input literals and consecutive
AND/OR gates alternate. -/
def NormalForm (circuit : Algebraic.Circuit signature n g m) : Prop :=
  NegationsAtInputs circuit ∧
    Program.Alternating circuit.program

/-- Strong normal form in particular places every negation at an input. -/
theorem NormalForm.negationsAtInputs
    {circuit : Algebraic.Circuit signature n g m}
    (normal : NormalForm circuit) :
    NegationsAtInputs circuit :=
  normal.1

end Circuit

namespace Family

/-- Logical depth as a resource function of a nonuniform family. -/
def logicalDepth
    (family : Algebraic.Circuit.Family signature m)
    (n : Nat) : Nat :=
  Circuit.logicalDepth (family.circuit n)

/-- Every member of the family is in the source-facing normal form. -/
def NormalForm
    (family : Algebraic.Circuit.Family signature m) : Prop :=
  forall n, Circuit.NormalForm (family.circuit n)

/-- Every family member has only input-level negations. -/
def NegationsAtInputs
    (family : Algebraic.Circuit.Family signature m) : Prop :=
  forall n, Circuit.NegationsAtInputs (family.circuit n)

/-- Strong family normal form implies the input-negation invariant used by
the switching-lemma development. -/
theorem NormalForm.negationsAtInputs
    {family : Algebraic.Circuit.Family signature m}
    (normal : NormalForm family) :
    NegationsAtInputs family :=
  fun n => (normal n).negationsAtInputs

/-- One source-level depth bound works at every input width. -/
def HasConstantLogicalDepth
    (family : Algebraic.Circuit.Family signature m) : Prop :=
  Algebraic.Circuit.Resource.ConstantlyBounded (logicalDepth family)

/-- An unrestricted small-depth family has polynomial AND/OR cost and constant
logical depth. Internal NOT gates are allowed in this raw presentation. -/
def IsRawSmallDepth
    (family : Algebraic.Circuit.Family signature 1) : Prop :=
  family.HasPolynomialCost andOrCost ∧
    HasConstantLogicalDepth family

/-- A checked AC0 family has polynomial AND/OR cost, constant logical depth,
and only input-level negations. Alternation is available separately through
`Family.NormalForm` but is not needed for the class definition. -/
def IsSmallDepth
    (family : Algebraic.Circuit.Family signature 1) : Prop :=
  family.HasPolynomialCost andOrCost ∧
    HasConstantLogicalDepth family ∧
    NegationsAtInputs family

/-- Forgetting the input-negation invariant yields a raw small-depth family. -/
theorem IsSmallDepth.raw
    {family : Algebraic.Circuit.Family signature 1}
    (smallDepth : IsSmallDepth family) :
    IsRawSmallDepth family :=
  ⟨smallDepth.1, smallDepth.2.1⟩

end Family

/-- Nonuniform AC0 computability of a one-output Boolean target family. -/
def Computable (target : Target.Family Bool 1) : Prop :=
  Exists fun family : Algebraic.Circuit.Family signature 1 =>
    family.Computes interpretation target ∧ Family.IsSmallDepth family

/-- Raw nonuniform AC0 computability, allowing NOT gates at arbitrary internal
wires. Dual-rail normalization proves this presentation equivalent to
`Computable`. -/
def RawComputable (target : Target.Family Bool 1) : Prop :=
  Exists fun family : Algebraic.Circuit.Family signature 1 =>
    family.Computes interpretation target ∧
      Family.IsRawSmallDepth family

end AC0
end Algebraic
