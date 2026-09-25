/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Basis.DeMorgan
public import Complexitylib.Algebraic.Parallel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# De Morgan expressions compiled to circuits

This is a small tree language for Boolean formulas over the manuscript's
actual basis.  Unlike the Boolean-ring compiler, it emits `NOT`, `AND`, and
`OR` directly, which is useful for zero tests, comparisons, selectors, and
sorting-network records.  Constants are represented by nullary gates but are
free under `DeMorgan.standardCost`.
-/

@[expose] public section

namespace Algebraic
namespace DeMorgan

open scoped BigOperators

/-- Tree-shaped expressions over the De Morgan basis. -/
inductive Expression (n : Nat)
  | input (index : Fin n)
  | constant (value : Bool)
  | not (child : Expression n)
  | and (left right : Expression n)
  | or (left right : Expression n)

namespace Expression

/-- Number of program gates emitted by tree compilation. -/
@[reducible] def gateCount : Expression n -> Nat
  | .input _ => 0
  | .constant _ => 1
  | .not child => child.gateCount + 1
  | .and left right | .or left right =>
      left.gateCount + right.gateCount + 1

/-- Standard charged cost: constants and inputs are free, and each logical
operation costs one. -/
@[reducible] def standardCost : Expression n -> Nat
  | .input _ | .constant _ => 0
  | .not child => child.standardCost + 1
  | .and left right | .or left right =>
      left.standardCost + right.standardCost + 1

/-- Direct Boolean semantics. -/
def eval (input : Fin n -> Bool) : Expression n -> Bool
  | .input index => input index
  | .constant value => value
  | .not child => !(child.eval input)
  | .and left right => left.eval input && right.eval input
  | .or left right => left.eval input || right.eval input

/-- Rename the input coordinates of an expression. -/
def mapInputs
    (inputMap : Fin sourceInputs -> Fin targetInputs) :
    Expression sourceInputs -> Expression targetInputs
  | .input index => .input (inputMap index)
  | .constant value => .constant value
  | .not child => .not (mapInputs inputMap child)
  | .and left right =>
      .and (mapInputs inputMap left) (mapInputs inputMap right)
  | .or left right =>
      .or (mapInputs inputMap left) (mapInputs inputMap right)

@[simp] theorem mapInputs_eval
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : Expression sourceInputs)
    (input : Fin targetInputs -> Bool) :
    (expression.mapInputs inputMap).eval input =
      expression.eval (input ∘ inputMap) := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [mapInputs, eval, inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [mapInputs, eval, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [mapInputs, eval, leftIH, rightIH]

@[simp] theorem mapInputs_gateCount
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : Expression sourceInputs) :
    (expression.mapInputs inputMap).gateCount = expression.gateCount := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [mapInputs, gateCount, inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [mapInputs, gateCount, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [mapInputs, gateCount, leftIH, rightIH]

@[simp] theorem mapInputs_standardCost
    (inputMap : Fin sourceInputs -> Fin targetInputs)
    (expression : Expression sourceInputs) :
    (expression.mapInputs inputMap).standardCost = expression.standardCost := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [mapInputs, standardCost, inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [mapInputs, standardCost, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [mapInputs, standardCost, leftIH, rightIH]

/-- One free constant gate. -/
def constantCircuit (value : Bool) (n : Nat) :
    Circuit signature n 1 where
  program := (Program.empty : Program signature n 0).gate
    { op := if value then .true else .false
      wires := fun argument => Fin.elim0
        (Fin.cast (by cases value <;> rfl) argument) }
  outputs := fun _ => Wire.gate (Fin.last 0)

/-- One direct `NOT` gate. -/
def notCircuit : Circuit signature 1 1 where
  program := (Program.empty : Program signature 1 0).gate
    { op := .not
      wires := fun _ => Wire.input 0 }
  outputs := fun _ => Wire.gate (Fin.last 0)

/-- One direct `AND` gate. -/
def andCircuit : Circuit signature 2 1 where
  program := (Program.empty : Program signature 2 0).gate
    { op := .and
      wires := fun input => Wire.input input }
  outputs := fun _ => Wire.gate (Fin.last 0)

/-- One direct `OR` gate. -/
def orCircuit : Circuit signature 2 1 where
  program := (Program.empty : Program signature 2 0).gate
    { op := .or
      wires := fun input => Wire.input input }
  outputs := fun _ => Wire.gate (Fin.last 0)

@[simp] private theorem constantCircuit_eval
    (value : Bool)
    (input : Fin n -> Bool) :
    (constantCircuit value n).eval interpretation input 0 = value := by
  unfold Circuit.eval constantCircuit
  simp only [Function.comp_apply]
  simp only [Program.trace_gateWire, Program.gateFunction_gate_last]
  cases value <;> rfl

@[simp] private theorem notCircuit_eval
    (input : Fin 1 -> Bool) :
    notCircuit.eval interpretation input 0 = !(input 0) := by
  unfold Circuit.eval notCircuit
  simp only [Function.comp_apply]
  simp only [Program.trace_gateWire, Program.gateFunction_gate_last]
  rfl

@[simp] private theorem andCircuit_eval
    (input : Fin 2 -> Bool) :
    andCircuit.eval interpretation input 0 = (input 0 && input 1) := by
  unfold Circuit.eval andCircuit
  simp only [Function.comp_apply]
  simp only [Program.trace_gateWire, Program.gateFunction_gate_last]
  rfl

@[simp] private theorem orCircuit_eval
    (input : Fin 2 -> Bool) :
    orCircuit.eval interpretation input 0 = (input 0 || input 1) := by
  unfold Circuit.eval orCircuit
  simp only [Function.comp_apply]
  simp only [Program.trace_gateWire, Program.gateFunction_gate_last]
  rfl

@[simp] private theorem constantCircuit_cost
    (value : Bool) :
    (constantCircuit value n).cost DeMorgan.standardCost = 0 := by
  cases value <;> rfl

@[simp] private theorem notCircuit_cost :
    notCircuit.cost DeMorgan.standardCost = 1 := rfl

@[simp] private theorem andCircuit_cost :
    andCircuit.cost DeMorgan.standardCost = 1 := rfl

@[simp] private theorem orCircuit_cost :
    orCircuit.cost DeMorgan.standardCost = 1 := rfl

/-- Compile an expression into a one-output De Morgan circuit. -/
def circuit : (expression : Expression n) ->
    Circuit signature n 1
  | .input index =>
      (Circuit.id signature n).mapOutputs (fun _ => index)
  | .constant value => constantCircuit value n
  | .not child => notCircuit.comp child.circuit
  | .and left right => andCircuit.comp
      (left.circuit.parallel right.circuit)
  | .or left right => orCircuit.comp
      (left.circuit.parallel right.circuit)

/-- Compilation emits exactly `gateCount` program gates. -/
@[simp] theorem circuit_size
    (expression : Expression n) :
    expression.circuit.size = expression.gateCount := by
  induction expression with
  | input index => rfl
  | constant value => rfl
  | not child inductionHypothesis =>
      simp [circuit, gateCount, inductionHypothesis, notCircuit]
  | and left right leftIH rightIH =>
      simp [circuit, gateCount, leftIH, rightIH, andCircuit]
  | or left right leftIH rightIH =>
      simp [circuit, gateCount, leftIH, rightIH, orCircuit]

/-- Compilation preserves Boolean semantics. -/
@[simp] theorem circuit_eval
    (expression : Expression n)
    (input : Fin n -> Bool) :
    expression.circuit.eval interpretation input 0 =
      expression.eval input := by
  induction expression with
  | input index =>
      simp [circuit, eval]
  | constant value =>
      simp [circuit, eval]
  | not child inductionHypothesis =>
      rw [circuit, Circuit.eval_comp, notCircuit_eval,
        inductionHypothesis]
      rfl
  | and left right leftIH rightIH =>
      rw [circuit, Circuit.eval_comp, andCircuit_eval]
      rw [Circuit.eval_parallel]
      have leftValue : Fin.append
          (left.circuit.eval interpretation input)
          (right.circuit.eval interpretation input) (0 : Fin 2) =
          left.circuit.eval interpretation input 0 := by rfl
      have rightValue : Fin.append
          (left.circuit.eval interpretation input)
          (right.circuit.eval interpretation input) (1 : Fin 2) =
          right.circuit.eval interpretation input 0 := by rfl
      rw [leftValue, rightValue]
      rw [leftIH, rightIH]
      rfl
  | or left right leftIH rightIH =>
      rw [circuit, Circuit.eval_comp, orCircuit_eval]
      rw [Circuit.eval_parallel]
      have leftValue : Fin.append
          (left.circuit.eval interpretation input)
          (right.circuit.eval interpretation input) (0 : Fin 2) =
          left.circuit.eval interpretation input 0 := by rfl
      have rightValue : Fin.append
          (left.circuit.eval interpretation input)
          (right.circuit.eval interpretation input) (1 : Fin 2) =
          right.circuit.eval interpretation input 0 := by rfl
      rw [leftValue, rightValue]
      rw [leftIH, rightIH]
      rfl

/-- Compilation realizes the expression's standard charged cost exactly. -/
@[simp] theorem circuit_cost
    (expression : Expression n) :
    expression.circuit.cost DeMorgan.standardCost =
      expression.standardCost := by
  induction expression with
  | input index =>
      simp [circuit, standardCost]
  | constant value =>
      cases value <;> rfl
  | not child inductionHypothesis =>
      simp [circuit, standardCost, inductionHypothesis]
  | and left right leftIH rightIH =>
      simp [circuit, standardCost, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [circuit, standardCost, leftIH, rightIH]

/-- De Morgan implementation of Boolean XOR. -/
def xor (left right : Expression n) : Expression n :=
  .and (.or left right) (.not (.and left right))

@[simp] theorem xor_eval
    (left right : Expression n)
    (input : Fin n -> Bool) :
    (xor left right).eval input = left.eval input + right.eval input := by
  rw [Bool.add_eq_xor]
  cases leftValue : left.eval input <;>
    cases rightValue : right.eval input <;>
      simp [xor, eval, leftValue, rightValue]

/-- XOR a finite expression family, with false for the empty family. -/
def finXor :
    (count : Nat) -> (Fin count -> Expression n) -> Expression n
  | 0, _ => .constant false
  | count + 1, terms =>
      xor (finXor count (fun index => terms index.castSucc))
        (terms (Fin.last count))

@[simp] theorem finXor_eval
    (count : Nat)
    (terms : Fin count -> Expression n)
    (input : Fin n -> Bool) :
    (finXor count terms).eval input =
      Finset.univ.sum fun index => (terms index).eval input := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finXor, xor_eval, inductionHypothesis, Fin.sum_univ_castSucc]

/-- Conjunction of a finite expression family, with `true` as the empty
conjunction. -/
def finAnd :
    (count : Nat) -> (Fin count -> Expression n) -> Expression n
  | 0, _ => .constant true
  | count + 1, terms =>
      .and (finAnd count (fun index => terms index.castSucc))
        (terms (Fin.last count))

/-- Disjunction of a finite expression family, with `false` as the empty
disjunction. -/
def finOr :
    (count : Nat) -> (Fin count -> Expression n) -> Expression n
  | 0, _ => .constant false
  | count + 1, terms =>
      .or (finOr count (fun index => terms index.castSucc))
        (terms (Fin.last count))

/-- Boolean fold matching `finAnd`'s constructor order. -/
def finAndValue :
    (count : Nat) -> (Fin count -> Bool) -> Bool
  | 0, _ => true
  | count + 1, values =>
      finAndValue count (fun index => values index.castSucc) &&
        values (Fin.last count)

/-- Boolean fold matching `finOr`'s constructor order. -/
def finOrValue :
    (count : Nat) -> (Fin count -> Bool) -> Bool
  | 0, _ => false
  | count + 1, values =>
      finOrValue count (fun index => values index.castSucc) ||
        values (Fin.last count)

@[simp] theorem finAnd_eval
    (count : Nat)
    (terms : Fin count -> Expression n)
    (input : Fin n -> Bool) :
    (finAnd count terms).eval input =
      finAndValue count (fun index => (terms index).eval input) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finAnd, eval, finAndValue, inductionHypothesis]

@[simp] theorem finOr_eval
    (count : Nat)
    (terms : Fin count -> Expression n)
    (input : Fin n -> Bool) :
    (finOr count terms).eval input =
      finOrValue count (fun index => (terms index).eval input) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finOr, eval, finOrValue, inductionHypothesis]

theorem finAndValue_eq_true_iff
    (count : Nat)
    (values : Fin count -> Bool) :
    finAndValue count values = true ↔
      ∀ index, values index = true := by
  induction count with
  | zero => simp [finAndValue]
  | succ count inductionHypothesis =>
      rw [finAndValue, Bool.and_eq_true, inductionHypothesis]
      constructor
      · rintro ⟨hprefix, hfinal⟩ index
        exact Fin.lastCases hfinal (fun prior => hprefix prior) index
      · intro all
        exact ⟨fun prior => all prior.castSucc, all (Fin.last count)⟩

theorem finOrValue_eq_true_iff
    (count : Nat)
    (values : Fin count -> Bool) :
    finOrValue count values = true ↔
      ∃ index, values index = true := by
  induction count with
  | zero => simp [finOrValue]
  | succ count inductionHypothesis =>
      rw [finOrValue, Bool.or_eq_true, inductionHypothesis]
      constructor
      · rintro (hprefix | hfinal)
        · obtain ⟨index, equal⟩ := hprefix
          exact ⟨index.castSucc, equal⟩
        · exact ⟨Fin.last count, hfinal⟩
      · rintro ⟨index, equal⟩
        exact Fin.lastCases
          (fun hfinal => Or.inr hfinal)
          (fun prior hprior => Or.inl ⟨prior, hprior⟩)
          index equal

/-- A disjunction selected by a one-hot flag family returns the selected
value. -/
theorem finOrValue_oneHot
    (count : Nat)
    (selected : Fin count)
    (flags values : Fin count -> Bool)
    (selectedTrue : flags selected = true)
    (unique : ∀ index, flags index = true -> index = selected) :
    finOrValue count (fun index => flags index && values index) =
      values selected := by
  apply Bool.eq_iff_iff.mpr
  rw [finOrValue_eq_true_iff]
  constructor
  · rintro ⟨index, equal⟩
    rw [Bool.and_eq_true] at equal
    rw [unique index equal.1] at equal
    exact equal.2
  · intro selectedValue
    refine ⟨selected, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨selectedTrue, selectedValue⟩

/-- Exact charged cost of a finite conjunction. -/
theorem finAnd_standardCost
    (count : Nat)
    (terms : Fin count -> Expression n) :
    (finAnd count terms).standardCost =
      (∑ index, (terms index).standardCost) + count := by
  induction count with
  | zero => simp [finAnd, standardCost]
  | succ count inductionHypothesis =>
      rw [finAnd, standardCost, inductionHypothesis,
        Fin.sum_univ_castSucc]
      omega

/-- Exact charged cost of a finite disjunction. -/
theorem finOr_standardCost
    (count : Nat)
    (terms : Fin count -> Expression n) :
    (finOr count terms).standardCost =
      (∑ index, (terms index).standardCost) + count := by
  induction count with
  | zero => simp [finOr, standardCost]
  | succ count inductionHypothesis =>
      rw [finOr, standardCost, inductionHypothesis,
        Fin.sum_univ_castSucc]
      omega

end Expression
end DeMorgan
end Algebraic
