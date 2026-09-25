/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost

/-!
# Sum-of-terms circuit basis

This basis represents restricted arithmetic circuits whose charged gates
produce members of a prescribed dictionary and whose free gates add already
constructed values.  By choosing the term type appropriately, it models
diagonal depth-three circuits (sums of powers), sums of products, tensor-rank
decompositions, and related representation problems.

Coefficients can be included in the term parameter itself.  This keeps the
syntax independent of any scalar action on the semantic carrier.
-/

@[expose] public section

namespace Algebraic
namespace SumOfTerms

/-- Binary addition and a family of nullary dictionary terms. -/
inductive Op (T : Type u)
  | add
  | term (value : T)
  deriving DecidableEq

/-- Arity of sum-of-terms operations. -/
def arity : Op T → Nat
  | .add => 2
  | .term _ => 0

@[simp] theorem arity_add : arity (Op.add : Op T) = 2 := rfl

@[simp] theorem arity_term (term : T) : arity (.term term) = 0 := rfl

/-- Signature for free addition of charged dictionary terms. -/
abbrev signature (T : Type u) : Signature where
  Op := Op T
  Arity := arity

/-- Interpret a term by its dictionary value and addition by carrier addition. -/
def interpretation
    [Add V]
    (termValue : T → V) : Interpretation (signature T) V
  | .add, input => input (0 : Fin 2) + input (1 : Fin 2)
  | .term term, _ => termValue term

/-- Charge source additions and dictionary terms independently. -/
def weightedCost
    (addition term : Nat) : OperationCost (signature T)
  | .add => addition
  | .term _ => term

/-- Charge one for each dictionary term and make addition free. -/
def termCost : OperationCost (signature T) :=
  weightedCost 0 1

/-- Charge each dictionary term by a term-dependent natural weight and make
addition free. -/
def dictionaryCost
    (weight : T → Nat) : OperationCost (signature T)
  | .add => 0
  | .term term => weight term

/-- Charge source additions and make dictionary terms free. -/
def additionCost : OperationCost (signature T) :=
  weightedCost 1 0

/-- Charge every source operation once. -/
def gateCost : OperationCost (signature T) :=
  weightedCost 1 1

@[simp] theorem weightedCost_add
    (addition term : Nat) :
    weightedCost (T := T) addition term .add = addition := rfl

@[simp] theorem weightedCost_term
    (addition term : Nat)
    (value : T) :
    weightedCost addition term (.term value) = term := rfl

@[simp] theorem termCost_add : termCost (T := T) .add = 0 := rfl

@[simp] theorem termCost_term (term : T) : termCost (.term term) = 1 := rfl

@[simp] theorem dictionaryCost_add
    (weight : T → Nat) :
    dictionaryCost weight .add = 0 := rfl

@[simp] theorem dictionaryCost_term
    (weight : T → Nat)
    (term : T) :
    dictionaryCost weight (.term term) = weight term := rfl

@[simp] theorem additionCost_add : additionCost (T := T) .add = 1 := rfl

@[simp] theorem additionCost_term (term : T) :
    additionCost (.term term) = 0 := rfl

@[simp] theorem gateCost_add : gateCost (T := T) .add = 1 := rfl

@[simp] theorem gateCost_term (term : T) : gateCost (.term term) = 1 := rfl

/-- Weighted source cost decomposes exactly into addition count and dictionary
term count. -/
theorem program_cost_weightedCost
    (program : Program (signature T) n g)
    (addition term : Nat) :
    program.cost (weightedCost addition term) =
      addition * program.cost (additionCost (T := T)) +
        term * program.cost (termCost (T := T)) := by
  induction program with
  | empty => simp
  | gate program line inductionHypothesis =>
      cases line with
      | mk op wires =>
          cases op <;>
            simp [Program.cost, inductionHypothesis, Nat.mul_add] <;>
            omega

/-- Circuit form of exact weighted source-cost decomposition. -/
theorem circuit_cost_weightedCost
    (circuit : Circuit (signature T) n g m)
    (addition term : Nat) :
    circuit.cost (weightedCost addition term) =
      addition * circuit.cost (additionCost (T := T)) +
        term * circuit.cost (termCost (T := T)) :=
  program_cost_weightedCost circuit.program addition term

end SumOfTerms
end Algebraic
