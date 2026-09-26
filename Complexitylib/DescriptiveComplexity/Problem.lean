/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.DescriptiveComplexity.SecondOrder.Definable

/-!
# Invariant decision problems

A decision problem is a Boolean query together with its isomorphism invariance.
Bundling this law lets structural reductions compose even when the intermediate
universes have different canonical presentations. This is the decision-problem
interface used by Senellart--Gnatenko (2026), Section 3.1, specialized to our
`FinStruct` convention of at least two elements.
-/

@[expose] public section

namespace Complexity.DescriptiveComplexity

/-- An isomorphism-invariant property of finite structures. -/
structure DecisionProblem (V : Vocabulary) where
  /-- The underlying query on structures. -/
  toQuery : BooleanQuery V
  /-- Renaming the universe does not affect the answer. -/
  invariant : toQuery.IsOrderIndependent

instance {V : Vocabulary} : CoeFun (DecisionProblem V) (fun _ => FinStruct V → Prop) :=
  ⟨DecisionProblem.toQuery⟩

namespace DecisionProblem

variable {V : Vocabulary}

/-- Bundle an FO-definable query as a decision problem. -/
def ofFODefinable (Q : BooleanQuery V) (hQ : FODefinable Q) : DecisionProblem V :=
  ⟨Q, hQ.orderIndependent⟩

/-- Bundle an existential SO-definable query as a decision problem. -/
def ofExistSODefinable (Q : BooleanQuery V) (hQ : ExistSODefinable Q) : DecisionProblem V :=
  ⟨Q, hQ.orderIndependent⟩

/-- Complement of an invariant decision problem. -/
def complement (P : DecisionProblem V) : DecisionProblem V :=
  ⟨P.toQuery.complement, BooleanQuery.complement_orderIndependent P.invariant⟩

/-- Intersection of invariant decision problems. -/
def inter (P Q : DecisionProblem V) : DecisionProblem V :=
  ⟨P.toQuery.inter Q.toQuery, BooleanQuery.inter_orderIndependent P.invariant Q.invariant⟩

/-- Union of invariant decision problems. -/
def union (P Q : DecisionProblem V) : DecisionProblem V :=
  ⟨P.toQuery.union Q.toQuery, BooleanQuery.union_orderIndependent P.invariant Q.invariant⟩

end DecisionProblem

end Complexity.DescriptiveComplexity
