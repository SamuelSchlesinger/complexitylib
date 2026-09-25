/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.Cost
public import Complexitylib.Algebraic.Semantics
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Nonuniform circuit families

Circuit lower bounds are finite statements about one input width, while
complexity classes quantify over a sequence of circuits.  This module supplies
that missing bridge without fixing a gate basis.

A `Circuit.Family sigma m` chooses one `m`-output circuit for every input width.
Its gate count remains an explicit index, so `size` agrees definitionally with
the finite circuit model.  Polynomial size and constant depth are expressed by
exact natural-number bounds.  The factor `(n + 1) ^ degree` makes the definition
well behaved at input width zero and avoids burying finite-prefix adjustments
inside asymptotic notation.
-/

@[expose] public section

namespace Algebraic

namespace Target

/-- An `m`-output target at every input width. -/
abbrev Family (U : Type u) (m : Nat) :=
  (n : Nat) -> Target U n m

/-- Regard a family of scalar functions as a one-output target family. -/
def scalarFamily
    (family : (n : Nat) -> ScalarFunction U n) : Target.Family U 1 :=
  fun n input _ => family n input

@[simp] theorem scalarFamily_apply
    (family : (n : Nat) -> ScalarFunction U n)
    (input : Fin n -> U)
    (output : Fin 1) :
    Target.scalarFamily family n input output = family n input := rfl

end Target

namespace Circuit

namespace Resource

/-- A natural-valued resource is bounded by one fixed polynomial.

The coefficient and degree do not depend on the input width.  Using `n + 1`
gives an exact all-width statement equivalent to the usual eventual polynomial
bound for natural-valued resources. -/
def _root_.Cslib.Circuits.Circuit.Resource.PolynomiallyBounded (resource : Nat -> Nat) : Prop :=
  Exists fun coefficient : Nat =>
    Exists fun degree : Nat =>
      forall n, resource n <= coefficient * (n + 1) ^ degree

export Cslib.Circuits.Circuit.Resource (PolynomiallyBounded)

/-- A natural-valued resource is bounded by one constant at every width. -/
def _root_.Cslib.Circuits.Circuit.Resource.ConstantlyBounded (resource : Nat -> Nat) : Prop :=
  Exists fun bound : Nat => forall n, resource n <= bound

export Cslib.Circuits.Circuit.Resource (ConstantlyBounded)

/-- A resource eventually strictly exceeds every fixed natural polynomial. -/
def _root_.Cslib.Circuits.Circuit.Resource.EventuallyExceedsEveryPolynomial (resource : Nat -> Nat) : Prop :=
  forall coefficient degree,
    Filter.Eventually
      (fun n => coefficient * (n + 1) ^ degree < resource n)
      Filter.atTop

export Cslib.Circuits.Circuit.Resource (EventuallyExceedsEveryPolynomial)

/-- A pointwise smaller resource inherits a polynomial upper bound. -/
theorem _root_.Cslib.Circuits.Circuit.Resource.PolynomiallyBounded.of_le
    {smaller larger : Nat -> Nat}
    (bounded : PolynomiallyBounded larger)
    (comparison : forall n, smaller n <= larger n) :
    PolynomiallyBounded smaller := by
  obtain ⟨coefficient, degree, bound⟩ := bounded
  exact ⟨coefficient, degree, fun n => (comparison n).trans (bound n)⟩

export Cslib.Circuits.Circuit.Resource (PolynomiallyBounded.of_le)

/-- Every constant resource bound is a degree-zero polynomial bound. -/
theorem _root_.Cslib.Circuits.Circuit.Resource.ConstantlyBounded.polynomiallyBounded
    {resource : Nat -> Nat}
    (bounded : ConstantlyBounded resource) :
    PolynomiallyBounded resource := by
  obtain ⟨bound, bounded⟩ := bounded
  refine ⟨bound, 0, ?_⟩
  intro n
  simpa using bounded n

export Cslib.Circuits.Circuit.Resource (ConstantlyBounded.polynomiallyBounded)

/-- Eventual domination of every polynomial rules out a polynomial bound. -/
theorem _root_.Cslib.Circuits.Circuit.Resource.EventuallyExceedsEveryPolynomial.not_polynomiallyBounded
    {resource : Nat -> Nat}
    (dominates : EventuallyExceedsEveryPolynomial resource) :
    Not (PolynomiallyBounded resource) := by
  rintro ⟨coefficient, degree, bounded⟩
  obtain ⟨cutoff, dominatesFrom⟩ :=
    Filter.eventually_atTop.1 (dominates coefficient degree)
  exact (Nat.not_lt_of_ge (bounded cutoff))
    (dominatesFrom cutoff (le_refl cutoff))

export Cslib.Circuits.Circuit.Resource (EventuallyExceedsEveryPolynomial.not_polynomiallyBounded)

end Resource

/-- A nonuniform family chooses one finite circuit at each input width. -/
structure _root_.Cslib.Circuits.Circuit.Family (sigma : Signature) (m : Nat) where
  /-- Number of internal gates at each input width. -/
  gateCount : Nat -> Nat
  /-- The circuit chosen nonuniformly at each input width. -/
  circuit : (n : Nat) -> Circuit sigma n (gateCount n) m

export Cslib.Circuits.Circuit (Family)

namespace Family

/-- Gate-count size of every member of a circuit family. -/
def _root_.Cslib.Circuits.Circuit.Family.size (family : Circuit.Family sigma m) (n : Nat) : Nat :=
  (family.circuit n).size

export Cslib.Circuits.Circuit.Family (size)

@[simp] theorem _root_.Cslib.Circuits.Circuit.Family.size_eq_gateCount
    (family : Circuit.Family sigma m)
    (n : Nat) :
    family.size n = family.gateCount n := rfl

export Cslib.Circuits.Circuit.Family (size_eq_gateCount)

/-- Designated-output depth of every member of a circuit family. -/
def _root_.Cslib.Circuits.Circuit.Family.depth (family : Circuit.Family sigma m) (n : Nat) : Nat :=
  (family.circuit n).depth

export Cslib.Circuits.Circuit.Family (depth)

/-- Weighted gate cost of every member of a circuit family. -/
def _root_.Cslib.Circuits.Circuit.Family.cost
    (family : Circuit.Family sigma m)
    (operationCost : OperationCost sigma)
    (n : Nat) : Nat :=
  (family.circuit n).cost operationCost

export Cslib.Circuits.Circuit.Family (cost)

/-- Pointwise exact computation of a target family. -/
def _root_.Cslib.Circuits.Circuit.Family.Computes
    (family : Circuit.Family sigma m)
    (interpretation : Interpretation sigma U)
    (target : Target.Family U m) : Prop :=
  forall n, (family.circuit n).ComputesWith interpretation (target n)

export Cslib.Circuits.Circuit.Family (Computes)

/-- The family has a specified all-width size bound. -/
def _root_.Cslib.Circuits.Circuit.Family.HasSizeAtMost
    (family : Circuit.Family sigma m)
    (bound : Nat -> Nat) : Prop :=
  forall n, family.size n <= bound n

export Cslib.Circuits.Circuit.Family (HasSizeAtMost)

/-- The family has a specified all-width depth bound. -/
def _root_.Cslib.Circuits.Circuit.Family.HasDepthAtMost
    (family : Circuit.Family sigma m)
    (bound : Nat -> Nat) : Prop :=
  forall n, family.depth n <= bound n

export Cslib.Circuits.Circuit.Family (HasDepthAtMost)

/-- The family has polynomially bounded gate-count size. -/
def _root_.Cslib.Circuits.Circuit.Family.HasPolynomialSize (family : Circuit.Family sigma m) : Prop :=
  Resource.PolynomiallyBounded family.size

export Cslib.Circuits.Circuit.Family (HasPolynomialSize)

/-- The family has polynomially bounded weighted cost. -/
def _root_.Cslib.Circuits.Circuit.Family.HasPolynomialCost
    (family : Circuit.Family sigma m)
    (operationCost : OperationCost sigma) : Prop :=
  Resource.PolynomiallyBounded (family.cost operationCost)

export Cslib.Circuits.Circuit.Family (HasPolynomialCost)

/-- The family has one depth bound independent of the input width. -/
def _root_.Cslib.Circuits.Circuit.Family.HasConstantDepth (family : Circuit.Family sigma m) : Prop :=
  Resource.ConstantlyBounded family.depth

export Cslib.Circuits.Circuit.Family (HasConstantDepth)

/-- A pointwise size budget yields polynomial size when the budget is
polynomially bounded. -/
theorem _root_.Cslib.Circuits.Circuit.Family.HasSizeAtMost.polynomialSize
    {family : Circuit.Family sigma m}
    {bound : Nat -> Nat}
    (bounded : family.HasSizeAtMost bound)
    (polynomial : Resource.PolynomiallyBounded bound) :
    family.HasPolynomialSize :=
  polynomial.of_le bounded

export Cslib.Circuits.Circuit.Family (HasSizeAtMost.polynomialSize)

/-- A pointwise depth budget yields constant depth when the budget is
constantly bounded. -/
theorem _root_.Cslib.Circuits.Circuit.Family.HasDepthAtMost.constantDepth
    {family : Circuit.Family sigma m}
    {bound : Nat -> Nat}
    (bounded : family.HasDepthAtMost bound)
    (constant : Resource.ConstantlyBounded bound) :
    family.HasConstantDepth := by
  obtain ⟨depthBound, bound⟩ := constant
  exact ⟨depthBound, fun n => (bounded n).trans (bound n)⟩

export Cslib.Circuits.Circuit.Family (HasDepthAtMost.constantDepth)

end Family
end Circuit
end Algebraic
