/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.HighRate.LineParity
public import Mathlib.FieldTheory.Finite.Polynomial

/-!
# Independence of reduced monomial evaluations

Finite-field interpolation makes evaluation injective on polynomials of
degree below the field cardinality in each coordinate. Therefore every
family of distinct reduced monomials remains linearly independent as a
family of evaluation tables.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

/-- Distinct reduced monomials give linearly independent evaluation tables. -/
theorem monomialValuesLinearIndependent
    {K Coordinate : Type u} {Index : Type*}
    [Field K] [Fintype K] [Fintype Coordinate]
    (degrees : Index → Coordinate → Nat)
    (distinct : Function.Injective degrees)
    (reduced : ∀ index coordinate, degrees index coordinate < Fintype.card K) :
    LinearIndependent K (fun index => monomialValue (degrees index) (K := K)) := by
  classical
  let exponent := fun index => Finsupp.equivFunOnFinite.symm (degrees index)
  let polynomial := fun index => MvPolynomial.monomial (exponent index) (1 : K)
  have exponentsDistinct : Function.Injective exponent :=
    Finsupp.equivFunOnFinite.symm.injective.comp distinct
  have polynomialIndependent : LinearIndependent K polynomial := by
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, polynomial] using
      (MvPolynomial.basisMonomials Coordinate K).linearIndependent.comp exponent exponentsDistinct
  let bounded := MvPolynomial.restrictDegree Coordinate K (Fintype.card K - 1)
  have spanBounded : Submodule.span K (Set.range polynomial) ≤ bounded := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    change MvPolynomial.monomial (exponent index) (1 : K) ∈
      MvPolynomial.restrictSupport K {exponent | ∀ coordinate, exponent coordinate ≤ Fintype.card K - 1}
    rw [MvPolynomial.monomial_mem_restrictSupport]
    apply Or.inl
    intro coordinate
    exact Nat.le_sub_one_of_lt (reduced index coordinate)
  have evaluationInjective : Set.InjOn (MvPolynomial.evalₗ K Coordinate)
      (Submodule.span K (Set.range polynomial)) := by
    intro left leftIn right rightIn evaluationsEqual
    apply sub_eq_zero.mp
    apply MvPolynomial.eq_zero_of_eval_eq_zero Coordinate K (left - right)
    · intro point
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrFun evaluationsEqual point
    · exact bounded.sub_mem (spanBounded leftIn) (spanBounded rightIn)
  have evaluatedIndependent := polynomialIndependent.map_injOn
    (MvPolynomial.evalₗ K Coordinate) evaluationInjective
  have evaluates : (MvPolynomial.evalₗ K Coordinate) ∘ polynomial =
      fun index => monomialValue (degrees index) (K := K) := by
    funext index point
    change MvPolynomial.eval point (polynomial index) = monomialValue (degrees index) point
    rw [MvPolynomial.eval_monomial, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rwa [evaluates] at evaluatedIndependent

end Algebraic.MassProduction.HighRate
