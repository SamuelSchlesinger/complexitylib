/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LowDegree
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Tensor-product low-degree evaluation codes

This is the algebraic evaluation code used by the local-recovery gadget in
the
[Boolean mass-production manuscript](https://github.com/SamuelSchlesinger/boolean-mass-production).
Arbitrary data on a finite Cartesian grid is interpolated by a multivariate
polynomial and evaluated over the whole ambient affine space.

The semantic node map below is a fixed noncomputable injection obtained from
the finite cardinality equivalence. It proves the code theorem independently
of representation. A later circuit layer must use the manuscript's concrete
polynomial-basis field representation and prove its indexing costs.
-/

@[expose] public section

namespace Algebraic
namespace MassProduction

open scoped BigOperators

/-- The tensor-product Lagrange basis polynomial for one grid point. -/
noncomputable def gridBasis
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index] [Fintype Coordinate]
    (nodes : Index -> K)
    (point : Coordinate -> Index) : MvPolynomial Coordinate K :=
  ∏ coordinate : Coordinate,
    (Lagrange.basis Finset.univ nodes (point coordinate)).toMvPolynomial
      coordinate

/-- Interpolate an arbitrary field-valued message on a Cartesian grid. -/
noncomputable def gridInterpolate
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (message : (Coordinate -> Index) -> K) : MvPolynomial Coordinate K :=
  ∑ point : Coordinate -> Index,
    MvPolynomial.C (message point) * gridBasis nodes point

/-- Evaluate the tensor-grid interpolant at an ambient point. -/
noncomputable def evaluationCode
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (message : (Coordinate -> Index) -> K)
    (point : Coordinate -> K) : K :=
  MvPolynomial.eval point (gridInterpolate nodes message)

/-- The paper's grid width `floor ((q - 1) / dimension)`. -/
def resourceGridWidth (fieldCard dimension : Nat) : Nat :=
  (fieldCard - 1) / dimension

/-- A fixed semantic injection of interpolation-node indices into a finite
field. This definition is intentionally noncomputable; concrete field
indexing belongs to the circuit-realization layer. -/
noncomputable def resourceNodes
    (K : Type*)
    [Fintype K]
    (dimension : Nat) :
    Fin (resourceGridWidth (Fintype.card K) dimension) -> K :=
  fun point => (Fintype.equivFin K).symm
    ⟨point.val, point.isLt.trans_le <| by
      unfold resourceGridWidth
      exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)⟩

/-- The paper-parameterized systematic resource code. -/
noncomputable def paperEvaluationCode
    (K : Type*)
    [Field K] [Fintype K]
    (dimension : Nat)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (point : Fin dimension -> K) : K :=
  evaluationCode (resourceNodes K dimension) message point

/-- A tensor Lagrange basis polynomial evaluates to one at its own grid
point. -/
theorem eval_gridBasis_self
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate]
    (nodes : Index -> K)
    (nodesInjective : Function.Injective nodes)
    (point : Coordinate -> Index) :
    MvPolynomial.eval (nodes ∘ point) (gridBasis nodes point) = 1 := by
  classical
  simp [gridBasis, Lagrange.eval_basis_self nodesInjective.injOn]

/-- A tensor Lagrange basis polynomial vanishes at every other grid point. -/
theorem eval_gridBasis_of_ne
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate]
    (nodes : Index -> K)
    (target point : Coordinate -> Index)
    (different : target ≠ point) :
    MvPolynomial.eval (nodes ∘ target) (gridBasis nodes point) = 0 := by
  classical
  obtain ⟨coordinate, coordinateDifferent⟩ := Function.ne_iff.mp different
  rw [gridBasis, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
  rw [MvPolynomial.eval_toMvPolynomial]
  exact Lagrange.eval_basis_of_ne coordinateDifferent.symm (Finset.mem_univ _)

/-- The evaluation code agrees with the supplied message at every grid
point. -/
theorem evaluationCode_on_grid
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (nodesInjective : Function.Injective nodes)
    (message : (Coordinate -> Index) -> K)
    (target : Coordinate -> Index) :
    evaluationCode nodes message (nodes ∘ target) = message target := by
  classical
  simp only [evaluationCode, gridInterpolate, map_sum, map_mul,
    MvPolynomial.eval_C]
  rw [Finset.sum_eq_single target]
  · rw [eval_gridBasis_self nodes nodesInjective target, mul_one]
  · intro point _ pointDifferent
    rw [eval_gridBasis_of_ne nodes target point pointDifferent.symm, mul_zero]
  · simp

/-- Grid interpolation preserves message addition. -/
theorem gridInterpolate_add
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (left right : (Coordinate -> Index) -> K) :
    gridInterpolate nodes (left + right) =
      gridInterpolate nodes left + gridInterpolate nodes right := by
  classical
  simp only [gridInterpolate, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

/-- Grid interpolation preserves field scalar multiplication. -/
theorem gridInterpolate_smul
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (scalar : K)
    (message : (Coordinate -> Index) -> K) :
    gridInterpolate nodes (scalar • message) =
      scalar • gridInterpolate nodes message := by
  classical
  rw [gridInterpolate, gridInterpolate]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  simp only [map_mul]
  rw [MvPolynomial.algebraMap_eq, mul_assoc]

/-- Distinct grid messages have distinct ambient evaluation tables. -/
theorem evaluationCode_injective
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (nodesInjective : Function.Injective nodes) :
    Function.Injective
      (fun message : (Coordinate -> Index) -> K =>
        fun point => evaluationCode nodes message point) := by
  intro left right equalCodewords
  funext target
  rw [← evaluationCode_on_grid nodes nodesInjective left target,
    ← evaluationCode_on_grid nodes nodesInjective right target]
  exact congrFun equalCodewords (nodes ∘ target)

private theorem totalDegree_basisDivisor_toMv_le
    {K Coordinate : Type*}
    [Field K]
    (left right : K)
    (coordinate : Coordinate) :
    ((Lagrange.basisDivisor left right).toMvPolynomial coordinate :
      MvPolynomial Coordinate K).totalDegree <= 1 := by
  classical
  simp only [Lagrange.basisDivisor, map_mul, map_sub,
    Polynomial.toMvPolynomial_C, Polynomial.toMvPolynomial_X]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  rw [sub_eq_add_neg, ← MvPolynomial.C_neg]
  apply (MvPolynomial.totalDegree_add _ _).trans
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  simp

private theorem totalDegree_lagrangeBasis_toMv_le
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    (nodes : Index -> K)
    (point : Index)
    (coordinate : Coordinate) :
    ((Lagrange.basis Finset.univ nodes point).toMvPolynomial coordinate :
      MvPolynomial Coordinate K).totalDegree <= Fintype.card Index - 1 := by
  classical
  rw [Lagrange.basis, map_prod]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ index ∈ Finset.univ.erase point,
        ((Lagrange.basisDivisor (nodes point) (nodes index)).toMvPolynomial
          coordinate : MvPolynomial Coordinate K).totalDegree) <=
        ∑ _index ∈ Finset.univ.erase point, 1 := by
      apply Finset.sum_le_sum
      intro index _
      exact totalDegree_basisDivisor_toMv_le
        (nodes point) (nodes index) coordinate
    _ = Fintype.card Index - 1 := by simp

/-- A tensor basis polynomial has total degree at most the number of
coordinates times one less than the grid width. -/
theorem totalDegree_gridBasis_le
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate]
    (nodes : Index -> K)
    (point : Coordinate -> Index) :
    (gridBasis nodes point).totalDegree <=
      Fintype.card Coordinate * (Fintype.card Index - 1) := by
  classical
  rw [gridBasis]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ coordinate ∈ Finset.univ,
      ((Lagrange.basis Finset.univ nodes (point coordinate)).toMvPolynomial
        coordinate : MvPolynomial Coordinate K).totalDegree) <=
        ∑ _coordinate ∈ Finset.univ,
          (Fintype.card Index - 1) := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact totalDegree_lagrangeBasis_toMv_le
        nodes (point coordinate) coordinate
    _ = Fintype.card Coordinate * (Fintype.card Index - 1) := by simp

/-- The complete tensor-grid interpolant obeys the same total-degree
budget. -/
theorem totalDegree_gridInterpolate_le
    {K Index Coordinate : Type*}
    [Field K] [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (message : (Coordinate -> Index) -> K) :
    (gridInterpolate nodes message).totalDegree <=
      Fintype.card Coordinate * (Fintype.card Index - 1) := by
  classical
  rw [gridInterpolate]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro point _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_gridBasis_le nodes point

/-- The ambient evaluation table has `|K| ^ |Coordinate|` coordinates. -/
theorem card_evaluationCodeDomain
    (K Coordinate : Type*)
    [Fintype K] [Fintype Coordinate] [DecidableEq Coordinate] :
    Fintype.card (Coordinate -> K) =
      Fintype.card K ^ Fintype.card Coordinate := by
  simp

/-- The message grid has `|Index| ^ |Coordinate|` positions. -/
theorem card_evaluationCodeMessageDomain
    (Index Coordinate : Type*)
    [Fintype Index] [Fintype Coordinate] [DecidableEq Coordinate] :
    Fintype.card (Coordinate -> Index) =
      Fintype.card Index ^ Fintype.card Coordinate := by
  simp

/-- The fixed semantic node map is injective. -/
theorem resourceNodes_injective
    (K : Type*)
    [Fintype K]
    (dimension : Nat) :
    Function.Injective (resourceNodes K dimension) := by
  intro left right equalValues
  unfold resourceNodes at equalValues
  apply Fin.ext
  have equalFiniteIndices := (Fintype.equivFin K).symm.injective equalValues
  exact congrArg (fun point : Fin (Fintype.card K) => point.val)
    equalFiniteIndices

/-- The grid-width choice satisfies the strict affine-line degree bound. -/
theorem resourceGridWidth_degree_lt
    (fieldCard dimension : Nat)
    (fieldNontrivial : 2 <= fieldCard)
    (dimensionPositive : 0 < dimension) :
    dimension * (resourceGridWidth fieldCard dimension - 1) <
      fieldCard - 1 := by
  have productBound :
      dimension * resourceGridWidth fieldCard dimension <= fieldCard - 1 := by
    unfold resourceGridWidth
    exact Nat.mul_div_le (fieldCard - 1) dimension
  by_cases widthZero : resourceGridWidth fieldCard dimension = 0
  · simp [widthZero]
    omega
  · have widthPositive : 0 < resourceGridWidth fieldCard dimension :=
      Nat.pos_of_ne_zero widthZero
    have strictProduct :
        dimension * (resourceGridWidth fieldCard dimension - 1) <
          dimension * resourceGridWidth fieldCard dimension :=
      (Nat.mul_lt_mul_left dimensionPositive).mpr (by omega)
    exact strictProduct.trans_le productBound

/-- The paper-parameterized code is systematic on its interpolation grid. -/
theorem paperEvaluationCode_on_grid
    (K : Type*)
    [Field K] [Fintype K]
    (dimension : Nat)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (target :
      Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) :
    paperEvaluationCode K dimension message
      (resourceNodes K dimension ∘ target) = message target :=
  evaluationCode_on_grid _ (resourceNodes_injective K dimension)
    message target

/-- Under the exact tensor-degree inequality, every code symbol is the sum
of the other symbols on any affine line through it. -/
theorem evaluationCode_line_recovery_charTwo
    {K Index Coordinate : Type*}
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (nodes : Index -> K)
    (message : (Coordinate -> Index) -> K)
    (degree : Fintype.card Coordinate * (Fintype.card Index - 1) <
      Fintype.card K - 1)
    (target direction : Coordinate -> K) :
    evaluationCode nodes message target =
      ∑ parameter ∈ (Finset.univ.erase (0 : K)),
        evaluationCode nodes message
          (fun index => target index + direction index * parameter) := by
  unfold evaluationCode
  apply affineLine_identity_charTwo
  exact (totalDegree_gridInterpolate_le nodes message).trans_lt degree

/-- The paper's grid-width choice gives affine-line recovery in every
positive dimension. -/
theorem paperEvaluationCode_line_recovery
    (K : Type*)
    [Fintype K] [Field K] [DecidableEq K] [CharP K 2]
    (dimension : Nat)
    (dimensionPositive : 0 < dimension)
    (message :
      (Fin dimension ->
        Fin (resourceGridWidth (Fintype.card K) dimension)) -> K)
    (target direction : Fin dimension -> K) :
    paperEvaluationCode K dimension message target =
      ∑ parameter ∈ (Finset.univ.erase (0 : K)),
        paperEvaluationCode K dimension message
          (fun index => target index + direction index * parameter) := by
  unfold paperEvaluationCode
  apply evaluationCode_line_recovery_charTwo
  simpa only [Fintype.card_fin] using
    resourceGridWidth_degree_lt (Fintype.card K) dimension
      Fintype.one_lt_card dimensionPositive

end MassProduction
end Algebraic
