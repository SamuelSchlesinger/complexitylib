/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant.Rectangular
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Degree visibility of rectangular catalecticants

Every entry queried by the degree-`d`, split-`k` catalecticant has total degree
exactly `d`.  Thus all splits factor through the same degree-`d` homogeneous
component; only the subsequent flattening changes with `k`.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Rectangular
namespace Degree

noncomputable section

open scoped BigOperators

variable {K : Type}

/-- Every queried exponent has Finsupp degree exactly `degree`. -/
theorem entryExponent_degree
    (degree split : Nat)
    (row column : SumOfTerms.MatrixRank.Layer degree split) :
    (SumOfTerms.Waring.Rectangular.entryExponent degree split row column).degree =
      degree := by
  change (SumOfTerms.Waring.Rectangular.entryExponent degree split row column).sum
    (fun _ multiplicity => multiplicity) = degree
  exact SumOfTerms.Waring.Rectangular.entryExponent_sum degree split row column

/-- Coefficients queried by the rectangular catalecticant vanish below total
degree `degree`. -/
theorem coeff_entryExponent_eq_zero_of_totalDegree_lt
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (small : polynomial.totalDegree < degree)
    (row column : SumOfTerms.MatrixRank.Layer degree split) :
    AddMonoidAlgebra.coeff polynomial (SumOfTerms.Waring.Rectangular.entryExponent degree split row column) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  have queriedDegree :
      (∑ index ∈
          (SumOfTerms.Waring.Rectangular.entryExponent degree split row column).support,
        SumOfTerms.Waring.Rectangular.entryExponent degree split row column index) =
        degree := by
    change (SumOfTerms.Waring.Rectangular.entryExponent degree split row column).sum
      (fun _ multiplicity => multiplicity) = degree
    exact SumOfTerms.Waring.Rectangular.entryExponent_sum degree split row column
  rw [queriedDegree]
  exact small

/-- Lower-total-degree polynomials have zero rectangular catalecticant. -/
theorem catalecticant_eq_zero_of_totalDegree_lt
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (small : polynomial.totalDegree < degree) :
    SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial = 0 := by
  ext row column
  simp [SumOfTerms.Waring.Rectangular.catalecticant_apply,
    coeff_entryExponent_eq_zero_of_totalDegree_lt degree split polynomial
      small]

/-- Lower-total-degree polynomials are feature-invisible. -/
theorem feature_eq_zero_of_totalDegree_lt
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (small : polynomial.totalDegree < degree) :
    SumOfTerms.Waring.Rectangular.feature K degree split polynomial = 0 := by
  simp [SumOfTerms.Waring.Rectangular.feature,
    catalecticant_eq_zero_of_totalDegree_lt degree split polynomial small]

/-- The rectangular catalecticant only sees the degree-`degree` homogeneous
component. -/
theorem catalecticant_homogeneousComponent
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    SumOfTerms.Waring.Rectangular.catalecticant K degree split
        (MvPolynomial.homogeneousComponent degree polynomial) =
      SumOfTerms.Waring.Rectangular.catalecticant K degree split polynomial := by
  ext row column
  simp [SumOfTerms.Waring.Rectangular.catalecticant_apply,
    MvPolynomial.coeff_homogeneousComponent,
    entryExponent_degree degree split row column]

/-- Every split factors through the common critical homogeneous layer. -/
theorem feature_homogeneousComponent
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K) :
    SumOfTerms.Waring.Rectangular.feature K degree split
        (MvPolynomial.homogeneousComponent degree polynomial) =
      SumOfTerms.Waring.Rectangular.feature K degree split polynomial := by
  simp [SumOfTerms.Waring.Rectangular.feature,
    catalecticant_homogeneousComponent degree split polynomial]

/-- A zero critical component is invisible at every split. -/
theorem feature_eq_zero_of_homogeneousComponent_eq_zero
    [Field K]
    (degree split : Nat)
    (polynomial : MvPolynomial (Fin degree) K)
    (invisible : MvPolynomial.homogeneousComponent degree polynomial = 0) :
    SumOfTerms.Waring.Rectangular.feature K degree split polynomial = 0 := by
  rw [← feature_homogeneousComponent degree split polynomial, invisible]
  exact LinearMap.map_zero _

/-- A rectangular Waring linear form is homogeneous of degree one. -/
theorem linearForm_isHomogeneous
    [CommSemiring K]
    (term : SumOfTerms.Waring.Rectangular.Term K degree) :
    (SumOfTerms.Waring.Rectangular.linearForm term).IsHomogeneous 1 := by
  classical
  unfold SumOfTerms.Waring.Rectangular.linearForm
  apply MvPolynomial.IsHomogeneous.sum
  intro index _
  rw [MvPolynomial.smul_eq_C_mul]
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- A charged rectangular Waring term is homogeneous of total degree
`degree`. -/
theorem termValue_isHomogeneous
    [CommSemiring K]
    (term : SumOfTerms.Waring.Rectangular.Term K degree) :
    (SumOfTerms.Waring.Rectangular.termValue term).IsHomogeneous degree := by
  unfold SumOfTerms.Waring.Rectangular.termValue
  simpa using ((linearForm_isHomogeneous term).pow degree).C_mul term.scale

/-- Projecting a rectangular Waring term to its critical layer leaves it
unchanged. -/
theorem homogeneousComponent_termValue
    [CommSemiring K]
    (term : SumOfTerms.Waring.Rectangular.Term K degree) :
    MvPolynomial.homogeneousComponent degree
        (SumOfTerms.Waring.Rectangular.termValue term) =
      SumOfTerms.Waring.Rectangular.termValue term :=
  MvPolynomial.homogeneousComponent_eq_self (termValue_isHomogeneous term)

end
end Degree
end Rectangular
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
