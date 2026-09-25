/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MultiplicativeShadow
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Root-multiplicity shadows for polynomial circuits

For finitely many points, record the root multiplicity of a polynomial at
each point and cast those natural numbers into the coefficient field.  Away
from the zero polynomial, root multiplicities add under multiplication.  We
send the zero polynomial to the zero vector; if a product is zero, the
multiplicative-shadow rule instead uses zero coefficients.  This gives a
total feature suitable for circuits that may contain zero intermediate
values.

As a concrete application, one circuit producing the distinct nonzero shifts
`X - a_i` from `X` needs one addition per shift.  Multiplications, arbitrary
field constants, cancellation, and sharing between outputs remain entirely
unrestricted.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MultiplicativeShadow
namespace RootMultiplicity

open scoped Polynomial

variable {K : Type u} {C : Type v}

/-- Vector of root multiplicities at the selected points, cast into `K`. -/
noncomputable def rootMultiplicityFeature
    [Field K]
    (points : Fin m → K)
    (polynomial : K[X]) : Fin m → K :=
  fun point ↦ (polynomial.rootMultiplicity (points point) : K)

@[simp] theorem rootMultiplicityFeature_zero
    [Field K]
    (points : Fin m → K) :
    rootMultiplicityFeature points (0 : K[X]) = 0 := by
  funext point
  simp [rootMultiplicityFeature]

@[simp] theorem rootMultiplicityFeature_C
    [Field K]
    (points : Fin m → K)
    (value : K) :
    rootMultiplicityFeature points (Polynomial.C value) = 0 := by
  funext point
  simp [rootMultiplicityFeature]

/-- Root-multiplicity vectors add under a nonzero polynomial product. -/
theorem rootMultiplicityFeature_mul_of_ne_zero
    [Field K]
    (points : Fin m → K)
    {left right : K[X]}
    (product_ne_zero : left * right ≠ 0) :
    rootMultiplicityFeature points (left * right) =
      rootMultiplicityFeature points left +
        rootMultiplicityFeature points right := by
  funext point
  simp [rootMultiplicityFeature,
    Polynomial.rootMultiplicity_mul product_ne_zero]

/-- Total span propagation, including products that vanish. -/
theorem rootMultiplicityFeature_mul_span
    [Field K]
    (points : Fin m → K)
    (left right : K[X]) :
    ∃ leftScalar rightScalar : K,
      rootMultiplicityFeature points (left * right) =
        leftScalar • rootMultiplicityFeature points left +
          rightScalar • rootMultiplicityFeature points right := by
  by_cases product_ne_zero : left * right ≠ 0
  · exact ⟨1, 1, by
      simpa using rootMultiplicityFeature_mul_of_ne_zero points
        product_ne_zero⟩
  · exact ⟨0, 0, by simp [not_ne_iff.mp product_ne_zero]⟩

/-- Root-multiplicity certificate for any polynomial construction problem
whose free inputs do not vanish at the selected points. -/
noncomputable def certificate
    [Field K]
    (constant : C → K)
    (problem : Problem K[X])
    (points : Fin m → K)
    (input_zero : ∀ input point,
      (problem.inputs input).rootMultiplicity (points point) = 0) :
    MultiplicativeShadow.Certificate
      (K := K) (Q := Fin m → K)
      (fun scalar ↦ Polynomial.C (constant scalar)) problem where
  feature := rootMultiplicityFeature points
  input_zero := by
    intro input
    funext point
    simp [rootMultiplicityFeature, input_zero input point]
  constant_zero := fun scalar ↦
    rootMultiplicityFeature_C points (constant scalar)
  feature_mul := rootMultiplicityFeature_mul_span points

@[simp] theorem certificate_feature
    [Field K]
    (constant : C → K)
    (problem : Problem K[X])
    (points : Fin m → K)
    (input_zero : ∀ input point,
      (problem.inputs input).rootMultiplicity (points point) = 0)
    (polynomial : K[X]) :
    (certificate constant problem points input_zero).feature polynomial =
      rootMultiplicityFeature points polynomial := by
  simp [certificate]

/-- The span rank of any requested root-multiplicity vectors is bounded by
the addition cost of a circuit constructing those polynomials. -/
theorem rootMultiplicityFeatureSpan_finrank_le_additionCost
    [Field K]
    (constant : C → K)
    (problem : Problem K[X])
    (points : Fin r → K)
    (input_zero : ∀ input point,
      (problem.inputs input).rootMultiplicity (points point) = 0)
    (targets : Fin m → K[X])
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ Polynomial.C (constant scalar))
      problem targets circuit) :
    Module.finrank K
        (Submodule.span K
          (Set.range (rootMultiplicityFeature points ∘ targets))) ≤
      circuit.cost (Algebraic.Arithmetic.additionCost (K := C)) := by
  let shadowCertificate := certificate constant problem points input_zero
  have bound := featureSpan_finrank_le_additionCost shadowCertificate targets
    circuit constructs
  change Module.finrank K
      (Submodule.span K
        (Set.range (rootMultiplicityFeature points ∘ targets))) ≤
    circuit.cost (Algebraic.Arithmetic.additionCost (K := C)) at bound
  exact bound

/-- Independent root-multiplicity vectors force one addition per requested
output. -/
theorem circuit_addition_lowerBound_of_rootMultiplicityFeature
    [Field K]
    (constant : C → K)
    (problem : Problem K[X])
    (points : Fin r → K)
    (input_zero : ∀ input point,
      (problem.inputs input).rootMultiplicity (points point) = 0)
    (targets : Fin m → K[X])
    (independent : LinearIndependent K
      (rootMultiplicityFeature points ∘ targets))
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      problem.inputCount m)
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ Polynomial.C (constant scalar))
      problem targets circuit) :
    m ≤ circuit.cost (Algebraic.Arithmetic.additionCost (K := C)) := by
  let shadowCertificate := certificate constant problem points input_zero
  apply circuit_addition_lowerBound_of_linearIndependent shadowCertificate
    targets ?_ circuit constructs
  change LinearIndependent K
    (rootMultiplicityFeature points ∘ targets)
  exact independent

/-- The one-input construction problem used for the shift family.  Its
single-output target is irrelevant to the multi-output theorem. -/
noncomputable def shiftProblem [Field K] : Problem K[X] where
  inputCount := 1
  inputs := fun _ ↦ Polynomial.X
  target := 0

/-- Distinct affine shifts requested as simultaneous outputs. -/
noncomputable def shiftTargets [Field K]
    (points : Fin m → K) : Fin m → K[X] :=
  fun point ↦ Polynomial.X - Polynomial.C (points point)

/-- A nonzero point is not a root of the free input `X`. -/
theorem rootMultiplicity_X_eq_zero
    [Field K]
    {point : K}
    (point_ne_zero : point ≠ 0) :
    (Polynomial.X : K[X]).rootMultiplicity point = 0 := by
  classical
  rw [show (Polynomial.X : K[X]) =
    Polynomial.X - Polynomial.C 0 by simp]
  simp [point_ne_zero]

/-- At distinct points, the shift targets have the standard-basis
root-multiplicity vectors. -/
theorem rootMultiplicityFeature_shiftTargets
    [Field K]
    (points : Fin m → K)
    (injective : Function.Injective points)
    (point : Fin m) :
    rootMultiplicityFeature points (shiftTargets points point) =
      Pi.single point 1 := by
  classical
  funext coordinate
  by_cases equal : coordinate = point
  · subst coordinate
    simp [rootMultiplicityFeature, shiftTargets,
      Polynomial.rootMultiplicity_X_sub_C]
  · have values_ne : points coordinate ≠ points point := by
      exact fun values_eq ↦ equal (injective values_eq)
    simp [rootMultiplicityFeature, shiftTargets,
      Polynomial.rootMultiplicity_X_sub_C, values_ne, equal]

/-- Root-multiplicity shadows of distinct shifts are linearly independent. -/
theorem linearIndependent_rootMultiplicityFeature_shiftTargets
    [Field K]
    (points : Fin m → K)
    (injective : Function.Injective points) :
    LinearIndependent K
      (rootMultiplicityFeature points ∘ shiftTargets points) := by
  have feature_eq : rootMultiplicityFeature points ∘ shiftTargets points =
      fun point ↦ Pi.single point (1 : K) := by
    funext point
    exact rootMultiplicityFeature_shiftTargets points injective point
  rw [feature_eq]
  exact Pi.linearIndependent_single_one (Fin m) K

/-- One circuit producing `m` distinct nonzero affine shifts of its free
input needs at least `m` addition gates. -/
theorem shiftTargets_addition_lowerBound
    [Field K]
    (constant : C → K)
    (points : Fin m → K)
    (injective : Function.Injective points)
    (nonzero : ∀ point, points point ≠ 0)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) 1 m)
    (constructs : circuit.eval
      (Algebraic.Arithmetic.interpretation
        (fun scalar ↦ Polynomial.C (constant scalar)))
      (shiftProblem (K := K)).inputs = shiftTargets points) :
    m ≤ circuit.cost (Algebraic.Arithmetic.additionCost (K := C)) := by
  let inputRootFree : ∀ input point,
      ((shiftProblem (K := K)).inputs input).rootMultiplicity
        (points point) = 0 := by
    intro input point
    exact rootMultiplicity_X_eq_zero (nonzero point)
  exact circuit_addition_lowerBound_of_rootMultiplicityFeature constant
    (shiftProblem (K := K)) points inputRootFree (shiftTargets points)
    (linearIndependent_rootMultiplicityFeature_shiftTargets points injective)
    circuit constructs

end RootMultiplicity
end MultiplicativeShadow
end Arithmetic
end Fusion
end Algebraic
