/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Polynomial.Catalecticant
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Degree-visible catalecticant fusion

The middle catalecticant at half-degree `n` only reads coefficients of total
degree `2 * n`.  Consequently every lower-degree polynomial is invisible to
the feature.  This supplies a structural way to discharge the invisible
branch of `PowerOrInvisibleAtMultiplications`.

The resulting ordinary-circuit subclass permits arbitrary lower-degree
multiplication outputs and charges only critical-degree outputs, which must be
scalar multiples of `2n`-th powers of linear forms.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Interaction
namespace Polynomial
namespace Catalecticant
namespace Degree

noncomputable section

open scoped BigOperators

variable {K : Type} {C : Type}

/-- Every coefficient read by the middle catalecticant vanishes below the
critical total degree. -/
theorem coeff_entryExponent_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n)
    (row column : SumOfTerms.MatrixRank.Layer (2 * n) n) :
    AddMonoidAlgebra.coeff polynomial (SumOfTerms.Waring.entryExponent n row column) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  have degree :
      (∑ index ∈
          (SumOfTerms.Waring.entryExponent n row column).support,
        SumOfTerms.Waring.entryExponent n row column index) = 2 * n := by
    change (SumOfTerms.Waring.entryExponent n row column).sum
      (fun _ multiplicity => multiplicity) = 2 * n
    exact SumOfTerms.Waring.exponent_add_complement_sum n row column
  rw [degree]
  exact small

/-- A polynomial below total degree `2n` has zero middle catalecticant. -/
theorem catalecticant_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n) :
    SumOfTerms.Waring.catalecticant K n polynomial = 0 := by
  ext row column
  simp [SumOfTerms.Waring.catalecticant_apply,
    coeff_entryExponent_eq_zero_of_totalDegree_lt n polynomial small]

/-- A polynomial below total degree `2n` is invisible to the catalecticant
linear-map feature. -/
theorem feature_eq_zero_of_totalDegree_lt
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (small : polynomial.totalDegree < 2 * n) :
    SumOfTerms.Waring.feature K n polynomial = 0 := by
  simp [SumOfTerms.Waring.feature,
    catalecticant_eq_zero_of_totalDegree_lt n polynomial small]

/-- Every exponent queried by the middle catalecticant has Finsupp degree
exactly `2n`. -/
theorem entryExponent_degree
    (n : Nat)
    (row column : SumOfTerms.MatrixRank.Layer (2 * n) n) :
    (SumOfTerms.Waring.entryExponent n row column).degree = 2 * n := by
  change (SumOfTerms.Waring.entryExponent n row column).sum
    (fun _ multiplicity => multiplicity) = 2 * n
  exact SumOfTerms.Waring.exponent_add_complement_sum n row column

/-- The middle catalecticant only sees the critical homogeneous component. -/
theorem catalecticant_homogeneousComponent
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) :
    SumOfTerms.Waring.catalecticant K n
        (MvPolynomial.homogeneousComponent (2 * n) polynomial) =
      SumOfTerms.Waring.catalecticant K n polynomial := by
  ext row column
  simp [SumOfTerms.Waring.catalecticant_apply,
    MvPolynomial.coeff_homogeneousComponent,
    entryExponent_degree n row column]

/-- The catalecticant linear-map feature factors through the critical
homogeneous component. -/
theorem feature_homogeneousComponent
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K) :
    SumOfTerms.Waring.feature K n
        (MvPolynomial.homogeneousComponent (2 * n) polynomial) =
      SumOfTerms.Waring.feature K n polynomial := by
  simp [SumOfTerms.Waring.feature,
    catalecticant_homogeneousComponent n polynomial]

/-- Vanishing of the critical homogeneous component is the exact structural
invisibility condition needed by the feature. -/
theorem feature_eq_zero_of_homogeneousComponent_eq_zero
    [Field K]
    (n : Nat)
    (polynomial : MvPolynomial (Fin (2 * n)) K)
    (invisible : MvPolynomial.homogeneousComponent (2 * n) polynomial = 0) :
    SumOfTerms.Waring.feature K n polynomial = 0 := by
  rw [← feature_homogeneousComponent n polynomial, invisible]
  exact LinearMap.map_zero _

/-- A Waring linear form is homogeneous of degree one. -/
theorem linearForm_isHomogeneous
    [CommSemiring K]
    (term : SumOfTerms.Waring.Term K n) :
    (SumOfTerms.Waring.linearForm term).IsHomogeneous 1 := by
  classical
  unfold SumOfTerms.Waring.linearForm
  apply MvPolynomial.IsHomogeneous.sum
  intro index _
  rw [MvPolynomial.smul_eq_C_mul]
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- A charged Waring term is homogeneous of the critical degree. -/
theorem termValue_isHomogeneous
    [CommSemiring K]
    (term : SumOfTerms.Waring.Term K n) :
    (SumOfTerms.Waring.termValue term).IsHomogeneous (2 * n) := by
  unfold SumOfTerms.Waring.termValue
  simpa using ((linearForm_isHomogeneous term).pow (2 * n)).C_mul term.scale

/-- Projecting a Waring term to the critical homogeneous component leaves it
unchanged. -/
theorem homogeneousComponent_termValue
    [CommSemiring K]
    (term : SumOfTerms.Waring.Term K n) :
    MvPolynomial.homogeneousComponent (2 * n)
        (SumOfTerms.Waring.termValue term) =
      SumOfTerms.Waring.termValue term :=
  MvPolynomial.homogeneousComponent_eq_self (termValue_isHomogeneous term)

/-- Layer-exact ordinary-circuit restriction: the critical homogeneous
component of each multiplication output is either zero or one Waring term.
All off-layer terms are unrestricted. -/
def CriticalLayerOrPowerAtMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin (2 * n)) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K) →
    MvPolynomial.homogeneousComponent (2 * n)
        (arguments (0 : Fin 2) * arguments (1 : Fin 2)) = 0 ∨
      ∃ term : SumOfTerms.Waring.Term K n,
        MvPolynomial.homogeneousComponent (2 * n)
            (arguments (0 : Fin 2) * arguments (1 : Fin 2)) =
          SumOfTerms.Waring.termValue term

/-- Structural ordinary-circuit restriction: each multiplication output is
either below the critical degree or one scalar multiple of a `2n`-th power of
a linear form. -/
def LowDegreeOrPowerAtMultiplications
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1) : Prop :=
  ∀ arguments : Fin 2 → MvPolynomial (Fin (2 * n)) K,
    (⟨.mul, arguments⟩ : Atom (Algebraic.Arithmetic.signature C)
      (MvPolynomial (Fin (2 * n)) K)) ∈
        circuitAtoms circuit
          (Algebraic.Arithmetic.interpretation
            (fun scalar => MvPolynomial.C (constant scalar)))
          (MvPolynomial.X : Fin (2 * n) →
            MvPolynomial (Fin (2 * n)) K) →
    (arguments (0 : Fin 2) * arguments (1 : Fin 2)).totalDegree < 2 * n ∨
      ∃ term : SumOfTerms.Waring.Term K n,
        arguments (0 : Fin 2) * arguments (1 : Fin 2) =
          SumOfTerms.Waring.termValue term

/-- The total-degree restriction is a special case of the layer-exact
restriction. -/
theorem criticalLayerOrPower_of_lowDegreeOrPower
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    CriticalLayerOrPowerAtMultiplications constant n circuit := by
  intro arguments present
  rcases restricted arguments present with small | ⟨term, power⟩
  · exact Or.inl (MvPolynomial.homogeneousComponent_eq_zero _ _ small)
  · right
    refine ⟨term, ?_⟩
    rw [power]
    exact homogeneousComponent_termValue term

/-- Layer-exact critical components give atom-level catalecticant rank at
most one. -/
theorem multiplicationOutputRankAtMost_one_of_criticalLayerOrPower
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : CriticalLayerOrPowerAtMultiplications constant n circuit) :
    MultiplicationOutputRankAtMost constant n positive circuit 1 := by
  intro arguments present
  change LinearMap.rank
    (SumOfTerms.Waring.feature K n
      (arguments (0 : Fin 2) * arguments (1 : Fin 2))) ≤ 1
  rw [← feature_homogeneousComponent n]
  rcases restricted arguments present with invisible | ⟨term, powerTerm⟩
  · rw [invisible]
    simp
  · rw [powerTerm]
    exact SumOfTerms.Waring.term_rank_le_one term

/-- Every layer-exact critical-component circuit for the squarefree target
needs central-binomial multiplication cost. -/
theorem criticalLayer_multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : CriticalLayerOrPowerAtMultiplications constant n circuit) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  rankOne_multiplication_lowerBound constant n positive circuit constructs
    (localRankAtMost_of_multiplicationOutputRankAtMost constant n positive
      circuit 1
        (multiplicationOutputRankAtMost_one_of_criticalLayerOrPower constant n
          positive circuit restricted))

/-- Explicit exponential size lower bound for the layer-exact
critical-component circuit class. -/
theorem criticalLayer_four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : CriticalLayerOrPowerAtMultiplications constant n circuit) :
    4 ^ n < n * circuit.size :=
  (Nat.four_pow_lt_mul_centralBinom n n_big).trans_le
    (Nat.mul_le_mul_left n
      ((criticalLayer_multiplication_lowerBound constant n (by omega) circuit
        constructs restricted).trans
          ((Combined.circuit_multiplicationCost_le_gateCost circuit).trans
            (Combined.circuit_gateCost_le_size circuit))))

/-- The structural degree-or-power restriction implies the semantic
power-or-invisible restriction. -/
theorem powerOrInvisible_of_lowDegreeOrPower
    [Field K]
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    PowerOrInvisibleAtMultiplications constant n circuit := by
  intro arguments present
  rcases restricted arguments present with small | power
  · exact Or.inl (feature_eq_zero_of_totalDegree_lt n _ small)
  · exact Or.inr power

/-- Degree-or-power multiplication outputs have catalecticant rank at most
one. -/
theorem multiplicationOutputRankAtMost_one_of_lowDegreeOrPower
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    MultiplicationOutputRankAtMost constant n positive circuit 1 :=
  multiplicationOutputRankAtMost_one_of_powerOrInvisible constant n positive
    circuit
      (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

/-- Every degree-or-power ordinary arithmetic circuit for the squarefree
target needs central-binomial multiplication cost. -/
theorem multiplication_lowerBound
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (positive : 0 < n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    Nat.centralBinom n ≤
      circuit.cost
        (Algebraic.Arithmetic.multiplicationCost (K := C)) :=
  powerOrInvisible_multiplication_lowerBound constant n positive circuit
    constructs
      (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

/-- Explicit exponential size lower bound for the structural degree-or-power
ordinary arithmetic circuit subclass. -/
theorem four_pow_lt_mul_size
    [Field K]
    [CharZero K]
    (constant : C → K)
    (n : Nat)
    (n_big : 4 ≤ n)
    (circuit : Circuit (Algebraic.Arithmetic.signature C) (2 * n) g 1)
    (constructs : (problem K n).Constructs circuit
      (Algebraic.Arithmetic.interpretation
        (fun scalar => MvPolynomial.C (constant scalar))))
    (restricted : LowDegreeOrPowerAtMultiplications constant n circuit) :
    4 ^ n < n * circuit.size :=
  powerOrInvisible_four_pow_lt_mul_size constant n n_big circuit constructs
    (powerOrInvisible_of_lowDegreeOrPower constant n circuit restricted)

end
end Degree
end Catalecticant
end Polynomial
end Interaction
end Arithmetic
end Fusion
end Algebraic
