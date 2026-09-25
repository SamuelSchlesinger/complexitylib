/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.MultiplicativeShadow.Polynomial
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Interaction.Hessian.Pairwise

/-!
# Two-shadow bounds for shifted pairwise products

Request all polynomials `1 + x_i y_j` from two blocks of `n` variables.  The
quadratic coefficient or Hessian shadow forces `n^2` multiplications.  After a
suitable affine one-variable specialization, the distinct linear factors of
the same outputs give `n^2` independent root-multiplicity shadows and force
`n^2` additions.  The two component bounds add, giving `2 n^2` nonconstant
gates.

The general theorem leaves the elementary choice of specialization parameters
explicit.  Its hypotheses say that the `n^2` resulting roots are distinct and
avoid the roots of the specialized free inputs.  A second endpoint supplies
such parameters over the rationals for every `n`.

The circuits here use addition, multiplication, and named constants, without
division.  The additive ingredient is the classical addition-rank method; this
file records a checked two-shadow corollary, not a claim of historical
priority.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace MultiplicativeShadow
namespace Pairwise

open scoped Polynomial

noncomputable section

variable {K : Type} [Field K]

/-- Pairwise products with a constant term adjoined. -/
def targets
    (K : Type)
    [Field K]
    (n : Nat) :
    Fin (n * n) → MvPolynomial (Fin n ⊕ Fin n) K :=
  fun output ↦ 1 + Interaction.Hessian.Pairwise.targets K n output

/-- Specialize every left variable to a scalar and every right variable to an
affine copy of the univariate indeterminate. -/
def specialization
    (leftValue rightOffset : Fin n → K) :
    MvPolynomial (Fin n ⊕ Fin n) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C <| Sum.elim
    (fun left ↦ Polynomial.C (leftValue left))
    (fun right ↦ Polynomial.X + Polynomial.C (rightOffset right))

@[simp] theorem specialization_C
    (leftValue rightOffset : Fin n → K)
    (scalar : K) :
    specialization leftValue rightOffset (MvPolynomial.C scalar) =
      Polynomial.C scalar := by
  simp [specialization]

@[simp] theorem specialization_X_inl
    (leftValue rightOffset : Fin n → K)
    (left : Fin n) :
    specialization leftValue rightOffset (MvPolynomial.X (Sum.inl left)) =
      Polynomial.C (leftValue left) := by
  simp [specialization]

@[simp] theorem specialization_X_inr
    (leftValue rightOffset : Fin n → K)
    (right : Fin n) :
    specialization leftValue rightOffset (MvPolynomial.X (Sum.inr right)) =
      Polynomial.X + Polynomial.C (rightOffset right) := by
  simp [specialization]

/-- Root of the specialized shifted product indexed by `output`. -/
def rootPoints
    (leftValue rightOffset : Fin n → K)
    (output : Fin (n * n)) : K :=
  -((leftValue (finProdFinEquiv.symm output).1)⁻¹) -
    rightOffset (finProdFinEquiv.symm output).2

/-- Explicit rational specialization: the reciprocal of the left value is a
positive block offset, while the right offset is its coordinate index. -/
def rationalLeftValue (n : Nat) (left : Fin n) : ℚ :=
  ((n * (left.1 + 1) : Nat) : ℚ)⁻¹

/-- Right offsets for the explicit rational specialization. -/
def rationalRightOffset (right : Fin n) : ℚ :=
  right.1

/-- The explicit root indexed by an output is just the negative of its
one-based flattened index shifted by one full block. -/
theorem rational_rootPoints
    (n : Nat)
    (output : Fin (n * n)) :
    rootPoints (rationalLeftValue n) rationalRightOffset output =
      -((output.1 + n : Nat) : ℚ) := by
  have pair_eq : finProdFinEquiv.symm output =
      (output.divNat, output.modNat) := rfl
  simp only [rootPoints, rationalLeftValue, rationalRightOffset, inv_inv]
  rw [pair_eq]
  simp only [Fin.divNat, Fin.modNat]
  change -((n * (output.1 / n + 1) : Nat) : ℚ) -
      ((output.1 % n : Nat) : ℚ) = -((output.1 + n : Nat) : ℚ)
  have flatIndex :
      n * (output.1 / n + 1) + output.1 % n = output.1 + n := by
    calc
      n * (output.1 / n + 1) + output.1 % n =
          (output.1 % n + n * (output.1 / n)) + n := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      _ = output.1 + n := by rw [Nat.mod_add_div]
  have flatIndexCast :
      ((n * (output.1 / n + 1) + output.1 % n : Nat) : ℚ) =
        ((output.1 + n : Nat) : ℚ) := by
    exact_mod_cast flatIndex
  push_cast at flatIndexCast ⊢
  linarith

/-- All explicit rational left values are nonzero. -/
theorem rationalLeftValue_ne_zero
    (left : Fin n) :
    rationalLeftValue n left ≠ 0 := by
  have nPositive : 0 < n := Nat.zero_lt_of_lt left.isLt
  apply inv_ne_zero
  exact_mod_cast Nat.mul_ne_zero (Nat.ne_of_gt nPositive)
    (Nat.succ_ne_zero left.1)

/-- Distinct outputs receive distinct explicit rational roots. -/
theorem rational_rootPoints_injective
    (n : Nat) :
    Function.Injective
      (rootPoints (rationalLeftValue n) rationalRightOffset) := by
  intro left right equal
  rw [rational_rootPoints, rational_rootPoints] at equal
  apply Fin.ext
  norm_num at equal ⊢
  omega

/-- Explicit target roots never hit a root of a specialized right input. -/
theorem rational_rootPoints_avoidRight
    (output : Fin (n * n))
    (right : Fin n) :
    rootPoints (rationalLeftValue n) rationalRightOffset output ≠
      -rationalRightOffset right := by
  rw [rational_rootPoints]
  simp only [rationalRightOffset]
  intro equal
  have castEqual : ((output.1 + n : Nat) : ℚ) = (right.1 : ℚ) := by
    exact neg_injective equal
  have naturalEqual : output.1 + n = right.1 := by
    exact_mod_cast castEqual
  omega

/-- The shifted product specializes to a nonzero scalar times its designated
linear factor. -/
theorem specialization_target
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (output : Fin (n * n)) :
    specialization leftValue rightOffset (targets K n output) =
      Polynomial.C
          (leftValue (finProdFinEquiv.symm output).1) *
        (Polynomial.X - Polynomial.C
          (rootPoints leftValue rightOffset output)) := by
  rw [targets, Interaction.Hessian.Pairwise.targets]
  simp only [map_add, map_one, map_mul, specialization_X_inl,
    specialization_X_inr]
  simp [rootPoints]
  ring_nf
  have inverse_cancel :
      Polynomial.C (leftValue output.divNat) *
          Polynomial.C ((leftValue output.divNat)⁻¹) =
        (1 : K[X]) := by
    rw [← Polynomial.C_mul,
      mul_inv_cancel₀ (left_ne_zero output.divNat)]
    simp
  rw [inverse_cancel]
  ring

/-- The specialized free inputs have no selected roots. -/
theorem input_rootMultiplicity_eq_zero
    (leftValue rightOffset : Fin n → K)
    (avoidRightRoots : ∀ output right,
      rootPoints leftValue rightOffset output ≠ -rightOffset right)
    (input : Fin (2 * n))
    (output : Fin (n * n)) :
    Polynomial.rootMultiplicity (rootPoints leftValue rightOffset output)
      (specialization leftValue rightOffset
        ((Interaction.Hessian.Pairwise.inputProblem K n).inputs input)) = 0 := by
  classical
  change Polynomial.rootMultiplicity
    (rootPoints leftValue rightOffset output)
    (specialization leftValue rightOffset
      (MvPolynomial.X
        (Interaction.Hessian.Pairing.variableEquiv n input))) = 0
  generalize variable_eq :
    Interaction.Hessian.Pairing.variableEquiv n input = sourceVariable
  cases sourceVariable with
  | inl left => simp
  | inr right =>
      have avoid := avoidRightRoots output right
      rw [specialization_X_inr]
      rw [show Polynomial.X + Polynomial.C (rightOffset right) =
        Polynomial.X - Polynomial.C (-rightOffset right) by simp]
      rw [Polynomial.rootMultiplicity_X_sub_C]
      simp [avoid]

/-- Root-multiplicity shadow certificate on the original multivariate
polynomial problem, obtained by pulling the univariate certificate back along
the specialization. -/
def additionCertificate
    (constant : C → K)
    (n : Nat)
    (leftValue rightOffset : Fin n → K)
    (avoidRightRoots : ∀ output right,
      rootPoints leftValue rightOffset output ≠ -rightOffset right) :
    Certificate (K := K) (Q := Fin (n * n) → K)
      (fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem K n) := by
  let sourceProblem := Interaction.Hessian.Pairwise.inputProblem K n
  let map := specialization leftValue rightOffset
  let mappedProblem := sourceProblem.map map
  let inputRootFree : ∀ input output,
      (mappedProblem.inputs input).rootMultiplicity
        (rootPoints leftValue rightOffset output) = 0 := by
    intro input output
    exact input_rootMultiplicity_eq_zero leftValue rightOffset
      avoidRightRoots input output
  let imageCertificate := RootMultiplicity.certificate constant mappedProblem
    (rootPoints leftValue rightOffset) inputRootFree
  exact imageCertificate.comap
    (fun scalar ↦ MvPolynomial.C (constant scalar))
    (fun scalar ↦ Polynomial.C (constant scalar)) sourceProblem map
    map.map_mul (fun scalar ↦ specialization_C leftValue rightOffset _)

/-- The target root-multiplicity shadows are the standard basis vectors. -/
theorem targetFeatures_eq_single
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (roots_injective : Function.Injective
      (rootPoints leftValue rightOffset))
    (output : Fin (n * n)) :
    RootMultiplicity.rootMultiplicityFeature
        (rootPoints leftValue rightOffset)
        (specialization leftValue rightOffset (targets K n output)) =
      Pi.single output 1 := by
  classical
  rw [specialization_target leftValue rightOffset left_ne_zero output]
  funext coordinate
  have scalar_ne_zero : Polynomial.C
      (leftValue (finProdFinEquiv.symm output).1) ≠ (0 : K[X]) := by
    exact Polynomial.C_ne_zero.mpr
      (left_ne_zero (finProdFinEquiv.symm output).1)
  have factor_ne_zero : Polynomial.X - Polynomial.C
      (rootPoints leftValue rightOffset output) ≠ (0 : K[X]) :=
    Polynomial.X_sub_C_ne_zero _
  rw [show RootMultiplicity.rootMultiplicityFeature
      (rootPoints leftValue rightOffset)
      (Polynomial.C (leftValue (finProdFinEquiv.symm output).1) *
        (Polynomial.X - Polynomial.C
          (rootPoints leftValue rightOffset output))) coordinate =
      (((Polynomial.C
          (leftValue (finProdFinEquiv.symm output).1) *
        (Polynomial.X - Polynomial.C
          (rootPoints leftValue rightOffset output))).rootMultiplicity
            (rootPoints leftValue rightOffset coordinate) : Nat) : K) by rfl]
  rw [Polynomial.rootMultiplicity_mul
    (mul_ne_zero scalar_ne_zero factor_ne_zero)]
  simp only [Polynomial.rootMultiplicity_C, zero_add,
    Polynomial.rootMultiplicity_X_sub_C, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  by_cases equal : coordinate = output
  · subst coordinate
    simp
  · have roots_ne : rootPoints leftValue rightOffset coordinate ≠
        rootPoints leftValue rightOffset output :=
      fun roots_eq ↦ equal (roots_injective roots_eq)
    simp [roots_ne, equal]

/-- The target divisor shadows are linearly independent. -/
theorem targetFeatures_linearIndependent
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (roots_injective : Function.Injective
      (rootPoints leftValue rightOffset)) :
    LinearIndependent K
      (RootMultiplicity.rootMultiplicityFeature
        (rootPoints leftValue rightOffset) ∘
          specialization leftValue rightOffset ∘ targets K n) := by
  have feature_eq :
      RootMultiplicity.rootMultiplicityFeature
          (rootPoints leftValue rightOffset) ∘
            specialization leftValue rightOffset ∘ targets K n =
        fun output ↦ Pi.single output (1 : K) := by
    funext output
    exact targetFeatures_eq_single leftValue rightOffset left_ne_zero
      roots_injective output
  rw [feature_eq]
  exact Pi.linearIndependent_single_one (Fin (n * n)) K

/-- The Hessian shadows of shifted pairwise products are unchanged by the
constant term and remain linearly independent. -/
theorem hessianFeatures_linearIndependent
    (point : (Fin n ⊕ Fin n) → K) :
    LinearIndependent K
      (Interaction.Hessian.linearMap point ∘ targets K n) := by
  have independent :=
    Interaction.Hessian.Pairwise.targetFeatures_linearIndependent
      (K := K) point
  have oneFeature : Interaction.Hessian.linearMap point
      (1 : MvPolynomial (Fin n ⊕ Fin n) K) = 0 := by
    simpa using Interaction.Hessian.linearMap_C point 1
  convert independent using 1
  funext output
  simp [targets, oneFeature]

/-- Computing all shifted pairwise products requires `n^2` additions. -/
theorem circuit_addition_lowerBound
    (constant : C → K)
    (n : Nat)
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (roots_injective : Function.Injective
      (rootPoints leftValue rightOffset))
    (avoidRightRoots : ∀ output right,
      rootPoints leftValue rightOffset output ≠ -rightOffset right)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem K n) (targets K n) circuit) :
    n * n ≤ circuit.cost
      (Algebraic.Arithmetic.additionCost (K := C)) := by
  let certificate := additionCertificate constant n leftValue rightOffset
    avoidRightRoots
  apply circuit_addition_lowerBound_of_linearIndependent certificate
    (targets K n) ?_ circuit constructs
  change LinearIndependent K
    (RootMultiplicity.rootMultiplicityFeature
      (rootPoints leftValue rightOffset) ∘
        specialization leftValue rightOffset ∘ targets K n)
  exact targetFeatures_linearIndependent leftValue rightOffset left_ne_zero
    roots_injective

/-- Computing all shifted pairwise products requires `n^2` multiplications. -/
theorem circuit_multiplication_lowerBound
    (constant : C → K)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem K n) (targets K n) circuit) :
    n * n ≤ circuit.cost
      (Algebraic.Arithmetic.multiplicationCost (K := C)) := by
  let point : (Fin n ⊕ Fin n) → K := 0
  apply Interaction.Multiple.circuit_multiplication_lowerBound_of_linearIndependent
    (Interaction.Hessian.Pairwise.interactionCertificate constant n point)
    (targets K n)
  · change LinearIndependent K
      (Interaction.Hessian.linearMap point ∘ targets K n)
    exact hessianFeatures_linearIndependent point
  · exact constructs

/-- The two independent shadows add to an exact-form `2 n^2` lower bound on
nonconstant arithmetic gates. -/
theorem circuit_gate_lowerBound
    (constant : C → K)
    (n : Nat)
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (roots_injective : Function.Injective
      (rootPoints leftValue rightOffset))
    (avoidRightRoots : ∀ output right,
      rootPoints leftValue rightOffset output ≠ -rightOffset right)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem K n) (targets K n) circuit) :
    n * n + n * n ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) := by
  apply Combined.circuit_gate_lowerBound_of_components circuit
  · exact circuit_addition_lowerBound constant n leftValue rightOffset
      left_ne_zero roots_injective avoidRightRoots circuit constructs
  · exact circuit_multiplication_lowerBound constant n circuit constructs

/-- The raw circuit size obeys the same two-shadow lower bound. -/
theorem circuit_size_lowerBound
    (constant : C → K)
    (n : Nat)
    (leftValue rightOffset : Fin n → K)
    (left_ne_zero : ∀ left, leftValue left ≠ 0)
    (roots_injective : Function.Injective
      (rootPoints leftValue rightOffset))
    (avoidRightRoots : ∀ output right,
      rootPoints leftValue rightOffset output ≠ -rightOffset right)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem K n) (targets K n) circuit) :
    n * n + n * n ≤ circuit.size :=
  (circuit_gate_lowerBound constant n leftValue rightOffset left_ne_zero
      roots_injective avoidRightRoots circuit constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

/-- Unconditional rational-field instance of the two-shadow gate bound. -/
theorem rational_circuit_gate_lowerBound
    (constant : C → ℚ)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem ℚ n) (targets ℚ n)
      circuit) :
    n * n + n * n ≤
      circuit.cost (Algebraic.Arithmetic.gateCost (K := C)) := by
  exact circuit_gate_lowerBound constant n (rationalLeftValue n)
    rationalRightOffset rationalLeftValue_ne_zero
    (rational_rootPoints_injective n)
    rational_rootPoints_avoidRight circuit constructs

/-- Unconditional rational-field instance of the two-shadow size bound. -/
theorem rational_circuit_size_lowerBound
    (constant : C → ℚ)
    (n : Nat)
    (circuit : Circuit (Algebraic.Arithmetic.signature C)
      (2 * n) g (n * n))
    (constructs : Interaction.Multiple.Constructs
      (constant := fun scalar ↦ MvPolynomial.C (constant scalar))
      (Interaction.Hessian.Pairwise.inputProblem ℚ n) (targets ℚ n)
      circuit) :
    n * n + n * n ≤ circuit.size :=
  (rational_circuit_gate_lowerBound constant n circuit constructs).trans
    (Combined.circuit_gateCost_le_size circuit)

end
end Pairwise
end MultiplicativeShadow
end Arithmetic
end Fusion
end Algebraic
