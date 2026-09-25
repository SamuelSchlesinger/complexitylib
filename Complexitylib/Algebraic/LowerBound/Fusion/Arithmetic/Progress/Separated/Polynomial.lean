/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.Arithmetic.Progress.Separated.Addition

/-!
# Coefficient-one polynomials from finite monomial families

This module turns any finite family of exponent vectors into the polynomial
having exactly those monomials, each with coefficient one.  It is the reusable
bridge from finite separated-family arguments to arithmetic circuit lower
bounds; concrete families need only prove their finite support is separated.
-/

@[expose] public section

namespace Algebraic
namespace Fusion
namespace Arithmetic
namespace Progress
namespace Separated
namespace Polynomial

noncomputable section

/-- The natural-coefficient polynomial with exactly the given exponent
vectors, each occurring with coefficient one. -/
def ofSupport
    (support : Finset (Variable →₀ ℕ)) : MvPolynomial Variable ℕ :=
  ∑ exponent ∈ support, MvPolynomial.monomial exponent 1

/-- `ofSupport` has exactly its specified monomial support. -/
@[simp] theorem support_ofSupport
    (support : Finset (Variable →₀ ℕ)) :
    (ofSupport support).support = support := by
  classical
  rw [ofSupport, Expansion.support_finset_sum]
  simp_rw [MvPolynomial.support_monomial,
    ite_eq_right (one_ne_zero : (1 : ℕ) ≠ 0)]
  exact Finset.biUnion_singleton_eq_self

/-- Coefficients of `ofSupport` are the characteristic function of the
specified support. -/
@[simp] theorem coeff_ofSupport
    [DecidableEq Variable]
    (support : Finset (Variable →₀ ℕ))
    (exponent : Variable →₀ ℕ) :
    AddMonoidAlgebra.coeff (ofSupport support) exponent =
      if exponent ∈ support then 1 else 0 := by
  classical
  rw [ofSupport, MvPolynomial.coeff_sum]
  simp

/-- Every specified monomial has coefficient one. -/
theorem coeff_ofSupport_of_mem
    [DecidableEq Variable]
    {support : Finset (Variable →₀ ℕ)}
    {exponent : Variable →₀ ℕ}
    (present : exponent ∈ support) :
    AddMonoidAlgebra.coeff (ofSupport support) exponent = 1 := by
  simp [present]

/-- A separated finite family yields its cardinality-minus-one addition
lower bound for every constant-free monotone arithmetic circuit computing its
coefficient-one polynomial. -/
theorem circuit_addition_lowerBound
    (support : Finset (Fin n →₀ ℕ))
    (separated : IsSeparated support support)
    (circuit : Circuit
      (Algebraic.Arithmetic.signature PEmpty) n 1)
    (constructs :
      ({ inputCount := n, inputs := MvPolynomial.X,
          target := ofSupport support } :
        Problem (MvPolynomial (Fin n) ℕ)).Constructs circuit
          (polynomialInterpretation (Fin n))) :
    support.card - 1 ≤
      circuit.cost
        (Algebraic.Arithmetic.additionCost (K := PEmpty)) := by
  have targetSeparated : IsSeparated
      (ofSupport support).support (ofSupport support).support := by
    simpa using separated
  have coefficientsOne : ∀ exponent ∈ (ofSupport support).support,
      AddMonoidAlgebra.coeff (ofSupport support) exponent = 1 := by
    intro exponent present
    simp at present ⊢
    exact present
  have bound := Addition.circuit_addition_lowerBound_of_unitSeparated
    (ofSupport support) targetSeparated coefficientsOne circuit constructs
  simpa using bound

end
end Polynomial
end Separated
end Progress
end Arithmetic
end Fusion
end Algebraic
