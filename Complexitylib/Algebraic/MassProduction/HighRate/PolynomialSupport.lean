/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.LowDegree
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Polynomial support after Frobenius powers

In characteristic two, every exponent appearing in a `2^r`-th power is
divisible by `2^r`. Multiplication by a low-degree polynomial therefore
leaves the residue of each supported exponent bounded by that low degree.
-/

@[expose] public section

namespace Algebraic.MassProduction.HighRate

open scoped BigOperators

variable {K : Type*} [Field K] [CharP K 2]

/-- Frobenius powers have support only at multiples of the power. -/
theorem dvdOfMemSupportPowTwo
    (polynomial : Polynomial K) (width exponent : Nat)
    (inSupport : exponent ∈ (polynomial ^ 2 ^ width).support) :
    2 ^ width ∣ exponent := by
  classical
  have nonzero := Polynomial.mem_support_iff.mp inSupport
  rw [← Polynomial.map_iterateFrobenius_expand 2 polynomial width,
    Polynomial.coeff_map, Polynomial.coeff_expand (by positivity)] at nonzero
  by_contra notDivisible
  simp only [ite_eq_right notDivisible, map_zero, ne_eq, not_true_eq_false] at nonzero

/-- A low-degree factor bounds the residue of every supported exponent
after multiplication by a Frobenius power. -/
theorem residueLeNatDegreeOfMemSupportMulPowTwo
    (low high : Polynomial K) (width exponent : Nat)
    (inSupport : exponent ∈ (low * high ^ 2 ^ width).support) :
    exponent % 2 ^ width ≤ low.natDegree := by
  classical
  have nonzero := Polynomial.mem_support_iff.mp inSupport
  rw [Polynomial.coeff_mul] at nonzero
  obtain ⟨pair, inAntidiagonal, termNonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  have lowNonzero := left_ne_zero_of_mul termNonzero
  have highNonzero := right_ne_zero_of_mul termNonzero
  have divides := dvdOfMemSupportPowTwo high width pair.2
    (Polynomial.mem_support_iff.mpr highNonzero)
  have sumEquation := Finset.mem_antidiagonal.mp inAntidiagonal
  calc
    exponent % 2 ^ width = pair.1 % 2 ^ width := by
      rw [← sumEquation, Nat.add_mod, Nat.mod_eq_zero_of_dvd divides]
      simp
    _ ≤ pair.1 := Nat.mod_le _ _
    _ ≤ low.natDegree := Polynomial.le_natDegree_of_ne_zero lowNonzero

end Algebraic.MassProduction.HighRate
