/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Monomials.Defs
public import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Base-digit reconstruction and exact monomial substitution

The division algorithm reconstructs each integer below `h^m` from exactly
`m` digits. Substituting powers with weights `h^i` therefore recovers the
distinct powers indexed by the original `Fin K`, with degree strictly below
`K` even when `K` is smaller than `h^m`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem monomialDigit_lt {h j m : Nat} (positive : 0 < h) (i : Fin m) :
    monomialDigit h j i < h := Nat.mod_lt _ positive

private theorem digit_sum_carry (h j m : Nat) :
    (∑ i ∈ Finset.range m, (j / h ^ i % h) * h ^ i) + j / h ^ m * h ^ m = j := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      calc
        _ = (∑ i ∈ Finset.range m, (j / h ^ i % h) * h ^ i) +
            (j / h ^ m % h + h * (j / h ^ m / h)) * h ^ m := by
              rw [Nat.div_div_eq_div_mul]
              ring
        _ = (∑ i ∈ Finset.range m, (j / h ^ i % h) * h ^ i) +
            j / h ^ m * h ^ m := by rw [Nat.mod_add_div]
        _ = j := ih

theorem sum_monomialDigit_mul_pow {h j m : Nat} (bound : j < h ^ m) :
    (∑ i : Fin m, monomialDigit h j i * h ^ i.val) = j := by
  simpa only [Finset.sum_range, Nat.div_eq_of_lt bound, Nat.zero_mul, Nat.add_zero,
    monomialDigit] using digit_sum_carry h j m

theorem sum_monomialDigit_le {h j m : Nat} (positive : 0 < h) :
    (∑ i : Fin m, monomialDigit h j i) ≤ m * (h - 1) := by
  calc
    (∑ i : Fin m, monomialDigit h j i) ≤ ∑ _i : Fin m, (h - 1) := by
      apply Finset.sum_le_sum
      intro i _
      have := monomialDigit_lt (j := j) positive i
      lia
    _ = m * (h - 1) := by simp

theorem digitMonomial_pow {R : Type*} [CommMonoid R] {h j m : Nat}
    (bound : j < h ^ m) (u : R) :
    digitMonomial h j (fun i : Fin m => u ^ (h ^ i.val)) = u ^ j := by
  simp only [digitMonomial, ← pow_mul, Nat.mul_comm (h ^ _) (monomialDigit h j _),
    Finset.prod_pow_eq_pow_sum, sum_monomialDigit_mul_pow bound]

theorem digitMonomial_substitution {R : Type*} [CommSemiring R] {h K m : Nat}
    (bound : K ≤ h ^ m) (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.C (a j) *
      digitMonomial h j.val (fun i : Fin m => Polynomial.X ^ (h ^ i.val))) =
        ∑ j : Fin K, Polynomial.monomial j.val (a j) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [digitMonomial_pow (j.isLt.trans_le bound), Polynomial.C_mul_X_pow_eq_monomial]

theorem fin_monomial_sum_eq_ofFn {R : Type*} [Semiring R] [DecidableEq R]
    {K : Nat} (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) = Polynomial.ofFn K a :=
  (Polynomial.ofFn_eq_sum_monomial a).symm

theorem fin_monomial_sum_coeff {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) (j : Fin K) :
    (∑ i : Fin K, Polynomial.monomial i.val (a i)).coeff j.val = a j := by
  classical
  rw [fin_monomial_sum_eq_ofFn]
  exact Polynomial.ofFn_coeff_eq_val_of_lt a j.isLt

theorem fin_monomial_sum_degree_lt {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)).degree < K := by
  classical
  rw [fin_monomial_sum_eq_ofFn]
  exact Polynomial.ofFn_degree_lt a

theorem fin_monomial_sum_ne_zero_iff {R : Type*} [Semiring R] {K : Nat}
    (a : Fin K → R) :
    (∑ j : Fin K, Polynomial.monomial j.val (a j)) ≠ 0 ↔ ∃ j, a j ≠ 0 := by
  classical
  constructor
  · intro nonzero
    by_contra h
    simp only [not_exists, not_not] at h
    apply nonzero
    simp only [h, map_zero, Finset.sum_const_zero]
  · rintro ⟨j, hj⟩ zero
    apply hj
    rw [← fin_monomial_sum_coeff a j, zero, Polynomial.coeff_zero]

end Algebraic.Cutwidth.Extractor.Internal
