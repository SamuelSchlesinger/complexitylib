/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialThreshold.Internal.Bridge

/-!
# Multilinear normal form on the sign cube

Reducing exponents modulo two preserves evaluation at signs, produces a
multilinear polynomial, and never increases total degree. This removes the
multilinearity hypothesis from the imported Gotsman--Linial theorem.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialThreshold.Internal

open scoped BigOperators

theorem signMultilinearize_isMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsMultilinear (signMultilinearize p) := by
  classical
  intro m hm i
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have hma := MvPolynomial.support_monomial_subset ha
  have hma' := Finset.mem_singleton.mp hma
  subst m
  simp only [Finsupp.mapRange_apply]
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

theorem signMultilinearize_totalDegree_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (signMultilinearize p).totalDegree ≤ p.totalDegree := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hm)
  rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
  exact Finset.sum_le_sum (fun _ _ => Nat.mod_le _ _)

theorem signMultilinearize_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, x i ^ 2 = 1) :
    MvPolynomial.eval x (signMultilinearize p) = MvPolynomial.eval x p := by
  classical
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
  simp only [signMultilinearize, MvPolynomial.eval_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [Finsupp.prod_mapRange_index (fun _ => pow_zero _)]
  exact Finset.prod_congr rfl (fun i _ => (pow_eq_pow_mod (m i) (hx i)).symm)

theorem polynomialThreshold_signMultilinearize {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    BooleanAnalysis.polynomialThreshold (signMultilinearize p) =
      BooleanAnalysis.polynomialThreshold p := by
  apply BooleanFunction.ext
  intro x
  have hx (i : Fin n) : chi (x i) ^ 2 = 1 := by
    simp only [chi]
    split <;> norm_num
  change (if 0 ≤ MvPolynomial.eval _ _ then (1 : ℝ) else -1) = _
  rw [signMultilinearize_eval p _ hx]
  rfl

theorem totalInfluence_polynomialThreshold_le {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hd : p.totalDegree ≤ d) :
    totalInfluence (BooleanAnalysis.polynomialThreshold p) ≤ 8 * d * Real.sqrt n := by
  rw [← polynomialThreshold_signMultilinearize p]
  exact totalInfluence_polynomialThreshold_le_of_multilinear _
    (signMultilinearize_isMultilinear p) ((signMultilinearize_totalDegree_le p).trans hd)

end Complexity.BooleanAnalysis.PolynomialThreshold.Internal
