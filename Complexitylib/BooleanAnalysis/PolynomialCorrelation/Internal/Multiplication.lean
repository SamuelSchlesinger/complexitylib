/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.BooleanAnalysis.PolynomialCorrelation.Internal.Filtration

/-!
# The polynomial multiplication lemma

The ordinary total degree is Mathlib's `MvPolynomial.totalDegree`. Expanding
over the polynomial's support avoids any assumptions about cancellation.
-/

public section

namespace Complexity.BooleanAnalysis.PolynomialCorrelation.Internal

open Finset

variable {k m r : ℕ}

theorem variable_pow_mul_mem {f : BlockCube k m → ZMod 2}
    (hf : f ∈ filtration k m r) (i : Fin k) (j : Fin (2 * m + 1)) (d : ℕ) :
    (fun x => monomial {j} (x i) ^ d * f x) ∈ filtration k m (r + d) := by
  induction d with
  | zero => simpa using hf
  | succ d ih =>
    simpa [pow_succ, mul_left_comm, mul_comm, mul_assoc, Nat.add_assoc] using
      variable_mul_mem ih i j

theorem variable_prod_mul_mem {f : BlockCube k m → ZMod 2}
    (hf : f ∈ filtration k m r) (s : Finset (Fin k × Fin (2 * m + 1)))
    (e : Fin k × Fin (2 * m + 1) → ℕ) :
    (fun x => (∏ ij ∈ s, monomial {ij.2} (x ij.1) ^ e ij) * f x) ∈
      filtration k m (r + ∑ ij ∈ s, e ij) := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | @insert ij s hij ih =>
    simpa [prod_insert hij, sum_insert hij, mul_assoc, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using variable_pow_mul_mem ih ij.1 ij.2 (e ij)

/-- Multiplication by a degree-`d` polynomial increases modified degree by at most `d`. -/
theorem polynomial_mul_mem {f : BlockCube k m → ZMod 2}
    (hf : f ∈ filtration k m r)
    (p : MvPolynomial (Fin k × Fin (2 * m + 1)) (ZMod 2)) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (fun x => polynomialEval p x * f x) ∈ filtration k m (r + d) := by
  classical
  have heq : (fun x => polynomialEval p x * f x) =
      ∑ e ∈ p.support, p.coeff e •
        (fun x => (∏ ij ∈ e.support, monomial {ij.2} (x ij.1) ^ e ij) * f x) := by
    ext x
    conv_lhs => rw [MvPolynomial.as_sum p]
    simp only [polynomialEval, MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_assoc, Finsupp.prod]
    congr 1
    funext e
    simp only [monomial, singleton_subset_iff, blockBits]
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem
  exact filtration_mono (Nat.add_le_add_left ((MvPolynomial.le_totalDegree he).trans hp) r)
    (variable_prod_mul_mem hf e.support e)

end Complexity.BooleanAnalysis.PolynomialCorrelation.Internal
