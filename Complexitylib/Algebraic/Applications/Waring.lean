/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Fusion.SumOfTerms.Waring

/-!
# Applying the squarefree-monomial Waring bound

A finite sum of scaled `2n`-th powers of linear forms representing the product
of `2n` variables has at least `choose (2n) n` terms. The premise is an equality
of polynomials; callers do not need to encode the sum as a circuit.

This is a lower bound on the number of power terms in this restricted
representation, not on unrestricted arithmetic circuit size.
For the source correspondence of the catalecticant argument, see the
module documentation of `Algebraic.LowerBound.Fusion.SumOfTerms.Waring`.
-/

@[expose] public section

namespace Algebraic.Applications

open scoped BigOperators

/-- A sum of scaled powers representing the squarefree monomial needs at least
the central binomial number of terms, over any characteristic-zero field. -/
theorem waringSum_lowerBound
    {K : Type} [Field K] [CharZero K] {ι : Type*}
    (n : Nat) (indices : Finset ι)
    (scale : ι → K) (coefficients : ι → Fin (2 * n) → K)
    (represents :
      ∑ i ∈ indices, MvPolynomial.C (scale i) *
          (∑ j, MvPolynomial.C (coefficients i j) * MvPolynomial.X j) ^ (2 * n) =
        ∏ j : Fin (2 * n), (MvPolynomial.X j : MvPolynomial (Fin (2 * n)) K)) :
    Nat.centralBinom n ≤ indices.card := by
  classical
  let terms (i : ι) : Fusion.SumOfTerms.Waring.Term K n :=
    { scale := scale i, coefficients := coefficients i }
  have sumEqual :
      ∑ i ∈ indices, Fusion.SumOfTerms.Waring.termValue (terms i) =
        Fusion.SumOfTerms.Waring.target K n := by
    simpa [Fusion.SumOfTerms.Waring.termValue, Fusion.SumOfTerms.Waring.linearForm,
      Fusion.SumOfTerms.Waring.target_eq_prod_X, MvPolynomial.smul_eq_C_mul, terms] using represents
  have bound : (Nat.centralBinom n : Cardinal) ≤ indices.card := calc
    _ ≤ LinearMap.rank (Fusion.SumOfTerms.Waring.feature K n
        (Fusion.SumOfTerms.Waring.target K n)) :=
      Fusion.SumOfTerms.Waring.target_rank_ge n
    _ = LinearMap.rank (∑ i ∈ indices,
        Fusion.SumOfTerms.Waring.feature K n (Fusion.SumOfTerms.Waring.termValue (terms i))) := by
      rw [← sumEqual, map_sum]
    _ ≤ ∑ i ∈ indices, LinearMap.rank (Fusion.SumOfTerms.Waring.feature K n
        (Fusion.SumOfTerms.Waring.termValue (terms i))) := LinearMap.rank_finsetSum_le _ _
    _ ≤ ∑ _i ∈ indices, (1 : Cardinal) :=
      Finset.sum_le_sum fun i _ => Fusion.SumOfTerms.Waring.term_rank_le_one (terms i)
    _ = _ := by simp
  exact_mod_cast bound

end Algebraic.Applications
