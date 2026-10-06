/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.KCNF.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexitylib.Circuits.KCNF.Internal.Coding

/-!
# The satisfiability coding lemma

The coding lemma of Paturi, Pudlák and Zane ("Satisfiability coding lemma", FOCS 1997 and
Chicago J. Theoret. Comput. Sci. 1999), in decoder form and with exact finite sums over all
`N!` orders of the variables in place of probabilities.

Fix a clause set `ψ` over `N` variables and an order `σ` of the variables (`σ v` is the position
of `v`). The decoder `ClauseSet.decode ψ σ` processes the variables in this order. At `v`, if some
clause has a literal on `v` and all its other literals are on earlier variables and false under
the values already decoded, it sets `v` to satisfy such a literal; otherwise it copies the input
bit `y v`. The variables at which this first rule fires on input `x` are `ψ.forced σ x`.

## Main results

* `decode_eq_of_agree`: on every input that agrees with a solution `x` off its forced variables,
  the decoder outputs `x`.
* `sum_two_pow_card_forced_le`: hence the sets of such inputs are disjoint, and
  `∑_{x ∈ sol ψ} 2 ^ |forced σ x| ≤ 2 ^ N` for every order (Lemma 1 (i) for one order).
* `sum_two_rpow_average_card_forced_le`: by Jensen's inequality, the same with the average of
  `|forced σ x|` over all `N!` orders in the exponent (Lemma 1 (i)).
* `card_isolatedDirections_mul_factorial_le`: in a clause set of width `k`, a solution with `ι`
  isolated directions (`x ⊕ e_i` is not a solution) has `ι · N! ≤ k ∑_σ |forced σ x|`.
* `sum_two_rpow_card_isolatedDirections_div_le`: hence `∑_{x ∈ sol ψ} 2 ^ (ι(x)/k) ≤ 2 ^ N`
  for every clause set of width `k ≥ 1` (Lemma 1 (ii)).
-/

@[expose] public section

namespace Complexity.ClauseSet

variable {N : ℕ}

/-- **Decoding.** On every input `y` that agrees with a solution `x` of `ψ` outside the variables
forced on `x` for the order `σ`, the decoder outputs `x`. -/
theorem decode_eq_of_agree {ψ : ClauseSet N} {σ : Equiv.Perm (Fin N)} {x y : BitString N}
    (hx : x ∈ ψ.solutions) (hy : ∀ v ∉ ψ.forced σ x, y v = x v) : ψ.decode σ y = x :=
  Coding.decode_eq_of_agree (mem_solutions.mp hx) hy

/-- **The coding bound for one order.** For every order `σ`, the solutions `x` of `ψ` satisfy
`∑ₓ 2 ^ |forced σ x| ≤ 2 ^ N`. -/
theorem sum_two_pow_card_forced_le (ψ : ClauseSet N) (σ : Equiv.Perm (Fin N)) :
    ∑ x ∈ ψ.solutions, 2 ^ (ψ.forced σ x).card ≤ 2 ^ N :=
  Coding.sum_two_pow_forced_le ψ σ

/-- **The coding lemma, decoder form (Lemma 1 (i)).** With `E(x)` the average of
`|forced σ x|` over all `N!` orders `σ`, the solutions `x` of `ψ` satisfy
`∑ₓ 2 ^ E(x) ≤ 2 ^ N`. -/
theorem sum_two_rpow_average_card_forced_le (ψ : ClauseSet N) :
    ∑ x ∈ ψ.solutions,
        (2 : ℝ) ^ ((∑ σ : Equiv.Perm (Fin N), ((ψ.forced σ x).card : ℝ)) / N.factorial) ≤
      2 ^ N :=
  Coding.sum_two_rpow_average_forced_le ψ

/-- **Isolated directions are forced often.** If every clause of `ψ` has at most `k` literals,
every solution `x` with `ι` isolated directions has `ι · N! ≤ k · ∑_σ |forced σ x|`: the
average number of forced variables is at least `ι / k`. -/
theorem card_isolatedDirections_mul_factorial_le {ψ : ClauseSet N} {k : ℕ}
    (hk : ∀ C ∈ ψ, C.card ≤ k) {x : BitString N} (hx : x ∈ ψ.solutions) :
    (isolatedDirections ψ.solutions x).card * N.factorial ≤
      k * ∑ σ : Equiv.Perm (Fin N), (ψ.forced σ x).card :=
  Coding.card_isolated_mul_factorial_le hk (mem_solutions.mp hx)

/-- **The coding lemma for `k`-CNFs (Lemma 1 (ii)).** If every clause of `ψ` has at most
`k ≥ 1` literals, then `∑_{x ∈ sol ψ} 2 ^ (ι(x)/k) ≤ 2 ^ N`, where `ι(x)` is the number of
directions `i` with `x ⊕ e_i ∉ sol ψ`. -/
theorem sum_two_rpow_card_isolatedDirections_div_le {ψ : ClauseSet N} {k : ℕ} (hk1 : 1 ≤ k)
    (hk : ∀ C ∈ ψ, C.card ≤ k) :
    ∑ x ∈ ψ.solutions,
        (2 : ℝ) ^ (((isolatedDirections ψ.solutions x).card : ℝ) / k) ≤ 2 ^ N :=
  Coding.sum_two_rpow_isolated_div_le hk1 hk

end Complexity.ClauseSet
