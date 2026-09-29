/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Log

/-!
# Choosing coprime moduli at the desired scale

As in Lecomte and Ramakrishnan, Section 4, use the smallest power of each of
the first `r` primes that exceeds the integer scale `k`. These powers lie
between `k` and a constant (depending only on `r`) times `k`.
-/

public section

namespace Complexity.Shallow

open Finset

/-- Any fixed number of pairwise coprime moduli can be chosen at a common
scale, with constants independent of that scale. -/
theorem exists_moduli (r : ℕ) : ∃ C : ℕ, 1 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
    ∃ m : Fin r → ℕ,
      Pairwise (fun i j => (m i).Coprime (m j)) ∧
      (∀ i, k < m i) ∧ (∀ i, m i ≤ C * k) := by
  let p (i : Fin r) := Nat.nth Nat.Prime i.val
  refine ⟨1 + ∑ i, p i, by omega, fun k hk => ?_⟩
  let m (i : Fin r) := p i ^ (Nat.log (p i) k + 1)
  have hp (i : Fin r) : (p i).Prime := Nat.prime_nth_prime i.val
  refine ⟨m, ?_, ?_, ?_⟩
  · intro i j hij
    apply Nat.coprime_pow_primes _ _ (hp i) (hp j)
    intro heq
    apply hij
    apply Fin.ext
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective heq
  · intro i
    exact Nat.lt_pow_succ_log_self (hp i).one_lt k
  · intro i
    have hi : p i ≤ ∑ j, p j := single_le_sum (fun j _ => Nat.zero_le (p j)) (mem_univ i)
    calc
      m i = p i * p i ^ Nat.log (p i) k := by simp [m, pow_succ, Nat.mul_comm]
      _ ≤ p i * k := Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (by omega))
      _ ≤ (1 + ∑ j, p j) * k := Nat.mul_le_mul_right _ (by omega)

/-- The product of `r` moduli exceeding `k` exceeds `k^r`. -/
theorem pow_lt_prod_moduli {r k : ℕ} (hr : 0 < r) (m : Fin r → ℕ)
    (hm : ∀ i, k < m i) : k ^ r < ∏ i, m i := by
  calc
    k ^ r < (k + 1) ^ r := Nat.pow_lt_pow_left (by omega) (by omega)
    _ = ∏ _i : Fin r, (k + 1) := by simp
    _ ≤ ∏ i, m i := Finset.prod_le_prod (fun i _ => Nat.succ_le_of_lt (hm i))

end Complexity.Shallow
