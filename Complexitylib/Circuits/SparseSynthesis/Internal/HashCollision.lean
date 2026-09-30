/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.Randomized.Hashing.Affine
import Mathlib.Tactic

/-!
# A hash with few collisions

Pairwise independence and exact finite averaging give a seed with at most
`pairs.card / 2 ^ rangeWidth` collisions among any specified distinct pairs.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open scoped BigOperators

variable {n m seedWidth : ℕ} (hash : PairwiseIndependentHash n m seedWidth)

theorem hash_collision_prob (x y : BitString n) (different : x ≠ y) :
    eventProb (Finset.univ.filter fun seed => hash.eval seed x = hash.eval seed y) =
      1 / (2 : ℚ) ^ m := by
  classical
  rw [eventProb_eq_sum_fiberwise _ Finset.univ (fun seed => hash.eval seed x)
    (by intro seed _; simp)]
  have fiber (target : BitString m) :
      (Finset.univ.filter fun seed => hash.eval seed x = hash.eval seed y).filter
        (fun seed => hash.eval seed x = target) =
      Finset.univ.filter (fun seed => hash.eval seed x = target ∧ hash.eval seed y = target) := by
    ext seed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨eqn, hx⟩
      exact ⟨hx, eqn ▸ hx⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx.trans hy.symm, hx⟩
  simp_rw [fiber, hash.pairwise different]
  simp only [Finset.sum_const, Finset.card_univ, card_finArrowBool, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_mul']
  field_simp

/-- Specified ordered pairs whose endpoints hash to the same value. -/
def hashCollisions (pairs : Finset (BitString n × BitString n)) (seed : BitString seedWidth) :
    Finset (BitString n × BitString n) :=
  pairs.filter fun xy => hash.eval seed xy.1 = hash.eval seed xy.2

theorem sum_hashCollisions (pairs : Finset (BitString n × BitString n))
    (different : ∀ xy ∈ pairs, xy.1 ≠ xy.2) :
    (∑ seed, (hashCollisions hash pairs seed).card) * 2 ^ m = pairs.card * 2 ^ seedWidth := by
  classical
  have average : (∑ seed, ((hashCollisions hash pairs seed).card : ℚ)) /
      (2 : ℚ) ^ seedWidth = pairs.card / (2 : ℚ) ^ m := by
    simp only [hashCollisions, Finset.card_filter]
    push_cast
    rw [Finset.sum_comm, Finset.sum_div]
    have each (xy) (hxy : xy ∈ pairs) :
        (∑ seed : BitString seedWidth,
          if hash.eval seed xy.1 = hash.eval seed xy.2 then (1 : ℚ) else 0) /
          (2 : ℚ) ^ seedWidth = 1 / (2 : ℚ) ^ m := by
      have h := hash_collision_prob hash xy.1 xy.2 (different xy hxy)
      simpa only [eventProb, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero] using h
    rw [Finset.sum_congr rfl each]
    simp [div_eq_mul_inv]
  have product := (div_eq_div_iff (by positivity : (2 : ℚ) ^ seedWidth ≠ 0)
    (by positivity : (2 : ℚ) ^ m ≠ 0)).mp average
  exact_mod_cast product

theorem exists_few_hashCollisions (pairs : Finset (BitString n × BitString n))
    (different : ∀ xy ∈ pairs, xy.1 ≠ xy.2) :
    ∃ seed, (hashCollisions hash pairs seed).card * 2 ^ m ≤ pairs.card := by
  classical
  by_contra missing
  push Not at missing
  have h := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (BitString seedWidth)))
    Finset.univ_nonempty (fun seed _ => missing seed)
  rw [← Finset.sum_mul, sum_hashCollisions hash pairs different] at h
  simp only [Finset.sum_const, Finset.card_univ, card_finArrowBool, smul_eq_mul] at h
  exact (Nat.lt_irrefl _ (by simpa only [Nat.mul_comm] using h))

end Complexity.CircuitSparseSynthesis.Internal
