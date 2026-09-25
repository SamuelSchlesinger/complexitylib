/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.GCongr

/-!
# Finite covers from uniform local density

If a uniformly chosen test misses each obligation with probability at most
`p / q`, then `t` tests suffice whenever `card W * p ^ t < q ^ t`.
The argument counts finite function spaces and uses a union bound; no
measure-theoretic or independence assumptions are left to the caller.
-/

@[expose] public section

namespace Algebraic.Combinatorics.FiniteCover

open Finset

/-- A finite probabilistic cover bound, stated with integer cardinalities. -/
theorem exists_cover_of_scaled_card_lt
    {S W : Type*} [Fintype S] [Nonempty S] [Fintype W]
    (hit : S → W → Prop) [DecidableRel hit] (p q t : Nat)
    (localBound : ∀ w,
      q * Fintype.card {s : S // ¬ hit s w} ≤ p * Fintype.card S)
    (small : Fintype.card W * p ^ t < q ^ t) :
    ∃ tests : Fin t → S, ∀ w, ∃ i, hit (tests i) w := by
  classical
  let bad (w : W) : Finset (Fin t → S) :=
    univ.filter fun tests => ∀ i, ¬ hit (tests i) w
  have badCard (w : W) :
      (bad w).card = (Fintype.card {s : S // ¬ hit s w}) ^ t := by
    calc
      (bad w).card =
          Fintype.card {tests : Fin t → S // ∀ i, ¬ hit (tests i) w} := by
            simp [bad, Fintype.card_subtype]
      _ = Fintype.card (Fin t → {s : S // ¬ hit s w}) :=
        Fintype.card_congr (Equiv.subtypePiEquivPi
          (p := fun (_ : Fin t) (s : S) => ¬ hit s w))
      _ = _ := by simp
  have localPower (w : W) :
      q ^ t * (bad w).card ≤ p ^ t * (Fintype.card S) ^ t := by
    rw [badCard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (localBound w) t
  let failures := univ.biUnion bad
  have unionBound : q ^ t * failures.card ≤
      Fintype.card W * p ^ t * (Fintype.card S) ^ t := by
    calc
      q ^ t * failures.card ≤ q ^ t * ∑ w, (bad w).card :=
        Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ w, q ^ t * (bad w).card := mul_sum ..
      _ ≤ ∑ _w : W, p ^ t * (Fintype.card S) ^ t :=
        sum_le_sum fun w _ => localPower w
      _ = _ := by simp [Nat.mul_assoc]
  have strict : q ^ t * failures.card <
      q ^ t * Fintype.card (Fin t → S) := by
    apply lt_of_le_of_lt unionBound
    simpa [Fintype.card_fun] using
      Nat.mul_lt_mul_of_pos_right small
        (Nat.pow_pos (Fintype.card_pos))
  have smaller : failures.card < Fintype.card (Fin t → S) := by
    exact Nat.lt_of_mul_lt_mul_left strict
  obtain ⟨tests, _, absent⟩ := exists_mem_notMem_of_card_lt_card
    (show failures.card < (univ : Finset (Fin t → S)).card by simpa using smaller)
  refine ⟨tests, fun w => ?_⟩
  by_contra none
  apply absent
  simp only [failures, mem_biUnion, mem_univ, true_and]
  exact ⟨w, by simpa [bad] using none⟩

end Algebraic.Combinatorics.FiniteCover
