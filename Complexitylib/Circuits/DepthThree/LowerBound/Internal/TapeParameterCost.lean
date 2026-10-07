/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeParameterSearch
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Unrestricted depth-three lower bound: tape parameter cost

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeParameterCost.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeParameterCost

open scoped BigOperators

private theorem pow_bound {c k : ℕ} (hk : k ≤ 7) : c ^ k ≤ (c + 1) ^ 7 :=
  Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ c) k)
    (Nat.pow_le_pow_right (Nat.succ_pos c) hk)

private theorem power_positive (c : ℕ) : 1 ≤ (c + 1) ^ 7 :=
  Nat.pow_pos (Nat.succ_pos c)

theorem power_cost {k : ℕ} (hk : k ≤ 6) (c : ℕ) :
    TapePower.cost k 1 c ≤ 108 * (c + 1) ^ 7 := by
  have hs : (∑ j ∈ Finset.range k, c ^ j) ≤ 6 * (c + 1) ^ 6 := by
    calc
      (∑ j ∈ Finset.range k, c ^ j) ≤ ∑ _j ∈ Finset.range k, (c + 1) ^ 6 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk := Finset.mem_range.mp hj
        exact Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ c) j)
          (Nat.pow_le_pow_right (Nat.succ_pos c) (by omega : j ≤ 6))
      _ = k * (c + 1) ^ 6 := by simp
      _ ≤ 6 * (c + 1) ^ 6 := Nat.mul_le_mul_right _ hk
  have hc : 10 * c + 14 ≤ 14 * (c + 1) := by omega
  have hp := power_positive c
  calc
    TapePower.cost k 1 c = (10 * c + 14) * (∑ j ∈ Finset.range k, c ^ j) + 4 * k := by
      rw [TapePower.cost_eq_sum, Nat.one_mul]
    _ ≤ (10 * c + 14) * (6 * (c + 1) ^ 6) + 24 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hs) (by omega)
    _ ≤ (14 * (c + 1)) * (6 * (c + 1) ^ 6) + 24 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _
    _ = 84 * (c + 1) ^ 7 + 24 := by ring
    _ ≤ 108 * (c + 1) ^ 7 := by omega

theorem compare_cost {k : ℕ} (hk : k ≤ 6) (c D : ℕ) :
    TapePowerCompare.cost k c D ≤ 124 * (c + 1) ^ 7 := by
  have hp := power_cost hk c
  have hmin := Nat.le_trans (Nat.min_le_left (c ^ k) D) (pow_bound (by omega : k ≤ 7))
  have hpos := power_positive c
  unfold TapePowerCompare.cost
  omega

theorem body_cost {k : ℕ} (hk : k ≤ 6) (two : Bool) (c : ℕ) :
    TapeSearchBody.cost k two c ≤ 16 * (c + 1) ^ 7 := by
  have hp : c ^ k ≤ (c + 1) ^ 7 := pow_bound (by omega)
  have hpos := power_positive c
  cases two <;> simp [TapeSearchBody.cost, TapeSearchBody.incrementCost] <;> omega

theorem search_cost {k : ℕ} (hk : k ≤ 6) (two : Bool) (D fuel c B : ℕ)
    (hc : c + TapeSearchBody.amount two * fuel ≤ B) :
    TapePowerSearch.cost k two D fuel c ≤ (fuel + 1) * 144 * (B + 1) ^ 7 := by
  induction fuel generalizing c with
  | zero =>
      have hcB : c ≤ B := by simpa using hc
      have hp : (c + 1) ^ 7 ≤ (B + 1) ^ 7 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hcB 1) 7
      have hcmp := Nat.le_trans (compare_cost hk c D) (Nat.mul_le_mul_left 124 hp)
      have hpos := power_positive B
      simp only [TapePowerSearch.cost, Nat.zero_add, Nat.one_mul]
      omega
  | succ fuel ih =>
      have hcB : c ≤ B := by omega
      have hnext : c + TapeSearchBody.amount two + TapeSearchBody.amount two * fuel ≤ B := by
        rw [Nat.mul_succ] at hc
        omega
      have hr := ih (c + TapeSearchBody.amount two) hnext
      have hp : (c + 1) ^ 7 ≤ (B + 1) ^ 7 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hcB 1) 7
      have hcmp := Nat.le_trans (compare_cost hk c D) (Nat.mul_le_mul_left 124 hp)
      have hb := Nat.le_trans (body_cost hk two c) (Nat.mul_le_mul_left 16 hp)
      have hpos := power_positive B
      have hprefix : TapePowerCompare.cost k c D + 1 + TapeSearchBody.cost k two c + 1 ≤
          144 * (B + 1) ^ 7 := by omega
      calc
        TapePowerSearch.cost k two D (fuel + 1) c ≤
            144 * (B + 1) ^ 7 + (fuel + 1) * 144 * (B + 1) ^ 7 :=
          Nat.add_le_add hprefix hr
        _ = (fuel + 1 + 1) * 144 * (B + 1) ^ 7 := by ring

theorem cube_cost (d : ℕ) : TapeParameterSearch.cubeCost d ≤ 200 * (d + 3) ^ 8 := by
  have hr := hashDimension_le d
  have hs := search_cost (by decide : 3 ≤ 6) false (d ^ 2) (hashDimension d) 0 d
    (by simpa [TapeSearchBody.amount] using hr)
  have hprod : (hashDimension d + 1) * 144 * (d + 1) ^ 7 ≤ 144 * (d + 1) ^ 8 := by
    calc
      _ ≤ (d + 1) * 144 * (d + 1) ^ 7 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_right hr 1))
      _ = _ := by ring
  have hs' := Nat.le_trans hs hprod
  have hbase : (d + 1) ^ 8 ≤ (d + 3) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have hsearch := Nat.le_trans hs' (Nat.mul_le_mul_left 144 hbase)
  have hp : (hashDimension d) ^ 3 ≤ (d + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : hashDimension d ≤ d + 3) 3)
      (Nat.pow_le_pow_right (by omega : 0 < d + 3) (by decide : 3 ≤ 8))
  have hpos : 1 ≤ (d + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold TapeParameterSearch.cubeCost
  omega

theorem sixth_cost (d : ℕ) : TapeParameterSearch.sixthCost d ≤ 200 * (d + 3) ^ 8 := by
  have ht := independenceOrder_le d
  have he := independenceOrder_even d
  have hterminal : 2 * (independenceOrder d / 2 + 1) = independenceOrder d + 2 := by
    obtain ⟨a, ha⟩ := he
    omega
  have hs := search_cost (by decide : 6 ≤ 6) true d
    (independenceOrder d / 2 + 1) 0 (d + 2)
    (by simp [TapeSearchBody.amount]; omega)
  have hprod : (independenceOrder d / 2 + 1 + 1) * 144 * (d + 2 + 1) ^ 7 ≤
      144 * (d + 3) ^ 8 := by
    calc
      _ ≤ (d + 3) * 144 * (d + 3) ^ 7 := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_right 144 (by omega)
        · apply Nat.pow_le_pow_left
          omega
      _ = _ := by ring
  have hsearch := Nat.le_trans hs hprod
  have hp : (independenceOrder d + 2) ^ 6 ≤ (d + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : independenceOrder d + 2 ≤ d + 3) 6)
      (Nat.pow_le_pow_right (by omega : 0 < d + 3) (by decide : 6 ≤ 8))
  have hpos : 1 ≤ (d + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold TapeParameterSearch.sixthCost
  omega

end TapeParameterCost
end DepthThreeLowerBound

end Complexity
