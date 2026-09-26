/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size

/-!
# Polynomial-time numbers and tests — division, powers and logarithms

The arithmetic behind the division, power and logarithm rules of
`Complexitylib.Classes.P.Unary`. Each of those functions is computed as a count
of the indices below a bound at which a comparison holds, or, for a capped
power, as a loop; the identities here say that the count or the loop gives the
intended value.

## Contents

- `card_filter_range_of_iff` — a count of the indices below a mark
- `div_eq_card_filter_range` — division as a count
- `min_mul_iterate` — capped multiplication, iterated, is a capped power
- `size_eq_card_filter_range`, `clog_eq_card_filter_range`,
  `log_eq_card_filter_range` — binary length and logarithms as counts
-/

@[expose] public section

namespace Complexity

/-- If a test holds at exactly the indices below `m ≤ n`, then `m` of the indices
below `n` pass it. -/
theorem card_filter_range_of_iff {n m : ℕ} (hm : m ≤ n) (p : ℕ → Prop) [DecidablePred p]
    (h : ∀ i < n, p i ↔ i < m) : ((Finset.range n).filter p).card = m := by
  have : (Finset.range n).filter p = Finset.range m := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨hi, hp⟩
      exact (h i hi).mp hp
    · intro hi
      exact ⟨by omega, (h i (by omega)).mpr hi⟩
  rw [this, Finset.card_range]

/-- **Division as a count**: `a / b` is the number of `i < a` with
`(i + 1) * b ≤ a`, or `0` when `b = 0`. -/
theorem div_eq_card_filter_range (a b : ℕ) :
    a / b = ((Finset.range a).filter fun i => 0 < b ∧ (i + 1) * b ≤ a).card := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · refine (card_filter_range_of_iff (Nat.div_le_self a b) _ fun i _ => ?_).symm
    rw [show i < a / b ↔ i + 1 ≤ a / b from Nat.lt_iff_add_one_le,
      Nat.le_div_iff_mul_le hb]
    exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩

/-- Multiplying by `b` and capping at `c`, `j` times from `min 1 c`, gives the
capped power `min (b ^ j) c`. -/
theorem min_mul_iterate (b c : ℕ) :
    ∀ j, (fun x => min (b * x) c)^[j] (min 1 c) = min (b ^ j) c
  | 0 => by rw [Function.iterate_zero_apply, pow_zero]
  | j + 1 => by
      rw [Function.iterate_succ_apply', min_mul_iterate b c j, pow_succ]
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      · rw [mul_comm (b ^ j) b]
        rcases le_total (b ^ j) c with h | h
        · rw [min_eq_left h]
        · have hc : c ≤ b * c := Nat.le_mul_of_pos_left c hb
          rw [min_eq_right h, min_eq_right hc,
            min_eq_right (hc.trans (Nat.mul_le_mul_left b h))]

/-- **Binary length as a count**: `Nat.size n` is the number of `i < n` with
`2 ^ i ≤ n`, the power capped at `n + 1`. -/
theorem size_eq_card_filter_range (n : ℕ) :
    Nat.size n = ((Finset.range n).filter fun i => min (2 ^ i) (n + 1) ≤ n).card := by
  refine (card_filter_range_of_iff (Nat.size_le.mpr Nat.lt_two_pow_self) _
    fun i _ => ?_).symm
  rw [Nat.lt_size]
  omega

/-- **The ceiling logarithm as a count**: for `1 < b`, `Nat.clog b n` is the
number of `i < n` with `b ^ i < n`, the power capped at `n`; and it is `0`
otherwise. -/
theorem clog_eq_card_filter_range (b n : ℕ) :
    Nat.clog b n = ((Finset.range n).filter fun i => 1 < b ∧ min (b ^ i) n < n).card := by
  by_cases hb : 1 < b
  · have hle : Nat.clog b n ≤ n := Nat.clog_le_of_le_pow
      ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hb n))
    refine (card_filter_range_of_iff hle _ fun i _ => ?_).symm
    rw [Nat.lt_clog_iff_pow_lt hb]
    omega
  · rw [Nat.clog_of_left_le_one (by omega)]
    simp [hb]

/-- **The floor logarithm as a count**: for `1 < b`, `Nat.log b n` is the number
of `i < n` with `b ^ (i + 1) ≤ n`, the power capped at `n + 1`; and it is `0`
otherwise. -/
theorem log_eq_card_filter_range (b n : ℕ) :
    Nat.log b n
      = ((Finset.range n).filter fun i => 1 < b ∧ min (b ^ (i + 1)) (n + 1) ≤ n).card := by
  by_cases hb : 1 < b
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · refine (card_filter_range_of_iff (Nat.log_le_self b n) _ fun i _ => ?_).symm
      rw [show i < Nat.log b n ↔ i + 1 ≤ Nat.log b n from Nat.lt_iff_add_one_le,
        Nat.le_log_iff_pow_le hb (by omega)]
      omega
  · rw [Nat.log_of_left_le_one (by omega)]
    simp [hb]

end Complexity
