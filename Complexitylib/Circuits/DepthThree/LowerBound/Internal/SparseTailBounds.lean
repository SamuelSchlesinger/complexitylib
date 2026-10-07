/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.SparseTestCodes
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.UniformSparseBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Unrestricted depth-three lower bound: sparse tail bounds

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/SparseTailBounds.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

namespace DepthThreeLowerBound

private theorem two_rpow_log_div (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ (Real.log x / Real.log 2) = x := by
  have htwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * (Real.log x / Real.log 2) = Real.log x := by
    field_simp [htwo]
  rw [he, Real.exp_log hx]

theorem nat_pow_eq_two_rpow (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = (2 : ℝ) ^ ((n : ℝ) * (Real.log x / Real.log 2)) := by
  calc
    x ^ n = ((2 : ℝ) ^ (Real.log x / Real.log 2)) ^ n := by
      rw [two_rpow_log_div x hx]
    _ = (2 : ℝ) ^ ((Real.log x / Real.log 2) * (n : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) _ n).symm
    _ = _ := by congr 1 ; ring

theorem sparse_count_le_two_rpow (m b L : ℕ) :
    ((2 * (m : ℝ) + 1) ^ b + 1) ^ L ≤
      (2 : ℝ) ^ ((L : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (m : ℝ) + 1) / Real.log 2))) := by
  have hx : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hxone : 1 ≤ 2 * (m : ℝ) + 1 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hpow : 1 ≤ (2 * (m : ℝ) + 1) ^ b := one_le_pow₀ hxone
  calc
    _ ≤ (2 * (2 * (m : ℝ) + 1) ^ b) ^ L :=
      pow_le_pow_left₀ (by positivity) (by linarith) L
    _ = ((2 : ℝ) ^ (1 + (b : ℝ) *
        (Real.log (2 * (m : ℝ) + 1) / Real.log 2))) ^ L := by
      congr 1
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
        ← nat_pow_eq_two_rpow _ hx b]
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1 ; ring

theorem sparseTestCode_card_le_two_rpow {V : Type uDepth1} [Fintype V] (b L : ℕ) :
    (Fintype.card (SparseTestCode V b L) : ℝ) ≤
      (2 : ℝ) ^ ((L : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (Fintype.card V : ℝ) + 1) / Real.log 2))) := by
  rw [SparseTestCode.card_eq]
  push_cast
  exact sparse_count_le_two_rpow (Fintype.card V) b L

theorem sparse_moment_union_le {V : Type uDepth2} [Fintype V] (b M t : ℕ)
    (hm : 0 < Fintype.card V) (ht : 0 < t)
    (hcond : (M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * (Fintype.card V : ℝ) + 1) / Real.log 2)) /
          (t : ℝ) + (Real.log (t : ℝ) / Real.log 2) / (Fintype.card V : ℝ) ≤ 1 / 8) :
    (Fintype.card (SparseTestCode V b (M * Fintype.card V)) : ℝ) * (t : ℝ) ^ t *
        (2 : ℝ) ^ (-((Fintype.card V : ℝ) * (t : ℝ)) / 4) ≤
      (2 : ℝ) ^ (-((Fintype.card V : ℝ) * (t : ℝ)) / 8) := by
  let m : ℝ := Fintype.card V
  have hmpos : 0 < m := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hmult := mul_le_mul_of_nonneg_right hcond (mul_nonneg hmpos.le htpos.le)
  have hclear : ((M : ℝ) *
        (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) / (t : ℝ) +
        (Real.log (t : ℝ) / Real.log 2) / m) * (m * (t : ℝ)) =
      (M : ℝ) * m * (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
        (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) := by
    field_simp [hmpos.ne', htpos.ne']
  change ((M : ℝ) *
      (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) / (t : ℝ) +
      (Real.log (t : ℝ) / Real.log 2) / m) * (m * (t : ℝ)) ≤
        (1 / 8 : ℝ) * (m * (t : ℝ)) at hmult
  rw [hclear] at hmult
  have hcount := sparseTestCode_card_le_two_rpow (V := V) b (M * Fintype.card V)
  calc
    _ ≤ (2 : ℝ) ^ (((M * Fintype.card V : ℕ) : ℝ) *
          (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2))) * (t : ℝ) ^ t *
        (2 : ℝ) ^ (-(m * (t : ℝ)) / 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcount (pow_nonneg (Nat.cast_nonneg t) t))
        (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (((M * Fintype.card V : ℕ) : ℝ) *
          (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
          (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) + -(m * (t : ℝ)) / 4) := by
      rw [nat_pow_eq_two_rpow (t : ℝ) htpos t,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      change (M : ℝ) * m *
        (1 + (b : ℝ) * (Real.log (2 * m + 1) / Real.log 2)) +
        (t : ℝ) * (Real.log (t : ℝ) / Real.log 2) + -(m * (t : ℝ)) / 4 ≤
          -(m * (t : ℝ)) / 8
      linarith

end DepthThreeLowerBound

end

end Complexity
