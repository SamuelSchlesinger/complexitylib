/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A closed finite bound for the advice error recurrence

The actual observer factors grow the left and right envelopes by powers
`D^(8i)` and `C^(5i)`. At a fixed final depth their contributions are bounded
by one constant budget, and the factor-four recurrence accumulates at most
`a * 4^a` times that budget. These are finite bounds, including zero depth.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem left_factor_le {D : ℝ} (hD : 1 ≤ D) :
    D * (1 + D ^ 2) * (2 + D ^ 4) ≤ 6 * D ^ 7 := by
  have hD0 : 0 ≤ D := by linarith
  have h2 : 1 ≤ D ^ 2 := one_le_pow₀ hD
  have h4 : 1 ≤ D ^ 4 := one_le_pow₀ hD
  calc
    D * (1 + D ^ 2) * (2 + D ^ 4) ≤ D * (2 * D ^ 2) * (3 * D ^ 4) := by
      gcongr <;> nlinarith
    _ = 6 * D ^ 7 := by ring

private theorem right_factor_le {C : ℝ} (hC : 1 ≤ C) :
    2 * C ^ 3 + C ^ 5 ≤ 3 * C ^ 5 := by
  have h35 : C ^ 3 ≤ C ^ 5 := pow_le_pow_right₀ hC (by decide)
  linarith

private theorem bit_card_one_le (n : Nat) :
    (1 : ℝ) ≤ Fintype.card (Fin n → Bool) := by
  exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := Fin n → Bool))

theorem adviceStepError_growth_le (L e i a : Nat) {ρ α β : ℝ}
    (hi : i ≤ a) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
    let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    adviceStepError L e ρ (D ^ (8 * i) * α) (C ^ (5 * i) * β) ≤
      4 * ρ + (12 * ((2 : ℝ) ^ e)⁻¹ + 3 * K * D ^ 2 / C +
        6 * K * D ^ (8 * a + 7) * α + 3 * J * C ^ (5 * a + 5) * β) := by
  let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
  let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
  let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
  let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
  have hK : 0 ≤ K := by positivity
  have hJ : 0 ≤ J := by positivity
  have hD : 1 ≤ D := bit_card_one_le _
  have hC : 1 ≤ C := bit_card_one_le _
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have left : K * D * (1 + D ^ 2) * (2 + D ^ 4) * (D ^ (8 * i) * α) ≤
      6 * K * D ^ (8 * a + 7) * α := by
    calc
      _ = K * (D * (1 + D ^ 2) * (2 + D ^ 4)) * D ^ (8 * i) * α := by ring
      _ ≤ K * (6 * D ^ 7) * D ^ (8 * i) * α := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (left_factor_le hD) hK)
            (pow_nonneg hD0 _)) hα
      _ = 6 * K * D ^ (8 * i + 7) * α := by rw [pow_add]; ring
      _ ≤ 6 * K * D ^ (8 * a + 7) * α := by
        gcongr
  have right : J * (2 * C ^ 3 + C ^ 5) * (C ^ (5 * i) * β) ≤
      3 * J * C ^ (5 * a + 5) * β := by
    calc
      _ = J * (2 * C ^ 3 + C ^ 5) * C ^ (5 * i) * β := by ring
      _ ≤ J * (3 * C ^ 5) * C ^ (5 * i) * β := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (right_factor_le hC) hJ)
            (pow_nonneg hC0 _)) hβ
      _ = 3 * J * C ^ (5 * i + 5) * β := by rw [pow_add]; ring
      _ ≤ 3 * J * C ^ (5 * a + 5) * β := by
        gcongr
  change 4 * ρ + 12 * ((2 : ℝ) ^ e)⁻¹ +
      K * D * (1 + D ^ 2) * (2 + D ^ 4) * (D ^ (8 * i) * α) +
      3 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * (C ^ (5 * i) * β) ≤ _
  change _ ≤ 4 * ρ + (12 * ((2 : ℝ) ^ e)⁻¹ + 3 * K * D ^ 2 / C +
    6 * K * D ^ (8 * a + 7) * α + 3 * J * C ^ (5 * a + 5) * β)
  linarith only [left, right]

private theorem accumulated_recurrence (ρ : Nat → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (initial : ρ 0 ≤ 0) (a : Nat)
    (step : ∀ i < a, ρ (i + 1) ≤ 4 * ρ i + B) :
    ρ a ≤ (a : ℝ) * 4 ^ a * B := by
  revert step
  induction a with
  | zero => intro _; simpa using initial
  | succ a ih =>
    intro step
    have previous := ih (fun i hi => step i (lt_trans hi (Nat.lt_succ_self a)))
    have hp : (1 : ℝ) ≤ 4 ^ a := one_le_pow₀ (by norm_num)
    have hb : B ≤ 4 ^ a * B := by nlinarith
    calc
      ρ (a + 1) ≤ 4 * ρ a + B := step a (Nat.lt_succ_self a)
      _ ≤ 4 * ((a : ℝ) * 4 ^ a * B) + 4 ^ a * B := by gcongr
      _ ≤ ((a + 1 : Nat) : ℝ) * 4 ^ (a + 1) * B := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ a) hB]

theorem adviceChainError_le (L e a : Nat) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
    let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    adviceChainError L e 0 α β a ≤ (a : ℝ) * 4 ^ a *
      (12 * ((2 : ℝ) ^ e)⁻¹ + 3 * K * D ^ 2 / C +
        6 * K * D ^ (8 * a + 7) * α + 3 * J * C ^ (5 * a + 5) * β) := by
  apply accumulated_recurrence (adviceChainError L e 0 α β) (by positivity) (by rfl) a
  intro i hi
  rw [adviceChainError_succ]
  exact adviceStepError_growth_le L e i a (Nat.le_of_lt hi) hα hβ

end Algebraic.Cutwidth.Extractor.Internal
