/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Closed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite entropy reserves and the advice error schedule

Three explicit integer reserves make each source-loss monomial at most the
local dyadic error. The accumulated recurrence and one final extraction
therefore cost at most `(24 * a * 4^a + 2) * 2^(-e)`. The displayed local
error schedule absorbs this factor. These arithmetic bounds do not supply
an initial source, factorization, or extractor-security invariant.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem dyadic_reserve_le (k d r e h : Nat) (reserve : k + r * d + e ≤ h) :
    (2 : ℝ) ^ k * ((2 : ℝ) ^ d) ^ r * ((2 : ℝ) ^ h)⁻¹ ≤ ((2 : ℝ) ^ e)⁻¹ := by
  have power : (2 : ℝ) ^ (k + d * r + e) ≤ (2 : ℝ) ^ h :=
    pow_le_pow_right₀ (by norm_num) (by simpa only [Nat.mul_comm d r] using reserve)
  apply (mul_le_mul_iff_left₀ (show 0 < (2 : ℝ) ^ e by positivity)).mp
  calc
    _ = (2 : ℝ) ^ (k + d * r + e) * ((2 : ℝ) ^ h)⁻¹ := by
      rw [pow_add, pow_add, pow_mul]
      ring
    _ ≤ (2 : ℝ) ^ h * ((2 : ℝ) ^ h)⁻¹ :=
      mul_le_mul_of_nonneg_right power (by positivity)
    _ = _ := by field_simp

theorem adviceChainError_final_le (L e a kX kY : Nat) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (left : α ≤ ((2 : ℝ) ^ kX)⁻¹) (right : β ≤ ((2 : ℝ) ^ kY)⁻¹)
    (state_reserve : 2 ^ 62 * L + 2 * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits 64 L)
    (left_reserve : 2 ^ 62 * L + (8 * a + 7) * matchedBlockSeedBits L + e ≤ kX)
    (right_reserve : 2 ^ 142 * L + (5 * a + 5) * matchedBlockOutputBits 64 L + e ≤ kY) :
    let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    adviceChainError L e 0 α β a + ((2 : ℝ) ^ e)⁻¹ +
        K * D ^ (8 * a + 1) * α ≤
      (24 * (a : ℝ) * 4 ^ a + 2) * ((2 : ℝ) ^ e)⁻¹ := by
  let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
  let J : ℝ := (2 : ℝ) ^ (2 ^ 142 * L)
  let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
  let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
  let ε := ((2 : ℝ) ^ e)⁻¹
  have cross : K * D ^ 2 / C ≤ ε := by
    simpa only [K, D, C, ε, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
      dyadic_reserve_le (2 ^ 62 * L) (matchedBlockSeedBits L) 2 e
        (matchedBlockOutputBits 64 L) state_reserve
  have left_loss : K * D ^ (8 * a + 7) * α ≤ ε := by
    calc
      _ ≤ K * D ^ (8 * a + 7) * ((2 : ℝ) ^ kX)⁻¹ :=
        mul_le_mul_of_nonneg_left left (by positivity)
      _ ≤ ε := by
        simpa only [K, D, ε, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat] using
          dyadic_reserve_le (2 ^ 62 * L) (matchedBlockSeedBits L) (8 * a + 7) e kX left_reserve
  have right_loss : J * C ^ (5 * a + 5) * β ≤ ε := by
    calc
      _ ≤ J * C ^ (5 * a + 5) * ((2 : ℝ) ^ kY)⁻¹ :=
        mul_le_mul_of_nonneg_left right (by positivity)
      _ ≤ ε := by
        simpa only [J, C, ε, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat] using
          dyadic_reserve_le (2 ^ 142 * L) (matchedBlockOutputBits 64 L) (5 * a + 5) e kY
            right_reserve
  have final_reserve : 2 ^ 62 * L + (8 * a + 1) * matchedBlockSeedBits L + e ≤ kX := by
    apply le_trans _ left_reserve
    gcongr
    lia
  have final_loss : K * D ^ (8 * a + 1) * α ≤ ε := by
    calc
      _ ≤ K * D ^ (8 * a + 1) * ((2 : ℝ) ^ kX)⁻¹ :=
        mul_le_mul_of_nonneg_left left (by positivity)
      _ ≤ ε := by
        simpa only [K, D, ε, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat] using
          dyadic_reserve_le (2 ^ 62 * L) (matchedBlockSeedBits L) (8 * a + 1) e kX final_reserve
  have budget : 12 * ε + 3 * K * D ^ 2 / C +
      6 * K * D ^ (8 * a + 7) * α + 3 * J * C ^ (5 * a + 5) * β ≤ 24 * ε := by
    simp only [div_eq_mul_inv] at cross ⊢
    linarith only [cross, left_loss, right_loss]
  have iter := adviceChainError_le L e a hα hβ
  change adviceChainError L e 0 α β a ≤ (a : ℝ) * 4 ^ a *
    (12 * ε + 3 * K * D ^ 2 / C +
      6 * K * D ^ (8 * a + 7) * α + 3 * J * C ^ (5 * a + 5) * β) at iter
  have chain := iter.trans (mul_le_mul_of_nonneg_left budget (by positivity))
  change adviceChainError L e 0 α β a + ε + K * D ^ (8 * a + 1) * α ≤ _
  calc
    _ ≤ (a : ℝ) * 4 ^ a * (24 * ε) + ε + ε :=
      add_le_add (add_le_add chain le_rfl) final_loss
    _ = _ := by ring

theorem adviceError_numerator_le (a : Nat) :
    24 * a * 4 ^ a + 2 ≤ 2 ^ (2 * a + Nat.clog 2 (a + 1) + 10) := by
  have hp : (1 : Nat) ≤ 4 ^ a := one_le_pow₀ (by norm_num)
  have ha : a + 1 ≤ 2 ^ Nat.clog 2 (a + 1) := Nat.le_pow_clog (by decide) _
  calc
    24 * a * 4 ^ a + 2 ≤ 32 * (a + 1) * 4 ^ a := by nlinarith
    _ ≤ 1024 * 2 ^ Nat.clog 2 (a + 1) * 4 ^ a := by gcongr; norm_num
    _ = 2 ^ (2 * a + Nat.clog 2 (a + 1) + 10) := by
      simp only [pow_add, pow_mul]
      norm_num
      ring

theorem adviceError_schedule_le (a target : Nat) :
    (24 * (a : ℝ) * 4 ^ a + 2) *
        ((2 : ℝ) ^ (target + 2 * a + Nat.clog 2 (a + 1) + 10))⁻¹ ≤
      ((2 : ℝ) ^ target)⁻¹ := by
  have hn : 24 * (a : ℝ) * 4 ^ a + 2 ≤
      (2 : ℝ) ^ (2 * a + Nat.clog 2 (a + 1) + 10) := by
    exact_mod_cast adviceError_numerator_le a
  rw [show target + 2 * a + Nat.clog 2 (a + 1) + 10 =
    target + (2 * a + Nat.clog 2 (a + 1) + 10) by lia, pow_add, mul_inv]
  calc
    _ ≤ (2 : ℝ) ^ (2 * a + Nat.clog 2 (a + 1) + 10) *
        (((2 : ℝ) ^ target)⁻¹ *
          ((2 : ℝ) ^ (2 * a + Nat.clog 2 (a + 1) + 10))⁻¹) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = ((2 : ℝ) ^ target)⁻¹ := by field_simp

theorem advice_state_entropy_gap {e L : Nat} (he : e ≤ L) :
    2 ^ 62 * L + 2 * matchedBlockSeedBits L + e ≤ matchedBlockOutputBits 64 L := by
  simp only [matchedBlockSeedBits, matchedBlockOutputBits]
  norm_num
  lia

theorem advice_left_entropy_reserve {a e L : Nat} (he : e ≤ L) :
    2 ^ 62 * L + (8 * a + 7) * matchedBlockSeedBits L + e ≤
      2 ^ 150 * (a + 1) * L := by
  simp only [matchedBlockSeedBits]
  norm_num
  nlinarith

theorem advice_right_entropy_reserve {a e L : Nat} (he : e ≤ L) :
    2 ^ 142 * L + (5 * a + 5) * matchedBlockOutputBits 64 L + e ≤
      2 ^ 150 * (a + 1) * L := by
  simp only [matchedBlockOutputBits]
  norm_num
  nlinarith

end Algebraic.Cutwidth.Extractor.Internal
