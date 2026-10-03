/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Reserves

/-!
# Checked finite bounds for the actual advice error sequence

The actual common recurrence is monotone and nonnegative, with a closed
`a * 4^a` bound from zero initial error. Equal original entropy reserves
`2^150 * (a+1) * L` cover all displayed observer losses when `e ≤ L`.
The local error choice `target + 2a + clog₂(a+1) + 10` then pays for both
the complete recurrence and the final original-left-source extraction.

These conservative arithmetic deductions accompany the CGL Algorithm 2 /
Lemma 6.9 advice-chain route, <https://arxiv.org/pdf/1505.00107>. They do not
assume or establish an execution invariant: the separate induction must
construct that invariant for the actual deterministic program.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceChainError_fixedReserve_le (L e a : Nat) {α β : ℝ}
    (error : e ≤ L) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (left : α ≤ ((2 : ℝ) ^ (2 ^ 150 * (a + 1) * L))⁻¹)
    (right : β ≤ ((2 : ℝ) ^ (2 ^ 150 * (a + 1) * L))⁻¹) :
    let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    adviceChainError L e 0 α β a + ((2 : ℝ) ^ e)⁻¹ +
        K * D ^ (8 * a + 1) * α ≤
      (24 * (a : ℝ) * 4 ^ a + 2) * ((2 : ℝ) ^ e)⁻¹ :=
  adviceChainError_final_le L e a _ _ hα hβ left right (advice_state_entropy_gap error)
    (advice_left_entropy_reserve error) (advice_right_entropy_reserve error)

theorem adviceChainError_fixedReserve_dyadic_le (L a target : Nat) {α β : ℝ}
    (error : target + 2 * a + Nat.clog 2 (a + 1) + 10 ≤ L)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (left : α ≤ ((2 : ℝ) ^ (2 ^ 150 * (a + 1) * L))⁻¹)
    (right : β ≤ ((2 : ℝ) ^ (2 ^ 150 * (a + 1) * L))⁻¹) :
    let e := target + 2 * a + Nat.clog 2 (a + 1) + 10
    let K : ℝ := (2 : ℝ) ^ (2 ^ 62 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    adviceChainError L e 0 α β a + ((2 : ℝ) ^ e)⁻¹ +
        K * D ^ (8 * a + 1) * α ≤ ((2 : ℝ) ^ target)⁻¹ :=
  (adviceChainError_fixedReserve_le L _ a error hα hβ left right).trans
    (adviceError_schedule_le a target)

end Algebraic.Cutwidth.Extractor.Internal
