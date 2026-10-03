/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Bounds.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Monotonicity of the actual advice error recurrence

Every source-loss coefficient is nonnegative for all parameters. Thus the
step bound is monotone without sign assumptions on its input bounds, and
the exact numerical iteration preserves nonnegativity and order.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceStepError_mono (L e : Nat) {ρ ρ' α α' β β' : ℝ}
    (hρ : ρ ≤ ρ') (hα : α ≤ α') (hβ : β ≤ β') :
    adviceStepError L e ρ α β ≤ adviceStepError L e ρ' α' β' := by
  dsimp only [adviceStepError]
  gcongr

theorem adviceStepError_nonneg (L e : Nat) {ρ α β : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ adviceStepError L e ρ α β := by
  dsimp only [adviceStepError]
  positivity

@[simp] theorem adviceChainError_zero (L e : Nat) (ρ α β : ℝ) :
    adviceChainError L e ρ α β 0 = ρ := rfl

theorem adviceChainError_succ (L e i : Nat) (ρ α β : ℝ) :
    adviceChainError L e ρ α β (i + 1) =
      adviceStepError L e (adviceChainError L e ρ α β i)
        ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ (8 * i) * α)
        ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ (5 * i) * β) := rfl

theorem adviceChainError_nonneg (L e i : Nat) {ρ α β : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    0 ≤ adviceChainError L e ρ α β i := by
  induction i with
  | zero => exact hρ
  | succ i ih =>
    rw [adviceChainError_succ]
    exact adviceStepError_nonneg L e ih (by positivity) (by positivity)

theorem adviceChainError_mono (L e i : Nat) {ρ ρ' α α' β β' : ℝ}
    (hρ : ρ ≤ ρ') (hα : α ≤ α') (hβ : β ≤ β') :
    adviceChainError L e ρ α β i ≤ adviceChainError L e ρ' α' β' i := by
  induction i with
  | zero => exact hρ
  | succ i ih =>
    rw [adviceChainError_succ, adviceChainError_succ]
    exact adviceStepError_mono L e ih
      (mul_le_mul_of_nonneg_left hα (by positivity))
      (mul_le_mul_of_nonneg_left hβ (by positivity))

end Algebraic.Cutwidth.Extractor.Internal
