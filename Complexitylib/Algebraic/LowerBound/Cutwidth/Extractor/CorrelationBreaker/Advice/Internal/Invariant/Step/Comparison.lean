/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A common one-bit error budget

The weak, first-mismatch, and already-separated estimates are all dominated
by the same recurrence. Only the actual Boolean alphabet cardinalities and
the nonnegativity of the relevant joint envelope totals are used.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem one_le_boolCard (n : Nat) :
    1 ≤ (Fintype.card (Fin n → Bool) : ℝ) := by
  exact_mod_cast (show 1 ≤ Fintype.card (Fin n → Bool) from Fintype.card_pos)

theorem adviceWeakStep_le (L e : Nat) (ρ α β : ℝ) (hα : 0 ≤ α) :
    let K : ℝ := 2 ^ (2 ^ 62 * L)
    let J : ℝ := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    4 * ρ + 12 * ((2 : ℝ) ^ e)⁻¹ + K * (1 + D ^ 2) * (2 + D ^ 4) * α +
      3 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β ≤ adviceStepError L e ρ α β := by
  have hD : 0 ≤ (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) - 1 :=
    sub_nonneg.mpr (one_le_boolCard _)
  have extra : 0 ≤ (2 : ℝ) ^ (2 ^ 62 * L) *
      ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) - 1) *
      (1 + (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 2) *
      (2 + (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 4) * α := by
    positivity
  apply sub_nonneg.mp
  convert extra using 1
  dsimp only [adviceStepError]
  ring

theorem advicePostStep_le (L e : Nat) (ρ α β : ℝ) (hβ : 0 ≤ β) :
    let K : ℝ := 2 ^ (2 ^ 62 * L)
    let J : ℝ := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    4 * ρ + 12 * ((2 : ℝ) ^ e)⁻¹ + K * D * (1 + D ^ 2) * (2 + D ^ 4) * α +
      3 * K * D ^ 2 / C + J * (2 * C ^ 2 + C ^ 5) * β ≤ adviceStepError L e ρ α β := by
  have hC : 0 ≤ (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) - 1 :=
    sub_nonneg.mpr (one_le_boolCard _)
  have extra : 0 ≤ 2 * (2 : ℝ) ^ (2 ^ 142 * L) *
      (Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ 2 *
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) - 1) * β := by
    positivity
  apply sub_nonneg.mp
  convert extra using 1
  dsimp only [adviceStepError]
  ring

theorem adviceOppositeStep_le (L e : Nat) (ρ α β : ℝ) (hρ : 0 ≤ ρ) (hα : 0 ≤ α) :
    let K : ℝ := 2 ^ (2 ^ 62 * L)
    let J : ℝ := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    2 * ρ + 10 * ((2 : ℝ) ^ e)⁻¹ + K * (1 + D ^ 2) * (2 + D ^ 4) * α +
      2 * K * D ^ 2 / C + J * (2 * C ^ 3 + C ^ 5) * β ≤ adviceStepError L e ρ α β := by
  have hD : 0 ≤ (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) - 1 :=
    sub_nonneg.mpr (one_le_boolCard _)
  have extra : 0 ≤ 2 * ρ + 2 * ((2 : ℝ) ^ e)⁻¹ +
      (2 : ℝ) ^ (2 ^ 62 * L) *
        ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) - 1) *
        (1 + (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 2) *
        (2 + (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 4) * α +
      (2 : ℝ) ^ (2 ^ 62 * L) *
        (Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ 2 /
        Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) := by
    positivity
  apply sub_nonneg.mp
  convert extra using 1
  dsimp only [adviceStepError]
  ring

end Algebraic.Cutwidth.Extractor.Internal
