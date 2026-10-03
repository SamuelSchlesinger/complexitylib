/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs

/-!
# The finite advice-chain error sequence

This internal sequence follows the actual common step error while the
original-source envelope totals grow by the checked transcript factors.
The sequence is numerical proof data; the program invariant must separately
be constructed for each executed prefix.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

/-- Iterate the actual common step bound with the exact envelope growth at each prefix. -/
noncomputable def adviceChainError (L e : Nat) (ρ α β : ℝ) : Nat → ℝ
  | 0 => ρ
  | i + 1 => adviceStepError L e (adviceChainError L e ρ α β i)
      ((Fintype.card (Fin (matchedBlockSeedBits L) → Bool) : ℝ) ^ (8 * i) * α)
      ((Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) : ℝ) ^ (5 * i) * β)

end Algebraic.Cutwidth.Extractor.Internal
