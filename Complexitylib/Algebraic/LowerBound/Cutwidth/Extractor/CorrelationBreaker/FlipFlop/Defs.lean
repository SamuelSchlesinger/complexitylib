/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs

/-!
# The concrete two-round look-ahead and advice-bit step

These are the deterministic programs in Algorithm 1 of Chattopadhyay,
Goyal, and Li, *Non-Malleable Extractors and Codes, with their Many
Tampered Extensions*, Section 6.3: https://arxiv.org/abs/1505.00107.
Every extractor call uses the actual scheduled Boolean program.

The shared seed width is `2^24 * L`; the right state has `2^64 * L` bits.
Both refresh calls read the original right source `y`. The intermediate
right state is used only by the middle call of each look-ahead. Each step
therefore makes eight extractor calls, with the advice bit choosing opposite
look-ahead outputs at the two refreshes. The definitions are total for all
parameters. `Opposite.False` and `Opposite.True` prove the one-step guarantee,
and `Advice.Extraction` proves the complete advice-chain guarantee
(`adviceCorrelationBreaker_dist_le`).
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Read the common seed-width prefix of a right state. -/
def flipFlopSeedPrefix (L : Nat) (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    Fin (matchedBlockSeedBits L) → Bool :=
  blockPrefix (Nat.mul_le_mul_right L (show 2 ^ 24 ≤ 2 ^ 64 by decide)) q

/-- Two rounds of alternating extraction, using three actual scheduled calls. -/
def flipFlopLookAhead (n L e : Nat) (x : Fin n → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    (Fin (matchedBlockSeedBits L) → Bool) × (Fin (matchedBlockSeedBits L) → Bool) :=
  let r₁ := matchedBlockExtractor n 24 L e x (flipFlopSeedPrefix L q)
  let s₂ := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e q r₁
  let r₂ := matchedBlockExtractor n 24 L e x s₂
  (r₁, r₂)

/-- The advice-bit step, refreshing twice from the original full right source. -/
def flipFlopStep (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) :
    Fin (matchedBlockOutputBits 64 L) → Bool :=
  let r := flipFlopLookAhead n L e x q
  let qbar := matchedBlockExtractor m 64 L e y (if b then r.2 else r.1)
  let rbar := flipFlopLookAhead n L e x qbar
  matchedBlockExtractor m 64 L e y (if b then rbar.1 else rbar.2)

end Algebraic.Cutwidth.Extractor
