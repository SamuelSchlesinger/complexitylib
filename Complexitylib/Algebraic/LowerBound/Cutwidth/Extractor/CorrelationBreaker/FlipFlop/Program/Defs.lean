/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Program.Defs

/-!
# String programs for the concrete look-ahead and advice-bit step

The look-ahead runtime encodes its two outputs with `Complexity.pair`.
The step uses the matched extractor runtime at fixed depths twenty-four
and sixty-four, always retaining the original source words. Each component
has total behavior on arbitrary strings and parameters; agreement with the
fixed-width definitions uses the explicit common-scale guard.

The single-input codec is `pair (pair x (pair y q)) (pair scale (pair error bit))`.
The numerical parameters are unary lengths and the advice bit is the first
bit of its word, defaulting to `false` for an empty word.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- Shared scale sufficient for all three kinds of extractor call in one step. -/
def FlipFlopSizeGuard (n m L e : Nat) : Prop :=
  e + 66 ≤ L ∧ Nat.clog 2 (n + 1) ≤ L ∧ Nat.clog 2 (m + 1) ≤ L ∧
    Nat.clog 2 (matchedBlockOutputBits 64 L + 1) ≤ L

/-- Encode the two look-ahead outputs from the actual string programs. -/
def flipFlopLookAheadRuntime (L e : Nat) (x q : List Bool) : List Bool :=
  let r₁ := matchedBlockExtractorRuntime 24 L e x (q.take (matchedBlockSeedBits L))
  let s₂ := matchedBlockExtractorRuntime 24 L e q r₁
  let r₂ := matchedBlockExtractorRuntime 24 L e x s₂
  pair r₁ r₂

/-- Execute one advice-bit step, using the original `y` at both refreshes. -/
def flipFlopStepRuntime (L e : Nat) (x y q : List Bool) (b : Bool) : List Bool :=
  let r := flipFlopLookAheadRuntime L e x q
  let qbar := matchedBlockExtractorRuntime 64 L e y (if b then pairSnd r else pairFst r)
  let rbar := flipFlopLookAheadRuntime L e x qbar
  matchedBlockExtractorRuntime 64 L e y (if b then pairFst rbar else pairSnd rbar)

/-- One total evaluator for all lengths, shared scales, errors, and advice bits. -/
def flipFlopStepEval (z : List Bool) : List Bool :=
  flipFlopStepRuntime (pairFst (pairSnd z)).length
    (pairFst (pairSnd (pairSnd z))).length
    (pairFst (pairFst z)) (pairFst (pairSnd (pairFst z)))
    (pairSnd (pairSnd (pairFst z))) ((pairSnd (pairSnd (pairSnd z)))[0]?.getD false)

end Algebraic.Cutwidth.Extractor
