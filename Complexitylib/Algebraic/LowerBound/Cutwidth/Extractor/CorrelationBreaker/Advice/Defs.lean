/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Defs

/-!
# The concrete advice chain and its final extraction

The initial state and left-to-right advice fold are Algorithm 2 of
Chattopadhyay, Goyal, and Li, *Non-Malleable Extractors and Codes, with their
Many Tampered Extensions*, Section 6.3: https://arxiv.org/abs/1505.00107.
The original sources remain fixed throughout the fold. Short right sources
are completed by false bits when forming the initial state.

The final map additionally extracts from the original left source using the
seed-width prefix of the final state. Every call is the actual scheduled
Boolean extractor. These definitions assert no statistical guarantee for
the advice chain; that requires a separate invariant and entropy argument.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The initial right state is a prefix of the right source, completed by false bits. -/
def adviceInitialState (m L : Nat) (y : Fin m → Bool) :
    Fin (matchedBlockOutputBits 64 L) → Bool :=
  fun i => (List.ofFn y)[i.val]?.getD false

/-- Process advice from its first bit to its last, keeping both original sources. -/
def adviceFold (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (advice : List Bool) :
    Fin (matchedBlockOutputBits 64 L) → Bool :=
  advice.foldl (flipFlopStep n m L e x y) q

/-- The actual advice chain followed by extraction from the original left source. -/
def adviceCorrelationBreaker (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (advice : List Bool) : Fin (matchedBlockSeedBits L) → Bool :=
  matchedBlockExtractor n 24 L e x
    (flipFlopSeedPrefix L (adviceFold n m L e x y (adviceInitialState m L y) advice))

end Algebraic.Cutwidth.Extractor
