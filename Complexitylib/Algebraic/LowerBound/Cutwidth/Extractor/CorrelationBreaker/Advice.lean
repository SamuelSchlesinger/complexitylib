/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal

/-!
# Exact composition laws for the advice chain

The concrete chain processes advice in its given order and preserves its
original sources. These algebraic laws do not supply the statistical chain
invariant needed for correlation breaking.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Empty advice preserves the supplied initial state. -/
theorem adviceFold_nil (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    adviceFold n m L e x y q [] = q :=
  Internal.adviceFold_nil n m L e x y q

/-- The first advice bit is processed before the remaining advice. -/
theorem adviceFold_cons (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) (advice : List Bool) :
    adviceFold n m L e x y q (b :: advice) =
      adviceFold n m L e x y (flipFlopStep n m L e x y q b) advice :=
  Internal.adviceFold_cons n m L e x y q b advice

/-- Concatenating advice composes its two consecutive folds. -/
theorem adviceFold_append (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (first last : List Bool) :
    adviceFold n m L e x y q (first ++ last) =
      adviceFold n m L e x y (adviceFold n m L e x y q first) last :=
  Internal.adviceFold_append n m L e x y q first last

end Algebraic.Cutwidth.Extractor
