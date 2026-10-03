/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Defs

/-!
# Basic laws for the concrete advice fold

The list fold exposes the order of the advice bits and its exact composition
law, without any distributional or size hypotheses.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceFold_nil (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) :
    adviceFold n m L e x y q [] = q := rfl

theorem adviceFold_cons (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (b : Bool) (advice : List Bool) :
    adviceFold n m L e x y q (b :: advice) =
      adviceFold n m L e x y (flipFlopStep n m L e x y q b) advice := by
  simp only [adviceFold, List.foldl_cons]

theorem adviceFold_append (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (first last : List Bool) :
    adviceFold n m L e x y q (first ++ last) =
      adviceFold n m L e x y (adviceFold n m L e x y q first) last :=
  List.foldl_append

end Algebraic.Cutwidth.Extractor.Internal
