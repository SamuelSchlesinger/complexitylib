/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Internal.Invariant.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice

/-!
# Exact list and phase identities for advice induction

Appending a bit performs one further actual step. Unequal paired advice
means that at least one processed pair differs, so the observed-transcript
phase applies at the end of any pair of unequal equal-length words.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem adviceFold_snoc (n m L e : Nat) (x : Fin n → Bool) (y : Fin m → Bool)
    (q : Fin (matchedBlockOutputBits 64 L) → Bool) (advice : List Bool) (b : Bool) :
    adviceFold n m L e x y q (advice ++ [b]) =
      flipFlopStep n m L e x y (adviceFold n m L e x y q advice) b := by
  rw [adviceFold_append, adviceFold_cons, adviceFold_nil]

theorem pairedAdvice_disagrees_iff (pairs : List (Bool × Bool)) :
    (∃ b ∈ pairs, b.1 ≠ b.2) ↔ pairs.map Prod.fst ≠ pairs.map Prod.snd := by
  simp only [ne_eq, List.map_eq_map_iff, not_forall, exists_prop]

theorem pairedAdvice_snoc_ne (pairs : List (Bool × Bool)) (b b' : Bool) :
    pairs.map Prod.fst ++ [b] ≠ pairs.map Prod.snd ++ [b'] ↔
      pairs.map Prod.fst ≠ pairs.map Prod.snd ∨ b ≠ b' := by
  constructor
  · intro h
    by_cases hp : pairs.map Prod.fst = pairs.map Prod.snd
    · exact Or.inr fun hb => h (by rw [hp, hb])
    · exact Or.inl hp
  · intro h heq
    obtain ⟨hp, hb⟩ := List.append_inj heq (by simp only [List.length_map])
    rcases h with h | h
    · exact h hp
    · exact h (List.cons.inj hb).1

end Algebraic.Cutwidth.Extractor.Internal
