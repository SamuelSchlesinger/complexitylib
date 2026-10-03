/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Mathlib.Data.Fin.Tuple.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Prepending a two-block source to its conditional tails

Disintegrating the two-coordinate head gives a capped first coordinate and
a capped second coordinate for every first value. Two applications of the
one-coordinate prepend theorem then retain all tail caps. Zero-mass rows
are already handled by the existing disintegration theorem.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem isBlockSource_pairPrepend {α : Type*} [Fintype α] {t K : Nat}
    (head : α × α → ℝ) (tail : α × α → (Fin t → α) → ℝ)
    (head_source : IsBlockSource (fun x : Fin 2 → α => head (x 0, x 1)) K)
    (tail_source : ∀ ab, IsBlockSource (tail ab) K) :
    IsBlockSource
      (fun x : Fin (t + 2) → α =>
        head (x 0, x 1) * tail (x 0, x 1) (Fin.tail (Fin.tail x))) K := by
  obtain ⟨w, q, probability, cap, sources, factor⟩ :=
    IsBlockSource.exists_head_tail (t := 1) head_source
  let second (a b : α) := q a (fun _ => b)
  have second_prob (a : α) : IsProbabilityWeight (second a) := by
    have transport : mapWeight (Equiv.funUnique (Fin 1) α) (q a) = second a := by
      funext b
      rw [mapWeight_equiv_apply]
      rfl
    rw [← transport]
    exact (sources a).probability.map (Equiv.funUnique (Fin 1) α)
  have second_cap (a : α) : CappedWeight (second a) K := by
    intro b
    exact ((isBlockSource_one_iff (q a) K).mp (sources a)).2 (fun _ => b)
  have head_factor (a b : α) : head (a, b) = w a * second a b := by
    simpa only [Fin.cons_zero, Fin.cons_one] using factor a (fun _ => b)
  have rows (a : α) :
      IsBlockSource
        (fun z : Fin (t + 1) → α => second a (z 0) * tail (a, z 0) (Fin.tail z)) K :=
    isBlockSource_prepend (second a) (fun b => tail (a, b))
      (second_prob a) (second_cap a) (fun b => tail_source (a, b))
  have result := isBlockSource_prepend w
    (fun a (z : Fin (t + 1) → α) => second a (z 0) * tail (a, z 0) (Fin.tail z))
    probability cap rows
  simpa only [Fin.tail, Fin.succ_zero_eq_one, ← mul_assoc, ← head_factor] using result

end Algebraic.Cutwidth.Extractor.Internal
