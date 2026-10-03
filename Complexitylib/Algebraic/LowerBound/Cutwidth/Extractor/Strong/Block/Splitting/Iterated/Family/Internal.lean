/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

/-!
# Averaging multiblock splitting over retained seeds

Choose a repaired block source in every seed fiber. Splitting preserves
the seed coordinate, and its joint distance is the average of the fiber
distances. The empty seed type contributes zero total mass and zero distance.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem exists_split_pow_two_seedFamily {α Seed : Type*} [Fintype α] [Fintype Seed]
    {t m s k e : Nat} (p : Seed → (Fin t → α × α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) (2 ^ k)) (card : Fintype.card α = 2 ^ m)
    (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : Seed → (Fin (2 * t) → α) → ℝ,
      (∀ y, IsBlockSource (q y) (2 ^ s)) ∧
        weightDist
          (mapWeight (fun yx : Seed × (Fin t → α × α) =>
            (yx.1, splitBlockEquiv α t yx.2)) (seedFamilyWeight p))
          (seedFamilyWeight q) ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ := by
  classical
  choose q witnesses close using fun y => (source y).exists_split_pow_two card width entropy
  refine ⟨q, witnesses, ?_⟩
  rw [mapWeight_seedFamilyWeight
    (fun (_ : Seed) (x : Fin t → α × α) => splitBlockEquiv α t x) p,
    weightDist_seedFamilyWeight]
  by_cases empty : Fintype.card Seed = 0
  · simp only [empty, Nat.cast_zero, div_zero]
    positivity
  · have positive : (0 : ℝ) < Fintype.card Seed := by
      exact_mod_cast Nat.pos_of_ne_zero empty
    apply (div_le_iff₀ positive).mpr
    calc
      _ ≤ ∑ _y : Seed, (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
        Finset.sum_le_sum fun y _ => close y
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Algebraic.Cutwidth.Extractor.Internal
