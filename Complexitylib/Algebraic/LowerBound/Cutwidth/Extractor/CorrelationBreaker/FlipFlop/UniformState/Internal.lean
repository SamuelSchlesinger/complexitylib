/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.LookAhead
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repaired-state extraction for the actual three-call program

A uniform Boolean state has a uniform seed-width prefix. Apply the generic
repair theorem to the two actual matched-depth extractors, keeping the whole
original right state and both first outputs. All state and source maps remain
those of the deterministic program.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def uniformStateSplit (d r : Nat) :
    (Fin (d + r) → Bool) ≃ (Fin d → Bool) × (Fin r → Bool) :=
  ((finSumFinEquiv : Fin d ⊕ Fin r ≃ Fin (d + r)).symm.arrowCongr
    (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

private theorem uniformStatePrefix (d r : Nat) :
    mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
      (uniformWeight (Fin (d + r) → Bool)) = uniformWeight (Fin d → Bool) := by
  have split : mapWeight (uniformStateSplit d r) (uniformWeight (Fin (d + r) → Bool)) =
      uniformWeight ((Fin d → Bool) × (Fin r → Bool)) := by
    funext y
    rw [mapWeight_equiv_apply]
    unfold uniformWeight
    rw [Fintype.card_congr (uniformStateSplit d r)]
  have first := congrArg (mapWeight Prod.fst) split
  rw [mapWeight_comp] at first
  change mapWeight (fun q : Fin (d + r) → Bool => fun i : Fin d => q (Fin.castAdd r i))
    (uniformWeight (Fin (d + r) → Bool)) = _ at first
  rw [first, mapWeight_fst]
  have positive : (Fintype.card (Fin r → Bool) : ℝ) ≠ 0 := by positivity
  funext y
  simp only [firstWeight, uniformWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  field_simp

private theorem uniformStatePrefix_of_le {d n : Nat} (size : d ≤ n) :
    mapWeight (fun q : Fin n → Bool => fun i : Fin d => q (Fin.castLE size i))
      (uniformWeight (Fin n → Bool)) = uniformWeight (Fin d → Bool) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le size
  exact uniformStatePrefix d r

theorem flipFlopSeedPrefix_uniform (L : Nat) :
    mapWeight (flipFlopSeedPrefix L)
      (uniformWeight (Fin (matchedBlockOutputBits 64 L) → Bool)) =
        uniformWeight (Fin (matchedBlockSeedBits L) → Bool) :=
  uniformStatePrefix_of_le (Nat.mul_le_mul_right L (show 2 ^ 24 ≤ 2 ^ 64 by decide))

theorem flipFlopLookAhead_uniformState_dist_le (n L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (length : Nat.clog 2 (n + 1) ≤ L)
    (right_length : Nat.clog 2 (matchedBlockOutputBits 64 L + 1) ≤ L)
    (room : 64 ≤ L) (error : e + 24 + 2 ≤ L)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ : Z → ℝ) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let M := Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
      (Fin (matchedBlockSeedBits L) → Bool))
    weightDist (flipFlopLookAheadWeight n L e w l r x x' q q')
      (uniformSecondWeight (flipFlopLookAheadWeight n L e w l r x x' q q')) ≤
        3 * ((2 : ℝ) ^ e)⁻¹ + 2 * ρ + (K : ℝ) * (1 + M) * (∑ z, μ z) +
          (K : ℝ) * M / Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool) := by
  dsimp only
  rw [flipFlopLookAheadWeight_eq]
  have first := matchedBlockExtractor_depth24 n L e length room error
  have bound := first.lookAhead_uniformState_dist_le (by positivity)
      (matchedBlockExtractor_depth24 _ L e right_length room error) (by positivity)
      w l r x x' q q' (flipFlopSeedPrefix L) μ hw hl hr nonnegative cap
      (flipFlopSeedPrefix_uniform L) state
  have cards : Fintype.card ((Fin (matchedBlockOutputBits 24 L) → Bool) ×
      (Fin (matchedBlockOutputBits 24 L) → Bool)) =
      Fintype.card ((Fin (matchedBlockSeedBits L) → Bool) ×
        (Fin (matchedBlockSeedBits L) → Bool)) := rfl
  rw [cards] at bound
  have errors : 2 * ((2 : ℝ) ^ e)⁻¹ + ((2 : ℝ) ^ e)⁻¹ = 3 * ((2 : ℝ) ^ e)⁻¹ := by ring
  rw [errors] at bound
  exact bound

end Algebraic.Cutwidth.Extractor.Internal
