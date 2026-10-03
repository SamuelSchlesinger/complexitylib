/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformRefresh
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.FlipFlop.UniformState
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The concrete selected refresh before advice differs

Specialize the uniform-state refresh theorem to the actual matched-width
extractors. Both initial right states remain arbitrary functions of the
original right state; the actual law keeps all four short outputs.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem flipFlopSelectedRefresh_dist_le (n m L e : Nat) {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (guard : FlipFlopSizeGuard n m L e)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x x' : Z → A → Fin n → Bool) (y : Z → B → Fin m → Bool)
    (q q' : Z → B → Fin (matchedBlockOutputBits 64 L) → Bool)
    (μ ξ : Z → ℝ) (b : Bool) {ρ : ℝ}
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ξ z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (y z) (r z) y₀ ≤ ξ z)
    (state : weightDist (retainedSeedWeight w r q)
      (uniformSecondWeight (retainedSeedWeight w r q)) ≤ ρ) :
    let K : Nat := 2 ^ (2 ^ 62 * L)
    let J : Nat := 2 ^ (2 ^ 142 * L)
    let D : ℝ := Fintype.card (Fin (matchedBlockSeedBits L) → Bool)
    let C : ℝ := Fintype.card (Fin (matchedBlockOutputBits 64 L) → Bool)
    let ε := ((2 : ℝ) ^ e)⁻¹
    let p := lookAheadSelectedRefreshWeight (Mid := Fin (matchedBlockSeedBits L) → Bool)
      w l r x x' q q' (flipFlopSeedPrefix L) (matchedBlockExtractor n 24 L e)
      (matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e)
      y (matchedBlockExtractor m 64 L e) b
    weightDist p (uniformSecondWeight p) ≤
      4 * ε + 2 * ρ + (K : ℝ) * (1 + D ^ 2) * (∑ z, μ z) +
        (K : ℝ) * D ^ 2 / C + (J : ℝ) * C ^ 3 * ∑ z, ξ z := by
  let Mid := Fin (matchedBlockSeedBits L) → Bool
  let Q := Fin (matchedBlockOutputBits 64 L) → Bool
  let W : (Fin n → Bool) → Mid → Mid := matchedBlockExtractor n 24 L e
  let QExt : Q → Mid → Mid := matchedBlockExtractor (matchedBlockOutputBits 64 L) 24 L e
  let R : (Fin m → Bool) → Mid → Q := matchedBlockExtractor m 64 L e
  have room : 64 ≤ L := by have := guard.1; lia
  have error : e + 24 + 2 ≤ L := by have := guard.1; lia
  have first : WeightedStrongSeededExtractor W (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 n L e guard.2.1 room error
  have second : WeightedStrongSeededExtractor QExt (2 ^ (2 ^ 62 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth24 _ L e guard.2.2.2 room error
  have refresh : WeightedStrongSeededExtractor R (2 ^ (2 ^ 142 * L)) (((2 : ℝ) ^ e)⁻¹) :=
    matchedBlockExtractor_depth64 m L e guard.2.2.1 room (by have := guard.1; lia)
  have bound := first.lookAhead_uniformRefresh_dist_le (by positivity)
    second (by positivity) refresh (by positivity) w l r x x' q q' (flipFlopSeedPrefix L)
    y μ ξ b hw hl hr left_nonnegative right_nonnegative left_cap right_cap
    (flipFlopSeedPrefix_uniform L) state
  dsimp only
  convert bound using 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

end Algebraic.Cutwidth.Extractor.Internal
