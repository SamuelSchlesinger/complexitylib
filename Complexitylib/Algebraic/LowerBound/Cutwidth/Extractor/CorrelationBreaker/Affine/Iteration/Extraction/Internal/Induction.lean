/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration.Extraction.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Iteration
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Round.Invariant

/-!
# Security induction along actual affine-round states

The finite scalar mass premises concern only the original envelopes.
Exact observation identities supply each intermediate envelope and its
mass; the actual four-call theorem then doubles the subset capacity.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineIterationError_zero (e : Nat) (ρ : ℝ) : affineIterationError e ρ 0 = ρ := by
  simp [affineIterationError]

theorem affineIterationError_succ (e i : Nat) (ρ : ℝ) :
    affineIterationError e ρ (i + 1) =
      2 * affineIterationError e ρ i + 8 * ((2 : ℝ) ^ e)⁻¹ := by
  unfold affineIterationError
  rw [pow_succ]
  ring

theorem affineIterationState_iterate_invariant {n d h t L : Nat}
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (s : AffineIterationState n d h t L Z A B) (e rounds k : Nat)
    (kx ky : Nat → Nat) (μ ν : Z → ℝ) {ρ : ℝ}
    (size : matchedBlockSeedBits L ≤ matchedBlockOutputBits h L)
    (right_length : Nat.clog 2 (d + 1) ≤ L)
    (row_length : Nat.clog 2 (matchedBlockOutputBits h L + 1) ≤ L)
    (room : 64 ≤ L) (short_error : e + 24 + 2 ≤ L)
    (final_length : Nat.clog 2 (n + 1) ≤ L) (final_error : e + h + 2 ≤ L)
    (final_budget : (h + 1) * (e + 2 * h + Nat.clog 2 (L + 1) + 4) ≤ L)
    (hw : IsProbabilityWeight s.weight) (hl : ∀ z, IsProbabilityWeight (s.left z))
    (hr : ∀ z, IsProbabilityWeight (s.right z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, s.weight z * mapWeight (s.source z) (s.left z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, s.weight z *
      mapWeight (fun b => s.rightWords z b none) (s.right z) y₀ ≤ ν z)
    (first : ∀ i < rounds,
      2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤ ky i)
    (merge : 2 ^ 62 * L + (t + t + 1) * matchedBlockSeedBits L + e ≤
      matchedBlockOutputBits h L)
    (recover : ∀ i < rounds,
      2 ^ 62 * L + (t + 3 * (t + 1)) * matchedBlockSeedBits L + e ≤ ky i)
    (final : ∀ i < rounds, 2 ^ (2 * h + 14) * L + t * matchedBlockOutputBits h L +
      2 * (t + 1) * matchedBlockSeedBits L + e ≤ kx i)
    (left_mass : ∀ i < rounds,
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (2 * i) * (∑ z, μ z) ≤
        ((2 : ℝ) ^ kx i)⁻¹)
    (right_mass : ∀ i < rounds,
      (Fintype.card (AffineRoundShortMessages t L) : ℝ) ^ (4 * i) * (∑ z, ν z) ≤
        ((2 : ℝ) ^ ky i)⁻¹)
    (old : AffineRowInvariant h t L s.weight s.left s.leftRows k ρ)
    (i : Nat) (executed : i ≤ rounds) :
    AffineRowInvariant h t L (s.iterate e i).weight (s.iterate e i).left
      (s.iterate e i).leftRows (2 ^ i * k) (affineIterationError e ρ i) := by
  induction i with
  | zero =>
      rw [affineIterationError_zero, pow_zero, one_mul]
      convert old using 1 <;> rfl
  | succ i ih =>
      have before : i < rounds := by lia
      have probability := s.iterate_probability e i hw hl hr
      have left_total : (∑ z, s.leftEnvelope e μ i z) ≤ ((2 : ℝ) ^ kx i)⁻¹ := by
        rw [s.leftEnvelope_sum e i μ hw hl hr]
        exact left_mass i before
      have right_total : (∑ z, s.rightEnvelope e ν i z) ≤ ((2 : ℝ) ^ ky i)⁻¹ := by
        rw [s.rightEnvelope_sum e i ν hw hl hr]
        exact right_mass i before
      have step := affineRound_doubles_invariant n d h t L e (2 ^ i * k) (kx i) (ky i)
        (s.iterate e i).weight (s.iterate e i).left (s.iterate e i).right
        (s.iterate e i).source (s.iterate e i).leftRows (s.iterate e i).rightRows
        (s.iterate e i).rightWords (s.leftEnvelope e μ i) (s.rightEnvelope e ν i)
        size right_length row_length room short_error final_length final_error final_budget
        probability.1 probability.2.1 probability.2.2
        (s.leftEnvelope_nonnegative e i μ hw hl hr left_nonnegative)
        (s.rightEnvelope_nonnegative e i ν hw hl hr right_nonnegative)
        (s.leftEnvelope_cap e i μ hw hl hr left_cap)
        (s.rightEnvelope_cap e i ν hw hl hr right_cap)
        (first i before) merge (recover i before) (final i before) left_total right_total
        (ih (by lia))
      rw [affineIterationError_succ,
        show 2 ^ (i + 1) * k = 2 * (2 ^ i * k) by rw [pow_succ]; ac_rfl]
      exact step

end Algebraic.Cutwidth.Extractor.Internal
