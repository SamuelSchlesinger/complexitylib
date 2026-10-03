/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.PhaseOne.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Advice.Truncation
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched.Affine
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Matched
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.UniformState

/-!
# The actual initial seed for the affine phase's advice call

Uniformity of the original honest right input supplies its balanced prefix.
The depth-sixty-four extraction retains the full original right state.
Projecting that state to the first transcript therefore also retains every
tampered prefix and mask contribution, with no new error or source loss.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affinePhaseOneFirstSeed_uniform (d L₀ : Nat) (size : matchedBlockSeedBits L₀ ≤ d) :
    mapWeight (affinePhaseOneFirstSeed d L₀) (uniformWeight (Fin d → Bool)) =
      uniformWeight (Fin (matchedBlockSeedBits L₀) → Bool) :=
  adviceOutputPrefix_uniform size

theorem affinePhaseOne_initial_seed_dist_le (n d t L₀ e₀ : Nat)
    (length : Nat.clog 2 (n + 1) ≤ L₀) (room : 64 ≤ L₀) (error : e₀ + 64 + 2 ≤ L₀)
    (size : matchedBlockSeedBits L₀ ≤ d)
    {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → Fin n → Bool) (mask : Z → B → Fin n → Bool)
    (ys : Z → B → AffinePhaseOneCopies t d) (μ : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (uniform : ∀ z, mapWeight (fun b => ys z b none) (r z) = uniformWeight (Fin d → Bool)) :
    let actual := alternatingSeedWeight w l r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)
      (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a none)
    weightDist actual (uniformSecondWeight actual) ≤
      ((2 : ℝ) ^ e₀)⁻¹ + (2 : ℝ) ^ (2 ^ 142 * L₀) * ∑ z, μ z := by
  have seed := retainedSeedWeight_uniform_image_dist w r (fun z b => ys z b none)
    (affinePhaseOneFirstSeed d L₀) (affinePhaseOneFirstSeed_uniform d L₀ size)
    (fun z _ => by rw [uniform z])
  have first := matchedBlockExtractor_depth64_affine_dist_le n L₀ e₀ length room error
    w l r x mask (fun z b => affinePhaseOneFirstSeed d L₀ (ys z b none)) μ
    hw hl hr nonnegative cap seed.le
  have projected := weightDist_uniformSecond_map_first_le
    (affineExtractionWeight w l r x mask
      (fun z b => affinePhaseOneFirstSeed d L₀ (ys z b none))
      (fun a b i => Bool.xor (a i) (b i)) (matchedBlockExtractor n 64 L₀ e₀))
    (fun p : Z × B => (p.1, affinePhaseOneRightMessage n d t L₀ e₀ mask ys p.1 p.2))
  have actual : alternatingSeedWeight w l r (affinePhaseOneRightMessage n d t L₀ e₀ mask ys)
      (fun z a => affinePhaseOneFirstLeft n t L₀ e₀ x z a none) =
      mapWeight (fun p : (Z × B) × (Fin (matchedBlockOutputBits 64 L₀) → Bool) =>
        ((p.1.1, affinePhaseOneRightMessage n d t L₀ e₀ mask ys p.1.1 p.1.2), p.2))
        (affineExtractionWeight w l r x mask
          (fun z b => affinePhaseOneFirstSeed d L₀ (ys z b none))
          (fun a b i => Bool.xor (a i) (b i)) (matchedBlockExtractor n 64 L₀ e₀)) := by
    unfold alternatingSeedWeight affineExtractionWeight
    rw [mapWeight_comp]
    unfold affinePhaseOneFirstLeft affinePhaseOneRightMessage affinePhaseOneFirstOutput
    simp only [matchedBlockExtractor_xor]
  rw [← actual] at projected
  simpa only [add_zero] using projected.trans first

end Algebraic.Cutwidth.Extractor.Internal
