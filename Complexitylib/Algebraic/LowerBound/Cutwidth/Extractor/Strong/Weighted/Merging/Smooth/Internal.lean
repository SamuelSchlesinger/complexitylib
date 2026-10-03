/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Uniform
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Repair
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Seed
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Mathlib.Tactic.Ring

/-!
# Two-sided merging after a conditional smooth-source repair

Repair the honest coordinate while preserving the full original left
state. All prefixes, right-seed choices, and retained leaks consequently
keep their original joint law. The exact retained marginal makes transfer
cost the original distance once. Conditioning first on the selected old
left observation gives the public smooth-source consumer.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smoothMergingSeedWeight_probability {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothMergingSeedWeight w l r u q v y) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem smoothTwoSidedExtractionWeight_probability {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Q]
    [Fintype W] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W) (E : X → Seed → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (smoothTwoSidedExtractionWeight w l r x u q v y leak E) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem smoothPrefixExtractionWeight_dist_le
    {Z A B X Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → A → Q) (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (leak : Z × Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (retainedSeedWeight w l x)
      (uniformSecondWeight (retainedSeedWeight w l x)) ≤ ρ)
    (seed : weightDist (smoothPrefixSeedWeight w l r q v y)
      (uniformSecondWeight (smoothPrefixSeedWeight w l r q v y)) ≤ δ) :
    weightDist (smoothPrefixExtractionWeight w l r x q v y leak E)
      (uniformSecondWeight (smoothPrefixExtractionWeight w l r x q v y leak E)) ≤
        ε + δ + ρ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X := by
  obtain ⟨l', hl', first, uniform, distance⟩ :=
    smooth_exists_uniform_left_repair w l r x hw hl hr
  let x' : Z → A × X → X := fun _ => Prod.snd
  let q' : Z → A × X → Q := fun z ax => q z ax.1
  let leak' : Z × Q → V → A × X → W := fun zq v₀ ax => leak zq v₀ ax.1
  have forget := smooth_factored_forget_left w l r l' first
  have seed_eq : smoothPrefixSeedWeight w l' r q' v y =
      smoothPrefixSeedWeight w l r q v y := by
    unfold smoothPrefixSeedWeight
    rw [← forget, mapWeight_comp]
  have bounded := smoothPrefixExtractionWeight_uniform_dist_le (δ := δ) extract error w l' r
    x' q' v y leak' hw hl' hr uniform (by rw [seed_eq]; exact seed)
  let evaluate : (Z × B) × (A × X) → (((Z × Q) × B) × W) × Out := fun p =>
    let h := (p.1.1, q p.1.1 p.2.1)
    (((h, p.1.2), leak h (v h p.1.2) p.2.1), E p.2.2 (y h p.1.2))
  have original : mapWeight evaluate (factoredWeight w (rightCoordinateLift l x) r) =
      smoothPrefixExtractionWeight w l r x q v y leak E := by
    rw [smooth_factored_left_lift, mapWeight_comp]
    rfl
  have near := (weightDist_map_le (factoredWeight w (rightCoordinateLift l x) r)
    (factoredWeight w l' r) evaluate).trans (distance.trans source)
  rw [original] at near
  change weightDist (smoothPrefixExtractionWeight w l r x q v y leak E)
    (smoothPrefixExtractionWeight w l' r x' q' v y leak' E) ≤ ρ at near
  have same : firstWeight (smoothPrefixExtractionWeight w l r x q v y leak E) =
      firstWeight (smoothPrefixExtractionWeight w l' r x' q' v y leak' E) := by
    unfold smoothPrefixExtractionWeight
    rw [← mapWeight_fst, ← mapWeight_fst, mapWeight_comp, mapWeight_comp]
    rw [← forget, mapWeight_comp]
  have transferred := weightDist_uniformSecond_le_of_dist_of_same_first near bounded same
  exact transferred.trans_eq (by ring)

theorem weightedStrongSeededExtractor_smooth_two_sided_dist_le
    {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (observedSeedWeight w l u x)
      (uniformSecondWeight (observedSeedWeight w l u x)) ≤ ρ)
    (seed : weightDist (smoothMergingSeedWeight w l r u q v y)
      (uniformSecondWeight (smoothMergingSeedWeight w l r u q v y)) ≤ δ) :
    weightDist (smoothTwoSidedExtractionWeight w l r x u q v y leak E)
      (uniformSecondWeight (smoothTwoSidedExtractionWeight w l r x u q v y leak E)) ≤
        ε + δ + ρ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X := by
  rw [smooth_observed_source_eq_retained w l u x (fun z => (hl z).1)] at source
  rw [smoothMergingSeedWeight_eq_prefix w l r u q v y (fun z => (hl z).1)] at seed
  rw [smoothTwoSidedExtractionWeight_eq_prefix w l r x u q v y leak E
    (fun z => (hl z).1)]
  exact smoothPrefixExtractionWeight_dist_le extract error
    (observedTranscriptWeight w l u) (observedTranscriptKernel l u) (fun zu => r zu.1)
    (fun zu => x zu.1) (fun zu => q zu.1) v y leak
    (observedTranscriptWeight_probability w l u hw hl)
    (observedTranscriptKernel_probability l u hl) (fun zu => hr zu.1) source seed

theorem weightedStrongSeededExtractor_smooth_two_sided_dist_le_of_prefix_seed
    {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype U] [Fintype Q]
    [Fintype V] [Fintype W] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ ρ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (source : weightDist (observedSeedWeight w l u x)
      (uniformSecondWeight (observedSeedWeight w l u x)) ≤ ρ)
    (seed : weightDist (observedSeedWeight (observedTranscriptWeight w l q)
      (fun zq => r zq.1) v y)
      (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w l q)
        (fun zq => r zq.1) v y)) ≤ δ) :
    weightDist (smoothTwoSidedExtractionWeight w l r x u q
      (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)) leak E)
      (uniformSecondWeight (smoothTwoSidedExtractionWeight w l r x u q
        (fun h => v (h.1.1, h.2)) (fun h => y (h.1.1, h.2)) leak E)) ≤
        ε + δ + ρ + (K : ℝ) * Fintype.card W * Fintype.card Q / Fintype.card X := by
  apply weightedStrongSeededExtractor_smooth_two_sided_dist_le extract error
    w l r x u q _ _ leak hw hl hr source
  rw [smoothMergingSeedWeight_prefix_dist w l r u q v y hw.1 hl]
  exact seed

end Algebraic.Cutwidth.Extractor.Internal
