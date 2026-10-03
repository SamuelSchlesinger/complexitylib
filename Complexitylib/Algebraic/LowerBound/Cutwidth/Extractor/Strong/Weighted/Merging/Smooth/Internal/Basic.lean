/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal

/-!
# Exact original-law identities around a left prefix observation

The auxiliary laws expose a single actual prefix. The public smooth law
first conditions on its selected old left observation and then uses these
identities. Maps of the latent left state preserve all source multiplicities.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smooth_factored_map_left {Z A B C : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (f : Z → A → C) :
    mapWeight (fun p : (Z × B) × A => (p.1, f p.1.1 p.2)) (factoredWeight w l r) =
      factoredWeight w (fun z => mapWeight (f z) (l z)) r :=
  mapWeight_tagged (fun zb : Z × B => f zb.1)
    (fun zb => w zb.1 * r zb.1 zb.2) (fun zb => l zb.1)

theorem smooth_observedSeedWeight_eq_factored {Z A B V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (y : Z → B → Seed) (hl : ∀ z, IsProbabilityWeight (l z)) :
    observedSeedWeight w r v y =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1.1, v p.1.1 p.1.2), y p.1.1 p.1.2)) (factoredWeight w l r) := by
  unfold observedSeedWeight
  rw [← factoredWeight_right_marginal w l r hl, mapWeight_comp]

theorem smooth_observed_source_eq_retained {Z A U X : Type*}
    [Fintype Z] [Fintype A] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (x : Z → A → X)
    (hl : ∀ z a, 0 ≤ l z a) :
    observedSeedWeight w l u x =
      retainedSeedWeight (observedTranscriptWeight w l u)
        (observedTranscriptKernel l u) (fun zu => x zu.1) := by
  rw [show retainedSeedWeight (observedTranscriptWeight w l u)
      (observedTranscriptKernel l u) (fun zu => x zu.1) =
        fun zux => observedTranscriptWeight w l u zux.1 *
          mapWeight (x zux.1.1) (observedTranscriptKernel l u zux.1) zux.2 from
    mapWeight_tagged (fun zu : Z × U => x zu.1)
      (observedTranscriptWeight w l u) (observedTranscriptKernel l u)]
  funext ⟨⟨z, u₀⟩, x₀⟩
  rw [observedTranscript_left_source_eq w l x u hl]
  have mapped := congrFun (mapWeight_tagged (fun z a => (u z a, x z a)) w l)
    (z, (u₀, x₀))
  apply Eq.trans ?_ mapped
  simp only [observedSeedWeight, mapWeight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z' _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact propext (by simp only [Prod.mk.injEq, and_assoc])

/-- The actual right seed after a single original left prefix observation. -/
@[expose] noncomputable def smoothPrefixSeedWeight {Z A B Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed) : ((Z × Q) × V) × Seed → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let h := (p.1.1, q p.1.1 p.2)
    ((h, v h p.1.2), y h p.1.2)) (factoredWeight w l r)

/-- Actual extraction after a prefix, retaining every unchanged latent right value and left leak. -/
@[expose] noncomputable def smoothPrefixExtractionWeight {Z A B X Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → A → Q) (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (leak : Z × Q → V → A → W) (E : X → Seed → Out) :
    (((Z × Q) × B) × W) × Out → ℝ :=
  mapWeight (fun p : (Z × B) × A =>
    let h := (p.1.1, q p.1.1 p.2)
    (((h, p.1.2), leak h (v h p.1.2) p.2), E (x p.1.1 p.2) (y h p.1.2)))
    (factoredWeight w l r)

theorem smoothPrefixSeedWeight_eq_observed {Z A B Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → A → Q)
    (v : Z × Q → B → V) (y : Z × Q → B → Seed)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    smoothPrefixSeedWeight w l r q v y =
      observedSeedWeight (observedTranscriptWeight w l q) (fun zq => r zq.1) v y := by
  rw [smooth_observedSeedWeight_eq_factored _ (observedTranscriptKernel l q) _ v y
    (observedTranscriptKernel_probability l q hl)]
  rw [← factoredWeight_observe_left w l r q (fun z => (hl z).1), mapWeight_comp]
  rfl

theorem smoothMergingSeedWeight_eq_prefix {Z A B U Q V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed) (hl : ∀ z a, 0 ≤ l z a) :
    smoothMergingSeedWeight w l r u q v y =
      smoothPrefixSeedWeight (observedTranscriptWeight w l u) (observedTranscriptKernel l u)
        (fun zu => r zu.1) (fun zu => q zu.1) v y := by
  unfold smoothPrefixSeedWeight
  rw [← factoredWeight_observe_left w l r u hl, mapWeight_comp]
  rfl

theorem smoothTwoSidedExtractionWeight_eq_prefix {Z A B X U Q V W Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (q : Z → A → Q)
    (v : SmoothMergingTranscript Z U Q → B → V)
    (y : SmoothMergingTranscript Z U Q → B → Seed)
    (leak : SmoothMergingTranscript Z U Q → V → A → W) (E : X → Seed → Out)
    (hl : ∀ z a, 0 ≤ l z a) :
    smoothTwoSidedExtractionWeight w l r x u q v y leak E =
      smoothPrefixExtractionWeight (observedTranscriptWeight w l u)
        (observedTranscriptKernel l u) (fun zu => r zu.1)
        (fun zu => x zu.1) (fun zu => q zu.1) v y leak E := by
  unfold smoothPrefixExtractionWeight
  rw [← factoredWeight_observe_left w l r u hl, mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
