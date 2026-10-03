/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs

/-!
# Finite laws for extraction with two-sided leakage

A transcript indexes independent left and right distributions. The source
and its first leak depend on the left variable; the seed and its transcript
depend on the right variable. An additional finite leak may depend on the
left variable and the right transcript together. All maps count every source
occurrence, including collisions. The laws remain defined for arbitrary real
weights; normalization and independence are hypotheses of the theorems.

These finite laws support the independence-merging argument of
Chattopadhyay--Liao, *Extractors for Sum of Two Sources* (2021), Lemma 3.26,
<https://arxiv.org/abs/2110.12652>.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

variable {Z A B X Seed Out U V W : Type*}

/-- Independent left and right laws conditioned on a shared transcript, retaining the right tag. -/
noncomputable def factoredWeight (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (p : (Z × B) × A) : ℝ :=
  w p.1.1 * r p.1.1 p.1.2 * l p.1.1 p.2

/-- The joint law of the transcript, right-side observation, and actual seed. -/
noncomputable def observedSeedWeight [Fintype Z] [Fintype B]
    (w : Z → ℝ) (r : Z → B → ℝ) (v : Z → B → V) (y : Z → B → Seed) :
    (Z × V) × Seed → ℝ :=
  mapWeight (fun zb : Z × B => ((zb.1, v zb.1 zb.2), y zb.1 zb.2))
    (fun zb => w zb.1 * r zb.1 zb.2)

/-- The source law retaining both observations and the additional finite leak. -/
noncomputable def leakageSourceWeight [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (p : ((Z × V) × (U × W)) × X) : ℝ :=
  let z := p.1.1.1
  let v₀ := p.1.1.2
  w z * mapWeight (v z) (r z) v₀ *
    mapWeight (fun a => ((u z a, leak z v₀ a), x z a)) (l z) (p.1.2, p.2)

/-- Extraction retaining the full right variable, the left observation, and the extra leak. -/
noncomputable def twoSidedExtractionWeight [Fintype A]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (y : Z → B → Seed) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (E : X → Seed → Out)
    (p : ((Z × B) × (U × W)) × Out) : ℝ :=
  let z := p.1.1.1
  let b := p.1.1.2
  w z * r z b * mapWeight
    (fun a => ((u z a, leak z (v z b) a), E (x z a) (y z b))) (l z) (p.1.2, p.2)

end Algebraic.Cutwidth.Extractor
