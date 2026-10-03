/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.FixedTampering.Second.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.LookAhead.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional

/-!
# Exact seed averaging and laws for the second-output refresh

A normalized message from the independent left kernel only splits each
old transcript row. It preserves the original retained-seed discrepancy
exactly after averaging, including null messages. The deterministic laws
below then identify the actual second seed and final retained transcript.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem retainedSeedWeight_dist_eq {Z B Seed : Type*}
    [Fintype Z] [Fintype B] [Fintype Seed]
    (w : Z → ℝ) (r : Z → B → ℝ) (s : Z → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (retainedSeedWeight w r s) (uniformSecondWeight (retainedSeedWeight w r s)) =
      ∑ z, w z * weightDist (mapWeight (s z) (r z)) (uniformWeight Seed) := by
  have mass (z : Z) : ∑ seed, mapWeight (s z) (r z) seed = 1 := ((hr z).map (s z)).2
  have ideal : uniformSecondWeight (fun zs : Z × Seed =>
      w zs.1 * mapWeight (s zs.1) (r zs.1) zs.2) =
        fun zs => w zs.1 * uniformWeight Seed zs.2 := by
    funext zs
    simp only [uniformSecondWeight, uniformExtensionWeight, firstWeight,
      ← Finset.mul_sum, mass, mul_one]
  rw [retainedSeedWeight, mapWeight_tagged, ideal]
  exact weightDist_tagged_mixture w (fun z => mapWeight (s z) (r z))
    (fun _ => uniformWeight Seed) hw

theorem retainedSeedWeight_observe_left_dist {Z A B U Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype U] [Fintype Seed]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (f : Z → A → U) (s : Z → B → Seed)
    (hw : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (retainedSeedWeight (observedTranscriptWeight w l f)
      (fun zu => r zu.1) (fun zu => s zu.1))
      (uniformSecondWeight (retainedSeedWeight (observedTranscriptWeight w l f)
        (fun zu => r zu.1) (fun zu => s zu.1))) =
      weightDist (retainedSeedWeight w r s) (uniformSecondWeight (retainedSeedWeight w r s)) := by
  rw [retainedSeedWeight_dist_eq _ _ _
      (observedTranscriptWeight_nonnegative w l f hw (fun z => (hl z).1))
      (fun zu => hr zu.1), retainedSeedWeight_dist_eq w r s hw hr]
  simp only [Fintype.sum_prod_type, observedTranscriptWeight]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul, ← Finset.mul_sum, ((hl z).map (f z)).2, mul_one]

theorem fixedTamperingSecondRefreshWeight_probability
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight
      (fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem fixedTamperingSecond_seed_eq_map
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out) :
    alternatingSeedWeight (observedTranscriptWeight w l leak)
        (observedTranscriptKernel l leak) (fun zm => r zm.1)
        (fixedTamperingRightMessage q y' R)
        (fun t a => (fixedTamperingSecondHonestMessage x initialSeed W QExt t a).2) =
      mapWeight (fun p : (((Z × Mid) × B) × (Mid × Mid)) × Mid =>
        ((p.1.1.1, fixedTamperingRightMessage q y' R p.1.1.1 p.1.1.2), p.2))
        (lookAheadExtractionWeight (observedTranscriptWeight w l leak)
          (observedTranscriptKernel l leak) (fun zm => r zm.1)
          (fun zm => x zm.1) (fun zm => x zm.1) (fun zm => q zm.1) (fun zm => q zm.1)
          initialSeed W QExt) := by
  unfold alternatingSeedWeight lookAheadExtractionWeight
  rw [mapWeight_comp]
  rfl

theorem fixedTamperingSecondRefreshWeight_eq_alternating_map
    {Z A B X Q Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid] [Fintype Q] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (q : Z → B → Q) (y y' : Z → B → Y)
    (leak : Z → A → Mid) (initialSeed : Q → Seed)
    (W : X → Seed → Mid) (QExt : Q → Mid → Seed) (R : Y → Mid → Out)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    fixedTamperingSecondRefreshWeight w l r x q y y' leak initialSeed W QExt R =
      mapWeight (fun p : (((Z × Mid) × (Q × Out)) × A) × Out =>
        (((p.1.1, fixedTamperingSecondHonestMessage x initialSeed W QExt p.1.1 p.1.2),
          p.1.2), p.2))
        (alternatingExtractionWeight (observedTranscriptWeight w l leak)
          (observedTranscriptKernel l leak) (fun zm => r zm.1)
          (fixedTamperingRightMessage q y' R)
          (fun t a => (fixedTamperingSecondHonestMessage x initialSeed W QExt t a).2)
          (fun zm => y zm.1) R) := by
  unfold alternatingExtractionWeight
  rw [← factoredWeight_observe_left w l r leak (fun z => (hl z).1),
    mapWeight_comp, mapWeight_comp]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
