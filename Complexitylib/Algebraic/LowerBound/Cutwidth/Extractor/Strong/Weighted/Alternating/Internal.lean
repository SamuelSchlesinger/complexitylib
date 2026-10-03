/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Switching the source and seed sides after an observation

An exact observation update followed by swapping the two sides supplies
the conditional product law used by retained extraction. All identities
keep the original source variables and include impossible messages.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem factoredWeight_swap {Z A B : Type*} [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) :
    mapWeight (fun p : (Z × B) × A => ((p.1.1, p.2), p.1.2)) (factoredWeight w l r) =
      factoredWeight w r l := by
  let e : ((Z × B) × A) ≃ ((Z × A) × B) :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun p => ((p.1.1, p.2), p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  funext p
  change mapWeight e (factoredWeight w l r) p = _
  rw [mapWeight_equiv_apply]
  dsimp [e, factoredWeight]
  ring

theorem factoredWeight_right_marginal {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    mapWeight Prod.fst (factoredWeight w l r) = fun zb => w zb.1 * r zb.1 zb.2 := by
  rw [mapWeight_fst]
  funext zb
  simp only [firstWeight, factoredWeight, ← Finset.mul_sum, (hl _).2, mul_one]

theorem retainedSeedWeight_eq_factored {Z A B Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (y : Z → B → Seed)
    (hl : ∀ z, IsProbabilityWeight (l z)) :
    retainedSeedWeight w r y =
      mapWeight (fun p : (Z × B) × A => (p.1.1, y p.1.1 p.1.2)) (factoredWeight w l r) := by
  unfold retainedSeedWeight
  rw [← factoredWeight_right_marginal w l r hl, mapWeight_comp]

theorem factoredWeight_observe_swap {Z A B V : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (v : Z → B → V)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    mapWeight (fun p : (Z × B) × A => (((p.1.1, v p.1.1 p.1.2), p.2), p.1.2))
      (factoredWeight w l r) =
      factoredWeight (observedTranscriptWeight w r v) (observedTranscriptKernel r v)
        (fun zv => l zv.1) := by
  have observed := factoredWeight_observe_right w l r v (fun z => (hr z).1)
  have swapped := factoredWeight_swap (observedTranscriptWeight w r v)
    (fun zv => l zv.1) (observedTranscriptKernel r v)
  rw [← observed, mapWeight_comp] at swapped
  exact swapped

theorem alternatingSeedWeight_eq_retained {Z A B V Seed : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    alternatingSeedWeight w l r v s =
      retainedSeedWeight (observedTranscriptWeight w r v) (fun zv => l zv.1) s := by
  rw [retainedSeedWeight_eq_factored _ (observedTranscriptKernel r v) _ _
    (observedTranscriptKernel_probability r v hr)]
  rw [← factoredWeight_observe_swap w l r v hr, mapWeight_comp]
  rfl

theorem alternatingExtractionWeight_eq_retained {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (E : X → Seed → Out) (hr : ∀ z, IsProbabilityWeight (r z)) :
    alternatingExtractionWeight w l r v s x E =
      retainedExtractionWeight (observedTranscriptWeight w r v)
        (observedTranscriptKernel r v) (fun zv => l zv.1) (fun zv => x zv.1) s E := by
  unfold retainedExtractionWeight
  rw [← factoredWeight_observe_swap w l r v hr, mapWeight_comp]
  rfl

theorem alternatingExtractionWeight_probability {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (E : X → Seed → Out) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (alternatingExtractionWeight w l r v s x E) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem weightedStrongSeededExtractor_alternating_joint_dist_le
    {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype X]
    [Fintype Seed] [Fintype Out] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (μ : Z × V → ℝ) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z))
    (nonnegative : ∀ zv, 0 ≤ μ zv)
    (cap : ∀ z v₀ x₀, w z * mapWeight (fun b => (v z b, x z b)) (r z) (v₀, x₀) ≤ μ (z, v₀))
    (seed : weightDist (alternatingSeedWeight w l r v s)
      (uniformSecondWeight (alternatingSeedWeight w l r v s)) ≤ δ) :
    weightDist (alternatingExtractionWeight w l r v s x E)
      (uniformSecondWeight (alternatingExtractionWeight w l r v s x E)) ≤
        ε + δ + (K : ℝ) * ∑ zv, μ zv := by
  have jointCap (zv : Z × V) (x₀ : X) :
      observedTranscriptWeight w r v zv *
        mapWeight (x zv.1) (observedTranscriptKernel r v zv) x₀ ≤ μ zv := by
    rw [observedTranscript_left_source_eq w r x v (fun z => (hr z).1)]
    exact cap zv.1 zv.2 x₀
  rw [alternatingSeedWeight_eq_retained w l r v s hr] at seed
  rw [alternatingExtractionWeight_eq_retained w l r v s x E hr]
  exact extract.retained_dist_le error (observedTranscriptWeight w r v)
    (observedTranscriptKernel r v) (fun zv => l zv.1) (fun zv => x zv.1) s μ
    (observedTranscriptWeight_probability w r v hw hr)
    (observedTranscriptKernel_probability r v hr) (fun zv => hl zv.1)
    nonnegative jointCap seed

theorem weightedStrongSeededExtractor_alternating_dist_le
    {Z A B V X Seed Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype X]
    [Fintype Seed] [Fintype Out] [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (s : Z × V → A → Seed) (x : Z → B → X)
    (μ : Z → ℝ) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z))
    (nonnegative : ∀ z, 0 ≤ μ z)
    (cap : ∀ z x₀, w z * mapWeight (x z) (r z) x₀ ≤ μ z)
    (seed : weightDist (alternatingSeedWeight w l r v s)
      (uniformSecondWeight (alternatingSeedWeight w l r v s)) ≤ δ) :
    weightDist (alternatingExtractionWeight w l r v s x E)
      (uniformSecondWeight (alternatingExtractionWeight w l r v s x E)) ≤
        ε + δ + (K : ℝ) * Fintype.card V * ∑ z, μ z := by
  have cap' (z : Z) (v₀ : V) (x₀ : X) :
      w z * mapWeight (fun b => (v z b, x z b)) (r z) (v₀, x₀) ≤ μ z := by
    rw [← observedTranscript_left_source_eq w r x v (fun z => (hr z).1) (z, v₀) x₀]
    exact observedTranscript_left_envelope w r x v μ hw.1 (fun z => (hr z).1)
      cap (z, v₀) x₀
  have bound := weightedStrongSeededExtractor_alternating_joint_dist_le extract error
    w l r v s x (fun zv => μ zv.1) hw hl hr (fun zv => nonnegative zv.1) cap' seed
  simpa [Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc] using bound

theorem affineAlternatingWeight_eq_alternating {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (combine : X → X → X)
    (E : X → Seed → Mid) (F : Y → Mid → Out) (translate : Mid → Mid ≃ Mid)
    (linear : ∀ a b s, E (combine a b) s = translate (E b s) (E a s)) :
    affineAlternatingWeight w l r x mask y source combine E F =
      alternatingExtractionWeight w l r (fun z b => (y z b, E (mask z b) (y z b)))
        (fun zv a => translate zv.2.2 (E (x zv.1 a) zv.2.1)) source F := by
  simp only [affineAlternatingWeight, alternatingExtractionWeight, linear]

theorem affineAlternatingSeed_eq_map {Z A B X Seed Mid : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Mid]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (combine : X → X → X) (E : X → Seed → Mid) (translate : Mid → Mid ≃ Mid)
    (linear : ∀ a b s, E (combine a b) s = translate (E b s) (E a s)) :
    alternatingSeedWeight w l r (fun z b => (y z b, E (mask z b) (y z b)))
        (fun zv a => translate zv.2.2 (E (x zv.1 a) zv.2.1)) =
      mapWeight (fun p : (Z × B) × Mid =>
        ((p.1.1, (y p.1.1 p.1.2, E (mask p.1.1 p.1.2) (y p.1.1 p.1.2))), p.2))
        (affineExtractionWeight w l r x mask y combine E) := by
  unfold alternatingSeedWeight affineExtractionWeight
  rw [mapWeight_comp]
  simp only [linear]

theorem affineAlternatingWeight_probability {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Seed] [Fintype Mid] [Fintype Out]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (combine : X → X → X)
    (E : X → Seed → Mid) (F : Y → Mid → Out)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (affineAlternatingWeight w l r x mask y source combine E F) :=
  (factoredWeight_probability w l r hw hl hr).map _

theorem weightedStrongSeededExtractor_affine_alternating_dist_le
    {Z A B X Seed Mid Y Out : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X] [Fintype Seed]
    [Fintype Mid] [Fintype Y] [Fintype Out]
    [Nonempty Seed] [Nonempty Mid] [Nonempty Out]
    {E : X → Seed → Mid} {F : Y → Mid → Out} {K L : Nat} {ε η δ : ℝ}
    (first : WeightedStrongSeededExtractor E K ε) (first_error : 0 ≤ ε)
    (second : WeightedStrongSeededExtractor F L η) (second_error : 0 ≤ η)
    (combine : X → X → X) (translate : Mid → Mid ≃ Mid)
    (linear : ∀ a b s, E (combine a b) s = translate (E b s) (E a s))
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (x : Z → A → X) (mask : Z → B → X) (y : Z → B → Seed)
    (source : Z → B → Y) (μ ν : Z → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z))
    (left_nonnegative : ∀ z, 0 ≤ μ z) (right_nonnegative : ∀ z, 0 ≤ ν z)
    (left_cap : ∀ z x₀, w z * mapWeight (x z) (l z) x₀ ≤ μ z)
    (right_cap : ∀ z y₀, w z * mapWeight (source z) (r z) y₀ ≤ ν z)
    (seed : weightDist (retainedSeedWeight w r y)
      (uniformSecondWeight (retainedSeedWeight w r y)) ≤ δ) :
    weightDist (affineAlternatingWeight w l r x mask y source combine E F)
      (uniformSecondWeight (affineAlternatingWeight w l r x mask y source combine E F)) ≤
        η + (ε + δ + (K : ℝ) * ∑ z, μ z) +
          (L : ℝ) * Fintype.card (Seed × Mid) * ∑ z, ν z := by
  have first_bound := first.affine_dist_le first_error combine
    (fun b s => translate (E b s)) linear w l r x mask y μ hw hl hr
    left_nonnegative left_cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (affineExtractionWeight w l r x mask y combine E)
    (fun zb => (zb.1, (y zb.1 zb.2, E (mask zb.1 zb.2) (y zb.1 zb.2))))
  rw [← affineAlternatingSeed_eq_map w l r x mask y combine E translate linear] at projected
  rw [affineAlternatingWeight_eq_alternating w l r x mask y source combine E F translate linear]
  exact weightedStrongSeededExtractor_alternating_dist_le second second_error w l r
    (fun z b => (y z b, E (mask z b) (y z b)))
    (fun zv a => translate zv.2.2 (E (x zv.1 a) zv.2.1)) source ν hw hl hr
    right_nonnegative right_cap (projected.trans first_bound)

end Algebraic.Cutwidth.Extractor.Internal
