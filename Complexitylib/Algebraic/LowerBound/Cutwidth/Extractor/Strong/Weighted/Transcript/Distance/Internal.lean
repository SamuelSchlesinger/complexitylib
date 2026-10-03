/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Transport
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Transcript.Envelope
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Seed

/-!
# Transporting uniformity through independent messages

Balanced output maps contract conditional uniformity error. Relabeling an
observation and applying a transcript-dependent output bijection also
contract it. An observation of the independent opposite source preserves
the averaged error exactly, including null transcript rows.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightDist_uniformSecond_map_output_le {Z X Y : Type*}
    [Fintype Z] [Fintype X] [Fintype Y]
    (p : Z × X → ℝ) (f : X → Y)
    (balanced : mapWeight f (uniformWeight X) = uniformWeight Y) :
    weightDist (mapWeight (fun zx => (zx.1, f zx.2)) p)
      (uniformSecondWeight (mapWeight (fun zx => (zx.1, f zx.2)) p)) ≤
        weightDist p (uniformSecondWeight p) := by
  have uniform : mapWeight (fun zx => (zx.1, f zx.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun zx => (zx.1, f zx.2)) p) := by
    unfold uniformSecondWeight
    rw [firstWeight_map_fiber p (fun _ : Z => f)]
    unfold uniformExtensionWeight
    rw [mapWeight_tagged (fun _ : Z => f) (firstWeight p)
      (fun _ : Z => uniformWeight X), balanced]
  rw [← uniform]
  exact weightDist_map_le p (uniformSecondWeight p) _

theorem observedSeedWeight_image_dist_le {Z A U X Y : Type*}
    [Fintype Z] [Fintype A] [Fintype U] [Fintype X] [Fintype Y]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (x : Z → A → X)
    (f : X → Y) (balanced : mapWeight f (uniformWeight X) = uniformWeight Y) :
    weightDist (observedSeedWeight w l u (fun z a => f (x z a)))
      (uniformSecondWeight (observedSeedWeight w l u (fun z a => f (x z a)))) ≤
        weightDist (observedSeedWeight w l u x)
          (uniformSecondWeight (observedSeedWeight w l u x)) := by
  have bound := weightDist_uniformSecond_map_output_le (observedSeedWeight w l u x) f balanced
  simpa only [observedSeedWeight, mapWeight_comp] using bound

theorem observedSeedWeight_transform_dist_le {Z A U V X Y : Type*}
    [Fintype Z] [Fintype A] [Fintype U] [Fintype V] [Fintype X] [Fintype Y]
    (w : Z → ℝ) (l : Z → A → ℝ) (u : Z → A → U) (x : Z → A → X)
    (f : Z → U → V) (e : Z → X ≃ Y) :
    weightDist (observedSeedWeight w l (fun z a => f z (u z a))
      (fun z a => e z (x z a)))
      (uniformSecondWeight (observedSeedWeight w l (fun z a => f z (u z a))
        (fun z a => e z (x z a)))) ≤
      weightDist (observedSeedWeight w l u x)
        (uniformSecondWeight (observedSeedWeight w l u x)) := by
  let p := observedSeedWeight w l u x
  have projected := weightDist_uniformSecond_map_first_le
    (mapWeight (fun ux : (Z × U) × X => (ux.1, e ux.1.1 ux.2)) p)
    (fun zu : Z × U => (zu.1, f zu.1 zu.2))
  rw [weightDist_uniformSecond_fiberEquiv p (fun zu => e zu.1)] at projected
  simpa only [p, observedSeedWeight, mapWeight_comp] using projected

theorem observedSeedWeight_observe_other_dist {Z A B V U X : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype V] [Fintype U] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ)
    (g : Z → B → V) (u : Z → A → U) (x : Z → A → X)
    (hw : ∀ z, 0 ≤ w z) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (observedSeedWeight (observedTranscriptWeight w r g) (fun zv => l zv.1)
      (fun zv => u zv.1) (fun zv => x zv.1))
      (uniformSecondWeight (observedSeedWeight (observedTranscriptWeight w r g)
        (fun zv => l zv.1) (fun zv => u zv.1) (fun zv => x zv.1))) =
      weightDist (observedSeedWeight w l u x)
        (uniformSecondWeight (observedSeedWeight w l u x)) := by
  rw [smooth_observedSeedWeight_dist_eq _ _ _ _
    (observedTranscriptWeight_nonnegative w r g hw (fun z => (hr z).1)),
    smooth_observedSeedWeight_dist_eq w l u x hw]
  simp only [Fintype.sum_prod_type, observedTranscriptWeight]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul, ← Finset.mul_sum, ((hr z).map (g z)).2, mul_one]

end Algebraic.Cutwidth.Extractor.Internal
