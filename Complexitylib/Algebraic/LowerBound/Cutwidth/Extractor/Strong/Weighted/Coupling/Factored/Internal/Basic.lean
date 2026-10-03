/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Mathlib.Tactic.Ring

/-!
# Factored-law lifts and exact distance averages

Keeping the left kernel normalized makes the distance between two
factored laws exactly the weighted average of their right-kernel distances.
No individual transcript row needs positive transcript mass.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem rightCoordinateLift_probability {Z B Q : Type*} [Fintype B] [Fintype Q]
    (r : Z → B → ℝ) (q : Z → B → Q) (hr : ∀ z, IsProbabilityWeight (r z)) (z : Z) :
    IsProbabilityWeight (rightCoordinateLift r q z) :=
  (hr z).map _

theorem rightCoordinateLift_fst {Z B Q : Type*} [Fintype B] [Fintype Q]
    (r : Z → B → ℝ) (q : Z → B → Q) (z : Z) :
    mapWeight Prod.fst (rightCoordinateLift r q z) = r z := by
  unfold rightCoordinateLift
  rw [mapWeight_comp]
  exact mapWeight_id _

theorem rightCoordinateLift_snd {Z B Q : Type*} [Fintype B] [Fintype Q]
    (r : Z → B → ℝ) (q : Z → B → Q) (z : Z) :
    mapWeight Prod.snd (rightCoordinateLift r q z) = mapWeight (q z) (r z) := by
  unfold rightCoordinateLift
  rw [mapWeight_comp]

theorem factoredWeight_map_right {Z A B C : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype C]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (f : Z → B → C) :
    mapWeight (fun p : (Z × B) × A => ((p.1.1, f p.1.1 p.1.2), p.2))
      (factoredWeight w l r) = factoredWeight w l (fun z => mapWeight (f z) (r z)) := by
  have tagged := mapWeight_tagged (fun za : Z × A => f za.1)
    (fun za => w za.1 * l za.1 za.2) (fun za => r za.1)
  have swapped := factoredWeight_swap w l r
  have restore := factoredWeight_swap w (fun z => mapWeight (f z) (r z)) l
  change mapWeight (fun p : (Z × A) × B => (p.1, f p.1.1 p.2))
    (factoredWeight w r l) = factoredWeight w (fun z => mapWeight (f z) (r z)) l at tagged
  rw [← swapped, mapWeight_comp] at tagged
  rw [← tagged, mapWeight_comp] at restore
  exact restore

theorem factoredWeight_rightCoordinateLift {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) :
    factoredWeight w l (rightCoordinateLift r q) =
      mapWeight (fun p : (Z × B) × A => ((p.1.1, (p.1.2, q p.1.1 p.1.2)), p.2))
        (factoredWeight w l r) :=
  (factoredWeight_map_right w l r (fun z b => (b, q z b))).symm

theorem factoredWeight_dist_right {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r r' : Z → B → ℝ)
    (nonnegative : ∀ z, 0 ≤ w z) (hl : ∀ z, IsProbabilityWeight (l z)) :
    weightDist (factoredWeight w l r) (factoredWeight w l r') =
      ∑ z, w z * weightDist (r z) (r' z) := by
  simp only [weightDist, factoredWeight, Fintype.sum_prod_type, ← sub_mul,
    ← mul_sub, abs_mul]
  simp_rw [abs_of_nonneg (nonnegative _), abs_of_nonneg ((hl _).1 _)]
  simp only [← Finset.mul_sum, (hl _).2, mul_one]
  simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem retainedSeedWeight_dist_eq_sum {Z B Q : Type*}
    [Fintype Z] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (r : Z → B → ℝ) (q : Z → B → Q)
    (nonnegative : ∀ z, 0 ≤ w z) (hr : ∀ z, IsProbabilityWeight (r z)) :
    weightDist (retainedSeedWeight w r q) (uniformSecondWeight (retainedSeedWeight w r q)) =
      ∑ z, w z * weightDist (mapWeight (q z) (r z)) (uniformWeight Q) := by
  have actual : retainedSeedWeight w r q =
      fun zu => w zu.1 * mapWeight (q zu.1) (r zu.1) zu.2 :=
    mapWeight_tagged q w r
  have marginal : firstWeight (retainedSeedWeight w r q) = w := by
    rw [actual]
    funext z
    simp only [firstWeight, ← Finset.mul_sum, ((hr z).map (q z)).2, mul_one]
  simp only [uniformSecondWeight, marginal]
  rw [actual]
  exact weightDist_tagged_mixture w (fun z => mapWeight (q z) (r z))
    (fun _ => uniformWeight Q) nonnegative

theorem rightCoordinateRepair_source_eq {Z B Q X : Type*}
    [Fintype B] [Fintype Q]
    (w : Z → ℝ) (r : Z → B → ℝ) (r' : Z → B × Q → ℝ)
    (same : ∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b)
    (x : Z → B → X) (z : Z) (x₀ : X) :
    w z * mapWeight (fun bq => x z bq.1) (r' z) x₀ =
      w z * mapWeight (x z) (r z) x₀ := by
  have point : (fun b => w z * mapWeight Prod.fst (r' z) b) =
      fun b => w z * r z b := funext (same z)
  have pushed := congrArg (fun p => mapWeight (x z) p x₀) point
  simpa only [mapWeight_mul, mapWeight_comp] using pushed

theorem factoredWeight_forget_right_eq {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (r' : Z → B × Q → ℝ)
    (same : ∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b) :
    mapWeight (fun p : (Z × (B × Q)) × A => ((p.1.1, p.1.2.1), p.2))
      (factoredWeight w l r') = factoredWeight w l r := by
  rw [factoredWeight_map_right w l r' (fun _ => Prod.fst)]
  funext p
  change (w p.1.1 * mapWeight Prod.fst (r' p.1.1) p.1.2) * l p.1.1 p.2 = _
  rw [same]
  rfl

end Algebraic.Cutwidth.Extractor.Internal
