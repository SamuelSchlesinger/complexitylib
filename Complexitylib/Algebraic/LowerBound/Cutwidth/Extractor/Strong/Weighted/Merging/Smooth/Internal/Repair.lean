/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Smooth.Internal.Basic
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Alternating.Internal
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability

/-!
# Repairing a left coordinate while keeping the entire original left state

Swap the latent sides to apply the checked rowwise uniform-coordinate
coupling, then swap back. The original left marginal is preserved on every
row, including null transcript rows. Therefore all actual prefixes and
tampered coordinates, as functions of that latent variable, remain unchanged.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem smooth_factored_left_lift {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (x : Z → A → X) :
    factoredWeight w (rightCoordinateLift l x) r =
      mapWeight (fun p : (Z × B) × A => (p.1, (p.2, x p.1.1 p.2)))
        (factoredWeight w l r) :=
  (smooth_factored_map_left w l r (fun z a => (a, x z a))).symm

theorem smooth_factored_forget_left {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (l' : Z → A × X → ℝ)
    (first : ∀ z, mapWeight Prod.fst (l' z) = l z) :
    mapWeight (fun p : (Z × B) × (A × X) => (p.1, p.2.1))
      (factoredWeight w l' r) = factoredWeight w l r := by
  rw [smooth_factored_map_left w l' r (fun _ => Prod.fst)]
  simp only [first]

theorem smooth_exists_uniform_left_repair {Z A B X : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (x : Z → A → X)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    ∃ l' : Z → A × X → ℝ, (∀ z, IsProbabilityWeight (l' z)) ∧
      (∀ z, mapWeight Prod.fst (l' z) = l z) ∧
      (∀ z, mapWeight Prod.snd (l' z) = uniformWeight X) ∧
      weightDist (factoredWeight w (rightCoordinateLift l x) r) (factoredWeight w l' r) ≤
        weightDist (retainedSeedWeight w l x) (uniformSecondWeight (retainedSeedWeight w l x)) := by
  obtain ⟨l', probability, first, second, distance⟩ :=
    exists_factored_uniform_right_repair_rows w r l x hw hr hl
  refine ⟨l', probability, first, second, ?_⟩
  have swapped := weightDist_map_le (factoredWeight w r (rightCoordinateLift l x))
    (factoredWeight w r l') (fun p : (Z × (A × X)) × B => ((p.1.1, p.2), p.1.2))
  rw [factoredWeight_swap, factoredWeight_swap] at swapped
  exact swapped.trans_eq distance

end Algebraic.Cutwidth.Extractor.Internal
