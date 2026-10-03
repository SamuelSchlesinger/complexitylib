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
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Internal
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Internal.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling.Factored.Internal.Transfer

/-!
# Uniform-coordinate repair preserving the original source factors

A distinguished deterministic coordinate of the right source can be
replaced by a coordinate uniform given the transcript. The original right
marginal and the entire left kernel remain unchanged. The repaired
coordinate may still be correlated with the original right state.

The full factored-law distance is exactly the original retained-coordinate
discrepancy. Original source envelopes are therefore preserved, including
at null transcript rows. The construction uses the checked correlated
marginal-replacement coupling on normalized right kernels and averages its
exact distance identities; no repair witness is assumed.

Deterministic continuation pays this distance once when its retained
marginal is preserved. A comparison with an unrestricted actual retained
marginal explicitly pays it twice. The transfer bounds also apply to
arbitrary signed weights and empty alphabets.

The coupling is credited in `Strong.Weighted.Coupling`. This factored
specialization supplies a finite repair needed when iterating the
look-ahead argument of Chattopadhyay--Goyal--Li, Lemmas 6.5 and 6.8:
<https://arxiv.org/pdf/1505.00107>. It does not assume that approximate
uniformity itself gives a pointwise source-mass cap.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Appending the actual coordinate preserves normalization of each original right kernel. -/
theorem rightCoordinateLift_probability {Z B Q : Type*} [Fintype B] [Fintype Q]
    (r : Z → B → ℝ) (q : Z → B → Q) (hr : ∀ z, IsProbabilityWeight (r z)) (z : Z) :
    IsProbabilityWeight (rightCoordinateLift r q z) :=
  Internal.rightCoordinateLift_probability r q hr z

/-- The lifted factored law is exactly a deterministic image of the original joint law. -/
theorem factoredWeight_rightCoordinateLift {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q) :
    factoredWeight w l (rightCoordinateLift r q) =
      mapWeight (fun p : (Z × B) × A => ((p.1.1, (p.1.2, q p.1.1 p.1.2)), p.2))
        (factoredWeight w l r) :=
  Internal.factoredWeight_rightCoordinateLift w l r q

/-- Preserving the weighted right marginal preserves every original right-source envelope. -/
theorem rightCoordinateRepair_source_eq {Z B Q X : Type*}
    [Fintype B] [Fintype Q]
    (w : Z → ℝ) (r : Z → B → ℝ) (r' : Z → B × Q → ℝ)
    (same : ∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b)
    (x : Z → B → X) (z : Z) (x₀ : X) :
    w z * mapWeight (fun bq => x z bq.1) (r' z) x₀ =
      w z * mapWeight (x z) (r z) x₀ :=
  Internal.rightCoordinateRepair_source_eq w r r' same x z x₀

/-- Discarding the repaired coordinate recovers the entire original factored joint law. -/
theorem factoredWeight_forget_right_eq {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (r' : Z → B × Q → ℝ)
    (same : ∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b) :
    mapWeight (fun p : (Z × (B × Q)) × A => ((p.1.1, p.1.2.1), p.2))
      (factoredWeight w l r') = factoredWeight w l r :=
  Internal.factoredWeight_forget_right_eq w l r r' same

/-- A uniform coordinate repair preserves both original sources at exactly the joint seed error. -/
theorem exists_factored_uniform_right_repair_rows {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    ∃ r' : Z → B × Q → ℝ, (∀ z, IsProbabilityWeight (r' z)) ∧
      (∀ z, mapWeight Prod.fst (r' z) = r z) ∧
      (∀ z, mapWeight Prod.snd (r' z) = uniformWeight Q) ∧
      weightDist (factoredWeight w l (rightCoordinateLift r q)) (factoredWeight w l r') =
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) :=
  Internal.exists_factored_uniform_right_repair_rows w l r q hw hl hr

/-- The same repair has the corresponding weighted marginal identities on every row. -/
theorem exists_factored_uniform_right_repair {Z A B Q : Type*}
    [Fintype Z] [Fintype A] [Fintype B] [Fintype Q]
    (w : Z → ℝ) (l : Z → A → ℝ) (r : Z → B → ℝ) (q : Z → B → Q)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    ∃ r' : Z → B × Q → ℝ, (∀ z, IsProbabilityWeight (r' z)) ∧
      (∀ z b, w z * mapWeight Prod.fst (r' z) b = w z * r z b) ∧
      (∀ z u, w z * mapWeight Prod.snd (r' z) u = w z * uniformWeight Q u) ∧
      weightDist (factoredWeight w l (rightCoordinateLift r q)) (factoredWeight w l r') =
        weightDist (retainedSeedWeight w r q)
          (uniformSecondWeight (retainedSeedWeight w r q)) :=
  Internal.exists_factored_uniform_right_repair w l r q hw hl hr

/-- A repair preserving the retained marginal costs its total variation distance once. -/
theorem weightDist_uniformSecond_le_of_dist_of_same_first {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] {p q : Tag × Out → ℝ} {ρ ε : ℝ}
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist q (uniformSecondWeight q) ≤ ε)
    (same : firstWeight p = firstWeight q) :
    weightDist p (uniformSecondWeight p) ≤ ρ + ε :=
  Internal.weightDist_uniformSecond_le_of_dist_of_same_first near uniform same

/-- An unrestricted repair costs at most twice its distance against the actual retained marginal. -/
theorem weightDist_uniformSecond_le_of_dist {Tag Out : Type*}
    [Fintype Tag] [Fintype Out] {p q : Tag × Out → ℝ} {ρ ε : ℝ}
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist q (uniformSecondWeight q) ≤ ε) :
    weightDist p (uniformSecondWeight p) ≤ 2 * ρ + ε :=
  Internal.weightDist_uniformSecond_le_of_dist near uniform

/-- Deterministic continuation pays once when its retained marginal is preserved. -/
theorem weightDist_uniformSecond_map_le_of_dist_of_same_first {α Tag Out : Type*}
    [Fintype α] [Fintype Tag] [Fintype Out]
    {p q : α → ℝ} {ρ ε : ℝ} (F : α → Tag × Out)
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist (mapWeight F q) (uniformSecondWeight (mapWeight F q)) ≤ ε)
    (same : firstWeight (mapWeight F p) = firstWeight (mapWeight F q)) :
    weightDist (mapWeight F p) (uniformSecondWeight (mapWeight F p)) ≤ ρ + ε :=
  Internal.weightDist_uniformSecond_map_le_of_dist_of_same_first F near uniform same

/-- Deterministic continuation pays twice when its actual retained marginal may change. -/
theorem weightDist_uniformSecond_map_le_of_dist {α Tag Out : Type*}
    [Fintype α] [Fintype Tag] [Fintype Out]
    {p q : α → ℝ} {ρ ε : ℝ} (F : α → Tag × Out)
    (near : weightDist p q ≤ ρ)
    (uniform : weightDist (mapWeight F q) (uniformSecondWeight (mapWeight F q)) ≤ ε) :
    weightDist (mapWeight F p) (uniformSecondWeight (mapWeight F p)) ≤ 2 * ρ + ε :=
  Internal.weightDist_uniformSecond_map_le_of_dist F near uniform

end Algebraic.Cutwidth.Extractor
