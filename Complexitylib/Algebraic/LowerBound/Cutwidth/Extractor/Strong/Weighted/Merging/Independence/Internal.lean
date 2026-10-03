/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Independence.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Linarith

/-!
# Merging the independence of two selected tampering sets

Retain the source copies in `T`, the seed copies in `S`, and the extracted
outputs in `S`. The two-sided leakage theorem applies with extra alphabet
`S → Out`. Its retained data reconstruct every output in `S ∪ T`, choosing
the stored output on overlaps. Processing that side information preserves
the independent uniform comparison law.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private def independenceMergingSide {Z X Seed Out : Type*} {t : Nat}
    (E : X → Seed → Out) (S T : Finset (Fin t))
    (p : (Z × (Seed × (Fin t → Seed))) × ((T → X) × (S → Out))) :
    (Z × (Seed × (Fin t → Seed))) × (↥(S ∪ T) → Out) :=
  (p.1, fun j => if member : j.1 ∈ S then p.2.2 ⟨j.1, member⟩
    else E (p.2.1 ⟨j.1, (Finset.mem_union.mp j.2).resolve_left member⟩) (p.1.2.2 j.1))

private theorem independenceMergingWeight_eq_map_twoSided {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed] [Fintype Out]
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (E : X → Seed → Out)
    (S T : Finset (Fin t)) :
    mapWeight (fun p => (independenceMergingSide E S T p.1, p.2))
      (twoSidedExtractionWeight w l r (fun _ a => a.1) (fun _ b => b.1)
        (fun _ a (j : T) => a.2 j) (fun _ b (j : S) => b.2 j)
        (fun _ ys a (j : S) => E (a.2 j) (ys j)) E) =
      independenceMergingWeight w l r E S T := by
  classical
  rw [twoSidedExtractionWeight_eq_map, mapWeight_comp]
  unfold independenceMergingWeight
  congr 1
  funext p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      dsimp only [independenceMergingSide]
      split <;> rfl
  · rfl

theorem weightedStrongSeededExtractor_independence_merging_dist_le
    {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (S T : Finset (Fin t))
    (μ : Z × (T → X) → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ zu, 0 ≤ μ zu)
    (cap : ∀ z u x,
      w z * mapWeight (fun a => ((fun j : T => a.2 j), a.1)) (l z) (u, x) ≤ μ (z, u))
    (seed : weightDist
      (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))
      (uniformSecondWeight
        (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))) ≤ δ) :
    weightDist (independenceMergingWeight w l r E S T)
      (uniformSecondWeight (independenceMergingWeight w l r E S T)) ≤
        ε + δ + (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ zu, μ zu := by
  have bound := extract.two_sided_leakage_dist_le error w l r
    (fun _ a => a.1) (fun _ b => b.1)
    (fun _ a (j : T) => a.2 j) (fun _ b (j : S) => b.2 j)
    (fun _ ys a (j : S) => E (a.2 j) (ys j)) μ hw hl hr nonnegative cap seed
  have projected := weightDist_uniformSecond_map_first_le
    (twoSidedExtractionWeight w l r (fun _ a => a.1) (fun _ b => b.1)
      (fun _ a (j : T) => a.2 j) (fun _ b (j : S) => b.2 j)
      (fun _ ys a (j : S) => E (a.2 j) (ys j)) E)
    (independenceMergingSide E S T)
  rw [independenceMergingWeight_eq_map_twoSided] at projected
  exact projected.trans (by
    simpa only [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow] using bound)

theorem weightedStrongSeededExtractor_independence_merging_dist_le_of_budget
    {Z X Seed Out : Type*} {t : Nat}
    [Fintype Z] [Fintype X] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : X → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (w : Z → ℝ) (l : Z → (X × (Fin t → X)) → ℝ)
    (r : Z → (Seed × (Fin t → Seed)) → ℝ) (S T : Finset (Fin t))
    (μ : Z × (T → X) → ℝ)
    (hw : IsProbabilityWeight w) (hl : ∀ z, IsProbabilityWeight (l z))
    (hr : ∀ z, IsProbabilityWeight (r z)) (nonnegative : ∀ zu, 0 ≤ μ zu)
    (cap : ∀ z u x,
      w z * mapWeight (fun a => ((fun j : T => a.2 j), a.1)) (l z) (u, x) ≤ μ (z, u))
    (seed : weightDist
      (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))
      (uniformSecondWeight
        (observedSeedWeight w r (fun _ b (j : S) => b.2 j) (fun _ b => b.1))) ≤ δ)
    (budget : (K : ℝ) * (Fintype.card Out : ℝ) ^ S.card * ∑ zu, μ zu ≤ ε) :
    weightDist (independenceMergingWeight w l r E S T)
      (uniformSecondWeight (independenceMergingWeight w l r E S T)) ≤ 2 * ε + δ := by
  have bound := weightedStrongSeededExtractor_independence_merging_dist_le
    extract error w l r S T μ hw hl hr nonnegative cap seed
  linarith only [bound, budget]

end Algebraic.Cutwidth.Extractor.Internal
