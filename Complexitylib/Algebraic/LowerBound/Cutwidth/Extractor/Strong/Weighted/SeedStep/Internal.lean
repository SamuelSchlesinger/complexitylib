/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.BigOperators.Field

/-!
# Product-seed averaging and deterministic composition

Reassociating uniform seeds gives the product seed denominator. Finite
distance averaging then shows that adding a fresh independent seed and
applying a deterministic map cannot increase an earlier joint error.
The same finite pushforward identities identify successive seeded programs
with their deterministic composition.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem seedFamilyWeight_product {Earlier Fresh Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype Ω]
    (p : Earlier → Fresh → Ω → ℝ) :
    mapWeight (Equiv.prodAssoc Earlier Fresh Ω).symm
      (seedFamilyWeight (fun s => seedFamilyWeight (p s))) =
        seedFamilyWeight (fun sy : Earlier × Fresh => p sy.1 sy.2) := by
  funext syz
  rw [mapWeight_equiv_apply]
  simp [seedFamilyWeight, Fintype.card_prod, div_div, mul_comm]

theorem retainedSeedStep_seedFamilyWeight {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p : Earlier → X → ℝ) :
    retainedSeedStep F (seedFamilyWeight p) =
      seedFamilyWeight (fun sy : Earlier × Fresh =>
        mapWeight (fun x => F sy.1 x sy.2) (p sy.1)) := by
  funext syz
  rw [retainedSeedStep, mapWeight_equiv_apply]
  change
    mapWeight (fun sx : Earlier × X => (sx.1, F sx.1 sx.2 syz.1.2))
      (seedFamilyWeight p) (syz.1.1, syz.2) / (Fintype.card Fresh : ℝ) = _
  rw [mapWeight_seedFamilyWeight (fun s x => F s x syz.1.2) p]
  simp [seedFamilyWeight, Fintype.card_prod, div_div]

theorem weightDist_seedFamilyWeight_product {Earlier Fresh Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype Ω]
    (p q : Earlier → Fresh → Ω → ℝ) :
    weightDist (seedFamilyWeight (fun sy : Earlier × Fresh => p sy.1 sy.2))
      (seedFamilyWeight (fun sy : Earlier × Fresh => q sy.1 sy.2)) =
        (∑ s, weightDist (seedFamilyWeight (p s)) (seedFamilyWeight (q s))) /
          (Fintype.card Earlier : ℝ) := by
  simp only [weightDist_seedFamilyWeight, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

theorem weightedSeededOutput_dist_le {X Fresh Ω : Type*}
    [Fintype X] [Fintype Fresh] [Fintype Ω]
    (p q : X → ℝ) (F : X → Fresh → Ω) :
    weightDist (weightedSeededOutput p F) (weightedSeededOutput q F) ≤ weightDist p q := by
  change weightDist
      (seedFamilyWeight (fun y => mapWeight (fun x => F x y) p))
      (seedFamilyWeight (fun y => mapWeight (fun x => F x y) q)) ≤ _
  rw [weightDist_seedFamilyWeight]
  by_cases empty : Fintype.card Fresh = 0
  · simp only [empty, Nat.cast_zero, div_zero]
    exact weightDist_nonneg p q
  · have positive : (0 : ℝ) < Fintype.card Fresh := by
      exact_mod_cast Nat.pos_of_ne_zero empty
    apply (div_le_iff₀ positive).mpr
    calc
      _ ≤ ∑ _y : Fresh, weightDist p q :=
        Finset.sum_le_sum fun y _ => weightDist_map_le p q (fun x => F x y)
      _ = _ := by simp [mul_comm]

theorem retainedSeedStep_dist_le {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p q : Earlier × X → ℝ) :
    weightDist (retainedSeedStep F p) (retainedSeedStep F q) ≤ weightDist p q :=
  (weightDist_map_le _ _ (retainSeedEquiv Earlier Fresh Ω)).trans
    (weightedSeededOutput_dist_le p q (fun sx y => (sx.1, F sx.1 sx.2 y)))

theorem probabilityWeight_retainedSeedStep {Earlier Fresh X Ω : Type*}
    [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω] [Nonempty Fresh]
    {p : Earlier × X → ℝ} (probability : IsProbabilityWeight p)
    (F : Earlier → X → Fresh → Ω) : IsProbabilityWeight (retainedSeedStep F p) :=
  (probability.weightedSeededOutput (fun sx y => (sx.1, F sx.1 sx.2 y))).map
    (retainSeedEquiv Earlier Fresh Ω)

theorem retainedSeedStep_weightedSeededOutput {A Earlier Fresh X Ω : Type*}
    [Fintype A] [Fintype Earlier] [Fintype Fresh] [Fintype X] [Fintype Ω]
    (F : Earlier → X → Fresh → Ω) (p : A → ℝ) (E : A → Earlier → X) :
    retainedSeedStep F (weightedSeededOutput p E) =
      weightedSeededOutput p (fun a (sy : Earlier × Fresh) => F sy.1 (E a sy.1) sy.2) := by
  change retainedSeedStep F
    (seedFamilyWeight (fun y => mapWeight (fun a => E a y) p)) = _
  rw [retainedSeedStep_seedFamilyWeight]
  funext syz
  simp only [seedFamilyWeight, weightedSeededOutput, mapWeight_comp]

end Algebraic.Cutwidth.Extractor.Internal
