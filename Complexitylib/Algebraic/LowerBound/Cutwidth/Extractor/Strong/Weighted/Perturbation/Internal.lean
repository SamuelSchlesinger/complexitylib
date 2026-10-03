/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Leakage
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Perturbing a source-correlated seed

Independent-seed leakage extraction applies to the uniformized joint law.
Deterministic processing pays the distance to that law once. Replacing its
retained marginal by the actual retained marginal costs at most the same
distance again, because uniformization contracts total variation.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem weightDist_uniformExtension_eq {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β] (p q : α → ℝ) :
    weightDist (uniformExtensionWeight β p) (uniformExtensionWeight β q) =
      weightDist p q := by
  have uniform := isProbabilityWeight_uniform β
  simp only [weightDist, uniformExtensionWeight, Fintype.sum_prod_type, ← sub_mul, abs_mul]
  simp_rw [abs_of_nonneg (uniform.1 _)]
  simp only [← Finset.mul_sum, uniform.2, mul_one]

private theorem weightDist_uniformSecond_le {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β] (p q : α × β → ℝ) :
    weightDist (uniformSecondWeight p) (uniformSecondWeight q) ≤ weightDist p q := by
  simp only [uniformSecondWeight, weightDist_uniformExtension_eq]
  rw [← mapWeight_fst, ← mapWeight_fst]
  exact weightDist_map_le p q Prod.fst

private def regroupSeedOutput (Tag Seed Out : Type*) :
    Seed × (Tag × Out) ≃ (Tag × Seed) × Out where
  toFun p := ((p.2.1, p.1), p.2.2)
  invFun p := (p.1.2, (p.1.1, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem independent_seed_dist_le {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    [Nonempty Seed] [Nonempty Out]
    {E : Source → Seed → Out} {K : Nat} {ε : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : (Tag × Source) × Seed → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, firstWeight p (t, x) ≤ μ t) :
    weightDist
      (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) (uniformSecondWeight p))
      (uniformSecondWeight
        (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2))
          (uniformSecondWeight p))) ≤ ε + (K : ℝ) * ∑ t, μ t := by
  let F := fun txs : (Tag × Source) × Seed => ((txs.1.1, txs.2), E txs.1.2 txs.2)
  have actual : mapWeight (regroupSeedOutput Tag Seed Out)
      (weightedSeededOutput (firstWeight p) (fun tx y => (tx.1, E tx.2 y))) =
        mapWeight F (uniformSecondWeight p) := by
    rw [weightedSeededOutput_eq_mapWeight, mapWeight_comp]
    simp only [uniformSecondWeight, div_eq_mul_inv]
    rfl
  have marginal : firstWeight (mapWeight F (uniformSecondWeight p)) =
      uniformExtensionWeight Seed (firstWeight (firstWeight p)) := by
    rw [← mapWeight_fst, mapWeight_comp]
    change mapWeight (fun txs : (Tag × Source) × Seed => (txs.1.1, txs.2))
      (uniformExtensionWeight Seed (firstWeight p)) = _
    rw [mapWeight_uniformExtension (firstWeight p) Prod.fst, mapWeight_fst]
  have ideal : mapWeight (regroupSeedOutput Tag Seed Out)
      (seedFamilyWeight (fun _ : Seed =>
        uniformExtensionWeight Out (firstWeight (firstWeight p)))) =
        uniformSecondWeight (mapWeight F (uniformSecondWeight p)) := by
    funext tso
    rw [mapWeight_equiv_apply]
    change (firstWeight (firstWeight p) tso.1.1 * (Fintype.card Out : ℝ)⁻¹) /
        (Fintype.card Seed : ℝ) =
      firstWeight (mapWeight F (uniformSecondWeight p)) tso.1 * (Fintype.card Out : ℝ)⁻¹
    rw [marginal]
    simp only [uniformExtensionWeight, uniformWeight, div_eq_mul_inv]
    ring
  have transport := weightDist_map_le
    (weightedSeededOutput (firstWeight p) (fun tx y => (tx.1, E tx.2 y)))
    (seedFamilyWeight (fun _ : Seed => uniformExtensionWeight Out (firstWeight (firstWeight p))))
    (regroupSeedOutput Tag Seed Out)
  rw [actual, ideal] at transport
  exact transport.trans
    (extract.leakage_dist_le error (firstWeight p) probability.first μ nonnegative cap)

theorem weightedStrongSeededExtractor_perturbed_seed_reference_dist_le
    {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    {E : Source → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : (Tag × Source) × Seed → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, firstWeight p (t, x) ≤ μ t)
    (seed : weightDist p (uniformSecondWeight p) ≤ δ) :
    weightDist (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)
      (uniformSecondWeight
        (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2))
          (uniformSecondWeight p))) ≤ ε + δ + (K : ℝ) * ∑ t, μ t := by
  obtain ⟨txs, _⟩ := probability.exists_pos
  let : Nonempty Seed := ⟨txs.2⟩
  let : Nonempty Out := ⟨E txs.1.2 txs.2⟩
  let F := fun txs : (Tag × Source) × Seed => ((txs.1.1, txs.2), E txs.1.2 txs.2)
  have extraction := independent_seed_dist_le extract error p probability μ nonnegative cap
  have transport := (weightDist_map_le p (uniformSecondWeight p) F).trans seed
  have triangle := weightDist_triangle (mapWeight F p)
    (mapWeight F (uniformSecondWeight p))
    (uniformSecondWeight (mapWeight F (uniformSecondWeight p)))
  linarith only [extraction, transport, triangle]

theorem weightedStrongSeededExtractor_perturbed_seed_dist_le
    {Tag Source Seed Out : Type*}
    [Fintype Tag] [Fintype Source] [Fintype Seed] [Fintype Out]
    {E : Source → Seed → Out} {K : Nat} {ε δ : ℝ}
    (extract : WeightedStrongSeededExtractor E K ε) (error : 0 ≤ ε)
    (p : (Tag × Source) × Seed → ℝ) (probability : IsProbabilityWeight p)
    (μ : Tag → ℝ) (nonnegative : ∀ t, 0 ≤ μ t)
    (cap : ∀ t x, firstWeight p (t, x) ≤ μ t)
    (seed : weightDist p (uniformSecondWeight p) ≤ δ) :
    weightDist (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)
      (uniformSecondWeight
        (mapWeight (fun txs => ((txs.1.1, txs.2), E txs.1.2 txs.2)) p)) ≤
      ε + 2 * δ + (K : ℝ) * ∑ t, μ t := by
  obtain ⟨txs, _⟩ := probability.exists_pos
  let : Nonempty Out := ⟨E txs.1.2 txs.2⟩
  let F := fun txs : (Tag × Source) × Seed => ((txs.1.1, txs.2), E txs.1.2 txs.2)
  have reference := weightedStrongSeededExtractor_perturbed_seed_reference_dist_le
    extract error p probability μ nonnegative cap seed
  have transport := (weightDist_map_le p (uniformSecondWeight p) F).trans seed
  have marginals := weightDist_uniformSecond_le
    (mapWeight F (uniformSecondWeight p)) (mapWeight F p)
  rw [weightDist_comm (mapWeight F (uniformSecondWeight p)) (mapWeight F p)] at marginals
  have triangle := weightDist_triangle (mapWeight F p)
    (uniformSecondWeight (mapWeight F (uniformSecondWeight p)))
    (uniformSecondWeight (mapWeight F p))
  linarith only [reference, transport, marginals, triangle]

end Algebraic.Cutwidth.Extractor.Internal
