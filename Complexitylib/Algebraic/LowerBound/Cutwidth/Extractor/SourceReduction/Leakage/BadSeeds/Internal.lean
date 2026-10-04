/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Leakage.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Adaptive witnesses and finite bad-seed counting

Choose one actual shift and tuple of tampered seeds on each bad honest
seed. The average bound for this deterministic choice controls the sum
over the bad set. No rowwise discrepancy or source normalization is used
in the counting argument.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem affineLeakageOutputWeight_probability {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool)
    (b : Fin n → Bool) (y : Fin d → Bool) (ys : Fin t → Fin d → Bool)
    (probability : IsProbabilityWeight p) :
    IsProbabilityWeight (affineLeakageOutputWeight cb p leak advice b y ys) :=
  probability.map _

theorem mem_affineLeakageBadSeeds {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool) :
    y ∈ affineLeakageBadSeeds cb p leak advice γ ↔ ∃ b ys,
      γ < weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys)) := by
  classical
  simp [affineLeakageBadSeeds]

theorem not_mem_affineLeakageBadSeeds {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) (γ : ℝ) (y : Fin d → Bool) :
    y ∉ affineLeakageBadSeeds cb p leak advice γ ↔ ∀ b ys,
      weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys)) ≤ γ := by
  rw [mem_affineLeakageBadSeeds]
  simp only [not_exists, not_lt]

theorem affineLeakageBadSeeds_card_le {n d t : Nat} {Out : Type*} [Fintype Out]
    (cb : (Fin n → Bool) → (Fin d → Bool) → List Bool → Out)
    (p : (Fin n → Bool) → ℝ)
    (leak : (Fin n → Bool) → Option (Fin t) → Fin d → Bool)
    (advice : Option (Fin t) → List Bool) {γ ε : ℝ} (positive : 0 < γ)
    (average : ∀ g : (Fin d → Bool) → Fin n → Bool,
      ∀ f : (Fin d → Bool) → Fin t → Fin d → Bool,
      (∑ y, uniformWeight (Fin d → Bool) y *
        weightDist (affineLeakageOutputWeight cb p leak advice (g y) y (f y))
          (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice (g y) y (f y)))) ≤ ε) :
    ((affineLeakageBadSeeds cb p leak advice γ).card : ℝ) ≤
      (ε / γ) * Fintype.card (Fin d → Bool) := by
  classical
  let bad := affineLeakageBadSeeds cb p leak advice γ
  have witnesses (y : Fin d → Bool) : ∃ b ys, y ∈ bad →
      γ < weightDist (affineLeakageOutputWeight cb p leak advice b y ys)
        (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice b y ys)) := by
    by_cases hy : y ∈ bad
    · obtain ⟨b, ys, bound⟩ := (mem_affineLeakageBadSeeds cb p leak advice γ y).mp hy
      exact ⟨b, ys, fun _ => bound⟩
    · exact ⟨fun _ => false, fun _ _ => false, fun member => (hy member).elim⟩
  choose g f witness using witnesses
  let score (y : Fin d → Bool) :=
    weightDist (affineLeakageOutputWeight cb p leak advice (g y) y (f y))
      (uniformSecondWeight (affineLeakageOutputWeight cb p leak advice (g y) y (f y)))
  have nonnegative (y : Fin d → Bool) : 0 ≤ score y := weightDist_nonneg _ _
  have counted : γ * (bad.card : ℝ) ≤ ∑ y, score y := by
    calc
      _ = ∑ _y ∈ bad, γ := by simp [mul_comm]
      _ ≤ ∑ y ∈ bad, score y := Finset.sum_le_sum fun y hy => (witness y hy).le
      _ ≤ ∑ y, score y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _ => nonnegative y)
  have seed_positive : 0 < (Fintype.card (Fin d → Bool) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have averaged := average g f
  change (∑ y, (Fintype.card (Fin d → Bool) : ℝ)⁻¹ * score y) ≤ ε at averaged
  rw [← Finset.mul_sum, inv_mul_le_iff₀ seed_positive] at averaged
  have bound := counted.trans averaged
  rw [div_mul_eq_mul_div, le_div_iff₀ positive]
  simpa only [bad, mul_comm] using bound

end Algebraic.Cutwidth.Extractor.Internal
