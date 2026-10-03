/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Coupling
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Tactic.Ring

/-!
# Coupling conditionally on an external transcript

Couple each normalized transcript row and average using the unchanged
transcript marginal. Null rows contribute zero. The coupling's kernel
identity survives this scaling without a positivity premise on any row.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem conditionalCoupling_factor {Z A : Type*} [Fintype Z] [Fintype A]
    {p : Z × A → ℝ} (hp : IsProbabilityWeight p) :
    (fun za : Z × A => firstWeight p za.1 * conditionalWeight p za.1 za.2) = p := by
  funext za
  exact conditionalWeight_factor p hp.1 za.1 za.2

theorem conditionalCoupling_first_factor {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} (hp : IsProbabilityWeight p) :
    mapWeight (fun zab => (zab.1, zab.2.1)) p =
      fun za => firstWeight p za.1 * firstWeight (conditionalWeight p za.1) za.2 := by
  conv_lhs => arg 2; rw [← conditionalCoupling_factor hp]
  simpa only [mapWeight_fst] using mapWeight_tagged
    (fun (_ : Z) (ab : A × B) => ab.1) (firstWeight p) (conditionalWeight p)

theorem conditionalCoupling_dist_eq {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} {q : Z × A → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q)
    (same : firstWeight p = firstWeight q) :
    weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q =
      ∑ z, firstWeight p z *
        weightDist (firstWeight (conditionalWeight p z)) (conditionalWeight q z) := by
  rw [conditionalCoupling_first_factor hp]
  conv_lhs => arg 2; rw [← conditionalCoupling_factor hq, ← same]
  exact weightDist_tagged_mixture (firstWeight p)
    (fun z => firstWeight (conditionalWeight p z)) (conditionalWeight q) hp.first.1
theorem exists_conditional_marginal_replacement_kernel {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} {q : Z × A → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q)
    (same : firstWeight p = firstWeight q) :
    ∃ ρ : (Z × (A × B)) × A → ℝ, IsProbabilityWeight ρ ∧
      (∀ zab, ∑ a', ρ (zab, a') = p zab) ∧
      (∀ z a', ∑ ab, ρ ((z, ab), a') = q (z, a')) ∧
      (∑ t with t.1.2.1 ≠ t.2, ρ t) =
        weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q ∧
      ∀ z a b a', (∑ b', p (z, (a, b'))) * ρ ((z, (a, b)), a') =
        p (z, (a, b)) * (∑ b', ρ ((z, (a, b')), a')) := by
  obtain ⟨⟨z₀, a₀, b₀⟩, _⟩ := hp.exists_pos
  let : Nonempty A := ⟨a₀⟩
  let : Nonempty B := ⟨b₀⟩
  choose row probability preserve replace disagreement kernel using
    fun z => Algebraic.Cutwidth.Extractor.exists_marginal_replacement_kernel
      (hp.conditionalWeight z) (hq.conditionalWeight z)
  let ρ (t : (Z × (A × B)) × A) :=
    firstWeight p t.1.1 * row t.1.1 (t.1.2, t.2)
  have old (zab : Z × (A × B)) : ∑ a', ρ (zab, a') = p zab := by
    simp only [ρ, ← Finset.mul_sum, preserve]
    exact conditionalWeight_factor p hp.1 zab.1 zab.2
  have new (z : Z) (a' : A) : ∑ ab, ρ ((z, ab), a') = q (z, a') := by
    simp only [ρ, ← Finset.mul_sum, replace, same]
    exact conditionalWeight_factor q hq.1 z a'
  have total : ∑ t, ρ t = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [old, hp.2]
  refine ⟨ρ, ⟨fun t => mul_nonneg (hp.first.1 _) ((probability _).1 _), total⟩,
    old, new, ?_, ?_⟩
  · calc
      (∑ t with t.1.2.1 ≠ t.2, ρ t) =
          ∑ z, firstWeight p z * (∑ t with t.1.1 ≠ t.2, row z t) := by
        simp only [Finset.sum_filter, Fintype.sum_prod_type, ρ, Finset.mul_sum,
          mul_ite, mul_zero]
      _ = ∑ z, firstWeight p z *
          weightDist (firstWeight (conditionalWeight p z)) (conditionalWeight q z) := by
        simp only [disagreement]
      _ = _ := (conditionalCoupling_dist_eq hp hq same).symm
  · intro z a b a'
    simp only [ρ, ← conditionalWeight_factor p hp.1, ← Finset.mul_sum]
    calc
      _ = (firstWeight p z) ^ 2 *
          (firstWeight (conditionalWeight p z) a * row z ((a, b), a')) := by
        unfold firstWeight
        ring
      _ = (firstWeight p z) ^ 2 *
          (conditionalWeight p z (a, b) * ∑ b', row z ((a, b'), a')) := by
        rw [kernel]
      _ = _ := by ring
private theorem mapWeight_retained_first {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (p : (Z × B) × A → ℝ) (z : Z) (a : A) :
    mapWeight (fun t => (t.1.1, t.2)) p (z, a) = ∑ b, p ((z, b), a) := by
  simp [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp

private theorem mapWeight_retained_second {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    (p : Z × (A × B) → ℝ) (z : Z) (b : B) :
    mapWeight (fun t => (t.1, t.2.2)) p (z, b) = ∑ a, p (z, (a, b)) := by
  simp [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem exists_conditional_joint_marginal_replacement {Z A B : Type*}
    [Fintype Z] [Fintype A] [Fintype B]
    {p : Z × (A × B) → ℝ} {q : Z × A → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q)
    (same : firstWeight p = firstWeight q) :
    ∃ p' : Z × (A × B) → ℝ, IsProbabilityWeight p' ∧
      mapWeight (fun zab => (zab.1, zab.2.1)) p' = q ∧
      (∀ z b, ∑ a, p' (z, (a, b)) = ∑ a, p (z, (a, b))) ∧
      weightDist p p' = weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q := by
  obtain ⟨ρ, hρ, preserve, replace, disagreement, _⟩ :=
    exists_conditional_marginal_replacement_kernel hp hq same
  let f (t : (Z × (A × B)) × A) := t.1
  let g (t : (Z × (A × B)) × A) := (t.1.1, (t.2, t.1.2.2))
  let p' := mapWeight g ρ
  have old : mapWeight f ρ = p := by
    funext zab
    rw [show f = Prod.fst from rfl, mapWeight_fst]
    exact preserve zab
  have new : mapWeight (fun t => (t.1.1, t.2)) ρ = q := by
    funext za
    rw [mapWeight_retained_first]
    exact replace za.1 za.2
  have first : mapWeight (fun zab => (zab.1, zab.2.1)) p' = q := by
    rw [mapWeight_comp]
    exact new
  have second : mapWeight (fun zab => (zab.1, zab.2.2)) p' =
      mapWeight (fun zab => (zab.1, zab.2.2)) p := by
    change mapWeight _ (mapWeight g ρ) = _
    rw [mapWeight_comp, ← old, mapWeight_comp]
  have upper : weightDist p p' ≤
      weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q := by
    have bound := weightDist_map_map_le hρ f g
    rw [old] at bound
    have mismatch : (∑ t with f t ≠ g t, ρ t) =
        ∑ t with t.1.2.1 ≠ t.2, ρ t := by
      congr 1
      ext ⟨⟨z, a, b⟩, a'⟩
      simp [f, g]
    calc
      weightDist p p' ≤ ∑ t with f t ≠ g t, ρ t := by
        convert bound using 1
        congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = _ := mismatch.trans disagreement
  have lower : weightDist (mapWeight (fun zab => (zab.1, zab.2.1)) p) q ≤
      weightDist p p' := by
    have bound := weightDist_map_le p p' (fun zab => (zab.1, zab.2.1))
    simpa only [first] using bound
  refine ⟨p', hρ.map g, first, ?_, le_antisymm upper lower⟩
  intro z b
  simpa only [mapWeight_retained_second] using congrFun second (z, b)

end Algebraic.Cutwidth.Extractor.Internal
