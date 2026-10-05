/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Weighted

/-!
# Collision budgets for biased Boolean features

An average collision bound replaces the maximum-fibre hypothesis in weighted
counting. Dividing each pulled-back message weight by its fibre size normalizes
the mass; two logarithmic mean inequalities then charge biased coordinates.
No independence assumption is made on the features.

The differential-uniformity collision estimate used by applications is classical:
Kölsch, Kriepke, and Kyureghyan, "Image sets of perfectly nonlinear maps" (2022),
Lemma 2 and Corollary 1, https://doi.org/10.1007/s10623-022-01094-4.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- The number of ordered pairs of inputs with equal keys, including the diagonal. -/
noncomputable def collisionCount {X T : Type*} [Fintype X] (key : X → T) : ℕ :=
  ∑ x, (Finset.univ.filter fun y => key y = key x).card

/-- Refining equality of keys cannot increase their number of collisions. -/
theorem collisionCount_le_of_refines {X T U : Type*} [Fintype X]
    (key : X → T) (coarse : X → U)
    (refines : ∀ x y, key x = key y → coarse x = coarse y) :
    collisionCount key ≤ collisionCount coarse := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, refines y x (Finset.mem_filter.mp hy).2⟩

/-- Reindex ordered collisions by their input displacement. -/
theorem collisionCount_eq_sum_differences {X T : Type*} [Fintype X] [AddGroup X]
    (key : X → T) :
    collisionCount key =
      ∑ d, (Finset.univ.filter fun x => key (x + d) = key x).card := by
  unfold collisionCount
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ x, ∑ y, if key y = key x then 1 else 0) =
        ∑ x, ∑ d, if key (x + d) = key x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Equiv.sum_comp (Equiv.addLeft x) (fun y => if key y = key x then 1 else 0)).symm
    _ = _ := Finset.sum_comm

/-- A bound on every nonzero difference gives the classical ordered-collision budget. -/
theorem collisionCount_le_of_differences {X T : Type*} [Fintype X] [AddGroup X]
    (key : X → T) {δ : ℕ}
    (differences : ∀ d : X, d ≠ 0 →
      (Finset.univ.filter fun x => key (x + d) = key x).card ≤ δ) :
    collisionCount key ≤ Fintype.card X + δ * (Fintype.card X - 1) := by
  rw [collisionCount_eq_sum_differences]
  calc
    (∑ d, (Finset.univ.filter fun x => key (x + d) = key x).card) ≤
        ∑ d : X, if d = 0 then Fintype.card X else δ := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : d = 0
      · simp [hd]
      · simpa only [hd, ↓reduceIte] using differences d hd
    _ = Fintype.card X + δ * (Fintype.card X - 1) := by
      rw [Finset.sum_ite]
      simp [Finset.filter_ne', mul_comm]
      have eq : (Finset.univ.filter fun x : X => x = 0) = {0} := by
        ext x
        simp
      rw [eq, Finset.card_singleton]

/-- Dividing pulled-back weights by their fibre sizes leaves mass at most one. -/
theorem sum_weight_div_fibre_le {X T : Type*} [Fintype X] [Fintype T]
    (key : X → T) (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (mass : ∑ t, weight t = 1) :
    (∑ x, weight (key x) / (Finset.univ.filter fun y => key y = key x).card) ≤ 1 := by
  classical
  rw [← mass, ← Finset.sum_fiberwise Finset.univ key]
  apply Finset.sum_le_sum
  intro t _
  have same : (∑ x ∈ Finset.univ.filter (fun x => key x = t),
      weight (key x) / (Finset.univ.filter fun y => key y = key x).card) =
      ∑ _x ∈ Finset.univ.filter (fun x => key x = t),
        weight t / (Finset.univ.filter fun y => key y = t).card := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [same]
  simp only [Finset.sum_const, nsmul_eq_mul]
  by_cases zero : (Finset.univ.filter fun y => key y = t).card = 0
  · simp only [zero, Nat.cast_zero, zero_mul]
    exact nonneg t
  · have nz : ((Finset.univ.filter fun y => key y = t).card : ℝ) ≠ 0 := by
      exact_mod_cast zero
    rw [mul_div_cancel₀ _ nz]

/-- Average collisions, rather than the largest fibre, suffice to charge biased features. -/
theorem log_card_le_of_collisions_and_bias {X ι : Type*} [Fintype X] [Nonempty X]
    [Fintype ι] (key : X → (ι → Bool)) (biased : Finset ι) (rare : ι → Bool)
    {D : ℝ} (hD : 0 < D)
    (collisions : (collisionCount key : ℝ) ≤ Fintype.card X * D)
    (bias : ∀ i ∈ biased,
      4 * (Finset.univ.filter fun x => key x i = rare i).card ≤ Fintype.card X) :
    Real.log (Fintype.card X) ≤ Real.log D + Fintype.card ι * Real.log 2 -
      biased.card * biasSaving := by
  let tag (i : ι) : Bool := decide (i ∈ biased)
  let weight := messageWeight tag rare
  let fibre (x : X) : ℝ := (Finset.univ.filter fun y => key y = key x).card
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have positive (x : X) : 0 < fibre x := by
    apply Nat.cast_pos.mpr
    exact Finset.card_pos.mpr ⟨x, by simp⟩
  have fibreSum : ∑ x, fibre x ≤ Fintype.card X * D := by
    change (∑ x, ((Finset.univ.filter fun y => key y = key x).card : ℝ)) ≤ _
    rw [← Nat.cast_sum]
    convert collisions using 2
    congr 1
    funext x
    congr 1
    ext y
    simp only [Finset.mem_filter]
  have fibreLog := sum_log_le_of_sum_le fibre positive hD fibreSum
  have mass := sum_weight_div_fibre_le key weight
    (fun m => (messageWeight_pos tag rare m).le) (sum_messageWeight tag rare)
  have upper := sum_log_le_of_sum_le (fun x => weight (key x) / fibre x)
    (fun x => div_pos (messageWeight_pos tag rare _) (positive x))
    (div_pos (by norm_num : (0 : ℝ) < 1) hN)
    (by
      rw [mul_one_div_cancel hN.ne']
      convert mass using 2
      rename_i x _
      apply congrArg (fun t : ℝ => weight (key x) / t)
      change ((Finset.univ.filter fun y => key y = key x).card : ℝ) = _
      congr 2
      ext y
      simp only [Finset.mem_filter])
  have logs (x : X) : Real.log (weight (key x) / fibre x) =
      Real.log (weight (key x)) - Real.log (fibre x) :=
    Real.log_div (messageWeight_pos tag rare _).ne' (positive x).ne'
  simp_rw [logs] at upper
  rw [Finset.sum_sub_distrib] at upper
  simp only [one_div, Real.log_inv] at upper
  have lower := sum_log_messageWeight_ge key biased rare bias
  change -(Fintype.card X : ℝ) * (Fintype.card ι * Real.log 2 -
    biased.card * biasSaving) ≤ ∑ x, Real.log (weight (key x)) at lower
  nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
