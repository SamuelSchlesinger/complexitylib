/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Finite mixture identities for retained tags

Deterministic pushforwards are linear in arbitrary real weights. Retaining
a mixture tag makes total variation an exact weighted sum; forgetting it
can only decrease the distance. Uniform seed families are a specialization,
including the empty seed type under the usual zero-division convention.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem mapWeight_mul {α β : Type*} [Fintype α]
    (f : α → β) (c : ℝ) (p : α → ℝ) :
    mapWeight f (fun x => c * p x) = fun y => c * mapWeight f p y := by
  funext y
  simp [mapWeight, Finset.mul_sum]

theorem mapWeight_sum {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, p i x) = fun y => ∑ i, mapWeight f (p i) y := by
  funext y
  simp only [mapWeight]
  calc
    (∑ x, if f x = y then ∑ i, p i x else 0) =
        ∑ x, ∑ i, if f x = y then p i x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ i, ∑ x, if f x = y then p i x else 0 := Finset.sum_comm

theorem mapWeight_mixture {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight f (fun x => ∑ i, w i * p i x) =
      fun y => ∑ i, w i * mapWeight f (p i) y := by
  rw [mapWeight_sum]
  simp only [mapWeight_mul]

theorem mapWeight_tagged {ι α β : Type*} [Fintype ι] [Fintype α]
    (f : ι → α → β) (w : ι → ℝ) (p : ι → α → ℝ) :
    mapWeight (fun ix : ι × α => (ix.1, f ix.1 ix.2))
      (fun ix => w ix.1 * p ix.1 ix.2) =
        fun iz => w iz.1 * mapWeight (f iz.1) (p iz.1) iz.2 := by
  funext iz
  rcases iz with ⟨i, z⟩
  simp only [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp [Finset.mul_sum]

theorem mapWeight_seedFamilyWeight {Seed α β : Type*}
    [Fintype Seed] [Fintype α] (f : Seed → α → β) (p : Seed → α → ℝ) :
    mapWeight (fun yz : Seed × α => (yz.1, f yz.1 yz.2)) (seedFamilyWeight p) =
      seedFamilyWeight (fun y => mapWeight (f y) (p y)) := by
  unfold seedFamilyWeight
  simpa only [div_eq_mul_inv, mul_comm] using
    mapWeight_tagged f (fun _ => (Fintype.card Seed : ℝ)⁻¹) p

theorem seedFamilyWeight_mixture {ι Seed Ω : Type*} [Fintype ι] [Fintype Seed]
    (w : ι → ℝ) (p : ι → Seed → Ω → ℝ) :
    seedFamilyWeight (fun y z => ∑ i, w i * p i y z) =
      fun yz => ∑ i, w i * seedFamilyWeight (p i) yz := by
  funext yz
  simp only [seedFamilyWeight, Finset.sum_div, mul_div_assoc]

theorem weightDist_tagged_mixture {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p q : ι → α → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun ix : ι × α => w ix.1 * p ix.1 ix.2)
      (fun ix => w ix.1 * q ix.1 ix.2) = ∑ i, w i * weightDist (p i) (q i) := by
  unfold weightDist
  rw [Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (nonnegative i)]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem weightDist_mixture_le {ι α : Type*} [Fintype ι] [Fintype α]
    (w : ι → ℝ) (p q : ι → α → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun x => ∑ i, w i * p i x) (fun x => ∑ i, w i * q i x) ≤
      ∑ i, w i * weightDist (p i) (q i) := by
  have forget (r : ι → α → ℝ) :
      mapWeight Prod.snd (fun ix : ι × α => w ix.1 * r ix.1 ix.2) =
        fun x => ∑ i, w i * r i x := by
    funext x
    exact mapWeight_snd_apply _ x
  rw [← forget p, ← forget q]
  exact (weightDist_map_le _ _ Prod.snd).trans_eq
    (weightDist_tagged_mixture w p q nonnegative)

theorem weightDist_seedFamilyWeight {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]
    (p q : Seed → Ω → ℝ) :
    weightDist (seedFamilyWeight p) (seedFamilyWeight q) =
      (∑ y, weightDist (p y) (q y)) / (Fintype.card Seed : ℝ) := by
  unfold seedFamilyWeight
  have identity := weightDist_tagged_mixture
    (fun _ : Seed => (Fintype.card Seed : ℝ)⁻¹) p q (fun _ => by positivity)
  simpa only [div_eq_mul_inv, mul_comm, Finset.mul_sum] using identity

theorem weightDist_weightedSeededOutput_seedFamilyWeight {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    (p : α → ℝ) (C : α → Seed → Ω) (q : Seed → Ω → ℝ) :
    weightDist (weightedSeededOutput p C) (seedFamilyWeight q) =
      (∑ y, weightDist (mapWeight (fun x => C x y) p) (q y)) /
        (Fintype.card Seed : ℝ) :=
  weightDist_seedFamilyWeight (fun y => mapWeight (fun x => C x y) p) q

end Algebraic.Cutwidth.Extractor.Internal
