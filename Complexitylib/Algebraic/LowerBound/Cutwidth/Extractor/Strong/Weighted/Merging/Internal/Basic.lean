/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Merging.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Mathlib.Tactic.Positivity

/-!
# Finite factorization identities for two-sided leakage

The actual observations preserve multiplicities. Regrouping product tags
exposes normalized left rows and the exact right observation law; the row
envelope is charged once for every value of the additional finite leak.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open scoped Classical

theorem merging_probability_tagged {ι α : Type*} [Fintype ι] [Fintype α]
    {w : ι → ℝ} {p : ι → α → ℝ} (hw : IsProbabilityWeight w)
    (hp : ∀ i, IsProbabilityWeight (p i)) :
    IsProbabilityWeight (fun ix : ι × α => w ix.1 * p ix.1 ix.2) := by
  refine ⟨fun ix => mul_nonneg (hw.1 _) ((hp _).1 _), ?_⟩
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (hp _).2, mul_one]
  exact hw.2

theorem merging_probability_nested {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    {w : ι → ℝ} {p : ι → α × β → ℝ} (hw : IsProbabilityWeight w)
    (hp : ∀ i, IsProbabilityWeight (p i)) :
    IsProbabilityWeight (fun ix : (ι × α) × β => w ix.1.1 * p ix.1.1 (ix.1.2, ix.2)) := by
  refine ⟨fun ix => mul_nonneg (hw.1 _) ((hp _).1 _), ?_⟩
  simp only [Fintype.sum_prod_type]
  have mass (i : ι) : ∑ a, ∑ b, p i (a, b) = 1 := by
    simpa only [Fintype.sum_prod_type] using (hp i).2
  simp only [← Finset.mul_sum, mass, mul_one]
  exact hw.2

theorem merging_sum_mapWeight_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → ℝ) :
    ∑ b, mapWeight f p b * g b = ∑ a, p a * g (f a) := by
  simp only [mapWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem merging_map_nested {ι α β γ : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (w : ι → ℝ) (p : ι → α × β → ℝ) (f : ι → β → γ) :
    mapWeight (fun itx : (ι × α) × β => (itx.1, f itx.1.1 itx.2))
      (fun itx => w itx.1.1 * p itx.1.1 (itx.1.2, itx.2)) =
      fun ito => w ito.1.1 *
        mapWeight (fun tx : α × β => (tx.1, f ito.1.1 tx.2))
          (p ito.1.1) (ito.1.2, ito.2) := by
  funext ⟨⟨i, t⟩, o⟩
  have equality := congrFun
    (mapWeight_tagged (fun i (tx : α × β) => (tx.1, f i tx.2)) w p) (i, (t, o))
  simpa only [mapWeight, Fintype.sum_prod_type, Prod.mk.injEq, and_assoc] using equality

theorem merging_map_refinement_le {α U W X : Type*} [Fintype α]
    (p : α → ℝ) (nonnegative : ∀ a, 0 ≤ p a)
    (u : α → U) (leak : α → W) (x : α → X) (u₀ : U) (w₀ : W) (x₀ : X) :
    mapWeight (fun a => ((u a, leak a), x a)) p ((u₀, w₀), x₀) ≤
      mapWeight (fun a => (u a, x a)) p (u₀, x₀) := by
  unfold mapWeight
  apply Finset.sum_le_sum
  intro a _
  by_cases condition : ((u a, leak a), x a) = ((u₀, w₀), x₀)
  · have coarse : (u a, x a) = (u₀, x₀) := by
      exact Prod.ext (congrArg (fun p => p.1.1) condition)
        (congrArg (fun p : (U × W) × X => p.2) condition)
    simp only [ite_eq_left condition, ite_eq_left coarse, le_refl]
  · simp only [ite_eq_right condition]
    split_ifs <;> first | exact nonnegative a | exact le_rfl

variable {Z A B X Seed Out U V W : Type*}
variable [Fintype Z] [Fintype A] [Fintype B] [Fintype X]
variable [Fintype Seed] [Fintype Out] [Fintype U] [Fintype V] [Fintype W]

/-- The left source together with its two observations at a fixed right transcript. -/
@[expose] noncomputable def mergingLeftWeight (l : Z → A → ℝ) (x : Z → A → X)
    (u : Z → A → U) (leak : Z → V → A → W) (zv : Z × V) : (U × W) × X → ℝ :=
  mapWeight (fun a => ((u zv.1 a, leak zv.1 zv.2 a), x zv.1 a)) (l zv.1)

/-- Extract from a fixed left joint source while keeping both of its observations. -/
@[expose] noncomputable def mergingOutputWeight (p : (U × W) × X → ℝ) (E : X → Seed → Out)
    (y : Seed) : (U × W) × Out → ℝ :=
  mapWeight (fun tx => (tx.1, E tx.2 y)) p

/-- The seed-by-seed discrepancy of a fixed pair of transcript values. -/
@[expose] noncomputable def mergingDistance (l : Z → A → ℝ) (x : Z → A → X)
    (u : Z → A → U) (leak : Z → V → A → W) (E : X → Seed → Out)
    (p : (Z × V) × Seed) : ℝ :=
  let output := mergingOutputWeight (mergingLeftWeight l x u leak p.1) E p.2
  weightDist output (uniformSecondWeight output)

omit [Fintype Z] [Fintype V] in
theorem mergingLeftWeight_probability (l : Z → A → ℝ) (x : Z → A → X)
    (u : Z → A → U) (leak : Z → V → A → W)
    (hl : ∀ z, IsProbabilityWeight (l z)) (zv : Z × V) :
    IsProbabilityWeight (mergingLeftWeight l x u leak zv) :=
  (hl zv.1).map _

omit [Fintype Seed] in
theorem mergingOutputWeight_probability (p : (U × W) × X → ℝ)
    (E : X → Seed → Out) (hp : IsProbabilityWeight p) (y : Seed) :
    IsProbabilityWeight (mergingOutputWeight p E y) := hp.map _

omit [Fintype Z] [Fintype Seed] [Fintype Out] [Fintype V] in
theorem mergingOutputWeight_left (l : Z → A → ℝ) (x : Z → A → X)
    (u : Z → A → U) (leak : Z → V → A → W) (E : X → Seed → Out)
    (zv : Z × V) (y : Seed) :
    mergingOutputWeight (mergingLeftWeight l x u leak zv) E y =
      mapWeight (fun a => ((u zv.1 a, leak zv.1 zv.2 a), E (x zv.1 a) y)) (l zv.1) := by
  exact mapWeight_comp _ _ _

theorem observedSeedWeight_probability (w : Z → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (y : Z → B → Seed) (hw : IsProbabilityWeight w)
    (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (observedSeedWeight w r v y) :=
  (merging_probability_tagged hw hr).map _

theorem observedSeedWeight_first (w : Z → ℝ) (r : Z → B → ℝ)
    (v : Z → B → V) (y : Z → B → Seed) :
    firstWeight (observedSeedWeight w r v y) =
      fun zv => w zv.1 * mapWeight (v zv.1) (r zv.1) zv.2 := by
  rw [← mapWeight_fst, observedSeedWeight, mapWeight_comp]
  exact mapWeight_tagged v w r

theorem leakageSourceWeight_probability (w : Z → ℝ) (l : Z → A → ℝ)
    (r : Z → B → ℝ) (x : Z → A → X) (u : Z → A → U) (v : Z → B → V)
    (leak : Z → V → A → W) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (leakageSourceWeight w l r x u v leak) :=
  merging_probability_nested
    (merging_probability_tagged hw (fun z => (hr z).map (v z)))
    (mergingLeftWeight_probability l x u leak hl)

omit [Fintype X] [Fintype Seed] [Fintype V] in
theorem twoSidedExtractionWeight_probability (w : Z → ℝ) (l : Z → A → ℝ)
    (r : Z → B → ℝ) (x : Z → A → X) (y : Z → B → Seed)
    (u : Z → A → U) (v : Z → B → V) (leak : Z → V → A → W)
    (E : X → Seed → Out) (hw : IsProbabilityWeight w)
    (hl : ∀ z, IsProbabilityWeight (l z)) (hr : ∀ z, IsProbabilityWeight (r z)) :
    IsProbabilityWeight (twoSidedExtractionWeight w l r x y u v leak E) :=
  merging_probability_nested (merging_probability_tagged hw hr)
    (fun zb => (hl zb.1).map
      (fun a => ((u zb.1 a, leak zb.1 (v zb.1 zb.2) a), E (x zb.1 a) (y zb.1 zb.2))))

omit [Fintype X] [Fintype Seed] [Fintype Out] [Fintype U] [Fintype V] [Fintype W] in
theorem twoSidedExtractionWeight_eq_map (w : Z → ℝ) (l : Z → A → ℝ)
    (r : Z → B → ℝ) (x : Z → A → X) (y : Z → B → Seed)
    (u : Z → A → U) (v : Z → B → V) (leak : Z → V → A → W)
    (E : X → Seed → Out) :
    twoSidedExtractionWeight w l r x y u v leak E =
      mapWeight (fun p : (Z × B) × A =>
        ((p.1, (u p.1.1 p.2, leak p.1.1 (v p.1.1 p.1.2) p.2)),
          E (x p.1.1 p.2) (y p.1.1 p.1.2))) (factoredWeight w l r) := by
  funext ⟨⟨zb, t⟩, o⟩
  have equality := congrFun (mapWeight_tagged
    (fun (zb : Z × B) a =>
      ((u zb.1 a, leak zb.1 (v zb.1 zb.2) a), E (x zb.1 a) (y zb.1 zb.2)))
    (fun zb => w zb.1 * r zb.1 zb.2) (fun zb => l zb.1)) (zb, (t, o))
  simpa only [twoSidedExtractionWeight, factoredWeight, mapWeight,
    Fintype.sum_prod_type, Prod.mk.injEq, and_assoc] using equality.symm

end Algebraic.Cutwidth.Extractor.Internal
