/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

/-!
# Normalized rows and total variation with retained conditioning

Nonnegative zero-mass rows vanish pointwise, making row factorization exact
even on null events. Tagged mixture distance then identifies conditional
distance with its average against the unchanged first marginal.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem conditionalWeight_factor {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (nonnegative : ∀ ab, 0 ≤ p ab) (a : α) (b : β) :
    firstWeight p a * conditionalWeight p a b = p (a, b) := by
  classical
  by_cases zero : firstWeight p a = 0
  · have vanishes : p (a, b) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => nonnegative (a, b))).mp zero b
        (Finset.mem_univ b)
    simp only [zero, zero_mul, vanishes]
  · rw [conditionalWeight, ite_eq_right zero, mul_div_cancel₀ _ zero]

theorem probabilityWeight_conditional {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) (a : α) :
    IsProbabilityWeight (conditionalWeight p a) := by
  classical
  by_cases zero : firstWeight p a = 0
  · have row : conditionalWeight p a = uniformWeight β := by
      funext b
      simp only [conditionalWeight, ite_eq_left zero]
    rw [row]
    exact isProbabilityWeight_uniform β
  · have positive : 0 < firstWeight p a := lt_of_le_of_ne (probability.first.1 a) (Ne.symm zero)
    refine ⟨fun b => ?_, ?_⟩
    · simp only [conditionalWeight, ite_eq_right zero]
      exact div_nonneg (probability.1 (a, b)) positive.le
    · simp only [conditionalWeight, ite_eq_right zero, ← Finset.sum_div]
      exact div_self zero

theorem probabilityWeight_uniformExtension {α : Type*} [Fintype α]
    {w : α → ℝ} (probability : IsProbabilityWeight w) (β : Type*) [Fintype β] [Nonempty β] :
    IsProbabilityWeight (uniformExtensionWeight β w) := by
  have uniform := isProbabilityWeight_uniform β
  refine ⟨fun ab => mul_nonneg (probability.1 ab.1) (uniform.1 ab.2), ?_⟩
  simpa only [uniformExtensionWeight, Fintype.sum_prod_type, ← Finset.mul_sum,
    uniform.2, mul_one] using probability.2

theorem firstWeight_uniformExtension {α β : Type*} [Fintype β] [Nonempty β]
    (w : α → ℝ) : firstWeight (uniformExtensionWeight β w) = w := by
  have uniform := isProbabilityWeight_uniform β
  funext a
  simp only [firstWeight, uniformExtensionWeight, ← Finset.mul_sum, uniform.2, mul_one]

theorem probabilityWeight_uniformSecond {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    IsProbabilityWeight (uniformSecondWeight p) :=
  probabilityWeight_uniformExtension probability.first β

theorem weightDist_uniformSecond_eq {α β : Type*}
    [Fintype α] [Fintype β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    weightDist p (uniformSecondWeight p) =
      ∑ a, firstWeight p a * weightDist (conditionalWeight p a) (uniformWeight β) := by
  have factor : p = fun ab => firstWeight p ab.1 * conditionalWeight p ab.1 ab.2 := by
    funext ab
    exact (conditionalWeight_factor p probability.1 ab.1 ab.2).symm
  calc
    weightDist p (uniformSecondWeight p) =
        weightDist (fun ab : α × β => firstWeight p ab.1 * conditionalWeight p ab.1 ab.2)
          (fun ab => firstWeight p ab.1 * uniformWeight β ab.2) := by
      exact congrArg (fun actual => weightDist actual (uniformSecondWeight p)) factor
    _ = _ := weightDist_tagged_mixture (firstWeight p) (conditionalWeight p)
      (fun _ => uniformWeight β) probability.first.1

theorem firstWeight_map_fiber {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → β → γ) :
    firstWeight (mapWeight (fun ab => (ab.1, f ab.1 ab.2)) p) = firstWeight p := by
  rw [← mapWeight_fst, mapWeight_comp, mapWeight_fst]

theorem weightDist_uniformSecond_tagged {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (w : ι → ℝ) (p : ι → α × β → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun iab : (ι × α) × β => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))
      (uniformSecondWeight (fun iab => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))) =
        ∑ i, w i * weightDist (p i) (uniformSecondWeight (p i)) := by
  simp only [weightDist, uniformSecondWeight, uniformExtensionWeight, firstWeight,
    Fintype.sum_prod_type, ← Finset.mul_sum, mul_assoc]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (nonnegative _)]
  simp only [Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

theorem firstWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    firstWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) =
      mapWeight f (firstWeight p) := by
  rw [← mapWeight_fst, mapWeight_comp, ← mapWeight_fst, mapWeight_comp]

theorem mapWeight_uniformExtension {α β γ : Type*}
    [Fintype α] [Fintype β] (w : α → ℝ) (f : α → γ) :
    mapWeight (fun ab : α × β => (f ab.1, ab.2)) (uniformExtensionWeight β w) =
      uniformExtensionWeight β (mapWeight f w) := by
  classical
  funext cb
  rcases cb with ⟨c, b⟩
  simp [mapWeight, uniformExtensionWeight, Fintype.sum_prod_type, Prod.mk.injEq,
    ite_and, Finset.sum_ite_irrel, Finset.sum_mul]

theorem uniformSecondWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    mapWeight (fun ab => (f ab.1, ab.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) := by
  simp only [uniformSecondWeight, mapWeight_uniformExtension, firstWeight_map_first]

theorem weightDist_uniformSecond_map_first_le {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    weightDist (mapWeight (fun ab => (f ab.1, ab.2)) p)
      (uniformSecondWeight (mapWeight (fun ab => (f ab.1, ab.2)) p)) ≤
        weightDist p (uniformSecondWeight p) := by
  rw [← uniformSecondWeight_map_first p f]
  exact weightDist_map_le p (uniformSecondWeight p) (fun ab => (f ab.1, ab.2))

end Algebraic.Cutwidth.Extractor.Internal
