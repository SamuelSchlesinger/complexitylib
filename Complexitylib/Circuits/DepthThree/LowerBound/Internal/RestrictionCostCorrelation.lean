/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPathProducts
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPathMixture
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionEasyBase
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCorrelation

/-!
# Unrestricted depth-three lower bound: restriction cost correlation

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionCostCorrelation.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype V] [Fintype I]

theorem pathMixture_eq_pathTerm (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (K : CNF (Live σ)) (x : Cube (Live σ)) :
    pathWeight C σ P *
      finiteAvg (fun π : PathMarkerSample C b σ P =>
        indicator ((pathMixtureCNF C b σ P K π).eval x)) =
      indicator (K.eval x) * pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P := by
  rw [pathTerm_eq_support_prod_inv]
  exact pathMixture_scaled_average C b σ hP hn hc K x

theorem pathTerm_zero_of_incompatible (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hc : ¬ pathCompatible C σ P)
    (x : Cube (Live σ)) :
    pathTerm (fun i => (C i).scope) (liveSet σ) b
      (fun i => (C i).violation (fill σ x)) P = 0 := by
  have hs : ¬ ∀ i ∈ P, (C i).violation (fill σ x) = true :=
    fun hx => hc ⟨x, hx⟩
  rw [pathTerm_eq_support_prod_inv, ite_eq_right hs]

theorem abs_corr_pathTerm_le (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hb : 1 ≤ b)
    (K : CNF (Live σ)) (hK : K.WidthAtMost b) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * (indicator (K.eval x) *
      pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P))| ≤
      (if pathCompatible C σ P then pathWeight C σ P else 0) * corr b G := by
  by_cases hc : pathCompatible C σ P
  · rw [ite_eq_left hc]
    have hlin :
        finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P)) =
        pathWeight C σ P * finiteAvg (fun x => G x *
          finiteAvg (fun π : PathMarkerSample C b σ P =>
            indicator ((pathMixtureCNF C b σ P K π).eval x))) := by
      calc
        _ = finiteAvg (fun x => pathWeight C σ P * (G x *
            finiteAvg (fun π : PathMarkerSample C b σ P =>
              indicator ((pathMixtureCNF C b σ P K π).eval x)))) := by
          apply finiteAvg_congr
          intro x
          rw [← pathMixture_eq_pathTerm C b σ hP hn hc K x]
          ring
        _ = _ := finiteAvg_const_mul _ _
    rw [hlin, abs_mul, abs_of_nonneg (pathWeight_nonneg C σ P)]
    apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg C σ P)
    have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
        (f : Cube (Live σ) → ℝ) (c : ℝ)
        (h : |@finiteAvg _ inst₁ f| ≤ c) : |@finiteAvg _ inst₂ f| ≤ c := by
      have hi : inst₁ = inst₂ := Subsingleton.elim _ _
      cases hi
      exact h
    exact htransport _ _ _ _
      (abs_corr_uniform_mixture_le (pathMixtureCNF C b σ P K) b G
        (pathMixtureCNF_widthAtMost C b σ P K hb hK))
  · have hz : ∀ x : Cube (Live σ), pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P = 0 :=
      pathTerm_zero_of_incompatible C b σ P hc
    simp [hc, hz]

/-- The contribution of paths of a specified length to the restriction expansion. -/
def pathLayer (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (K : CNF (Live σ)) (n : ℕ) (x : Cube (Live σ)) : ℝ :=
  indicator (K.eval x) *
    ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
      pathTerm (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) P

theorem abs_corr_pathLayer_le (C : I → Clause V) (hn : ∀ i, (C i).Normalized)
    (b : ℕ) (hb : 1 ≤ b) (σ : Restriction V) (K : CNF (Live σ))
    (hK : K.WidthAtMost b) (n : ℕ) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * pathLayer C b σ K n x)| ≤
      pathCost C b σ n * corr b G := by
  have hlin : finiteAvg (fun x => G x * pathLayer C b σ K n x) =
      ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P)) := by
    calc
      _ = finiteAvg (fun x =>
          ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
            G x * (indicator (K.eval x) *
              pathTerm (fun i => (C i).scope) (liveSet σ) b
                (fun i => (C i).violation (fill σ x)) P)) := by
        apply finiteAvg_congr
        intro x
        simp only [pathLayer, Finset.mul_sum]
      _ = _ := finiteAvg_sum _ _
  rw [hlin]
  calc
    _ ≤ ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        |finiteAvg (fun x => G x * (indicator (K.eval x) *
          pathTerm (fun i => (C i).scope) (liveSet σ) b
            (fun i => (C i).violation (fill σ x)) P))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ P ∈ paths (fun i => (C i).scope) (liveSet σ) b n,
        (if pathCompatible C σ P then pathWeight C σ P else 0) * corr b G := by
      apply Finset.sum_le_sum
      intro P hP
      exact abs_corr_pathTerm_le C b σ hP (fun i _ => hn i) hb K hK G
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem indexedCNF_restriction_expansion (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (x : Cube (Live σ)) :
    indicator ((indexedCNF C).eval (fill σ x)) =
      indicator ((easyBaseCNF C b σ).eval x) +
        ∑ j ∈ Finset.range ((liveSet σ).card / (b + 1)),
          (-1 : ℝ) ^ (j + 1) * pathLayer C b σ (easyBaseCNF C b σ) (j + 1) x := by
  have h := finite_violation_expansion (fun i => (C i).scope) (liveSet σ) b
    (fun i => (C i).violation (fill σ x))
  rw [← indexedCNF_eval_indicator C (fill σ x),
    ← easyBaseCNF_eval_indicator C b σ x] at h
  rw [h, mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [pathLayer]
  ring

theorem initial_and_live_path_cost_le (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) :
    1 + (∑ j ∈ Finset.range ((liveSet σ).card / (b + 1)), pathCost C b σ (j + 1)) ≤
      restrictionCost C b σ := by
  have hc : (liveSet σ).card / (b + 1) + 1 ≤ Fintype.card V / (b + 1) + 1 :=
    Nat.add_le_add_right (Nat.div_le_div_right (Finset.card_le_univ (liveSet σ))) 1
  calc
    _ = ∑ j ∈ Finset.range ((liveSet σ).card / (b + 1) + 1), pathCost C b σ j := by
      rw [Finset.sum_range_succ']
      simp only [pathCost_zero]
      ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hc)
      (fun j _ _ => pathCost_nonneg C b σ j)

theorem restricted_correlation_le_cost (C : I → Clause V)
    (b : ℕ) (hb : 1 ≤ b) (hn : ∀ i, (C i).Normalized)
    (σ : Restriction V) (G : Cube (Live σ) → ℝ) :
    |finiteAvg (fun x => G x * indicator ((indexedCNF C).eval (fill σ x)))| ≤
      restrictionCost C b σ * corr b G := by
  let K := easyBaseCNF C b σ
  let L := (liveSet σ).card / (b + 1)
  have hlin : finiteAvg (fun x => G x * indicator ((indexedCNF C).eval (fill σ x))) =
      finiteAvg (fun x => G x * indicator (K.eval x)) +
        ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x) := by
    calc
      _ = finiteAvg (fun x => G x * indicator (K.eval x) +
          ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
            (G x * pathLayer C b σ K (j + 1) x)) := by
        apply finiteAvg_congr
        intro x
        rw [indexedCNF_restriction_expansion, mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [finiteAvg_add, finiteAvg_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact finiteAvg_const_mul _ _
  rw [hlin]
  calc
    _ ≤ |finiteAvg (fun x => G x * indicator (K.eval x))| +
        |∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x)| := abs_add_le _ _
    _ ≤ corr b G + ∑ j ∈ Finset.range L,
        |(-1 : ℝ) ^ (j + 1) *
          finiteAvg (fun x => G x * pathLayer C b σ K (j + 1) x)| := by
      have htransport (inst₁ inst₂ : Fintype (Cube (Live σ)))
          (f : Cube (Live σ) → ℝ) (c : ℝ)
          (h : |@finiteAvg _ inst₁ f| ≤ c) : |@finiteAvg _ inst₂ f| ≤ c := by
        have hi : inst₁ = inst₂ := Subsingleton.elim _ _
        cases hi
        exact h
      apply add_le_add
      · exact htransport _ _ _ _ (abs_corr_le b G K (easyBaseCNF_widthAtMost C b σ))
      · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ corr b G + ∑ j ∈ Finset.range L, pathCost C b σ (j + 1) * corr b G := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j hj
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        abs_corr_pathLayer_le C hn b hb σ K (easyBaseCNF_widthAtMost C b σ) (j + 1) G
    _ = (1 + ∑ j ∈ Finset.range L, pathCost C b σ (j + 1)) * corr b G := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ restrictionCost C b σ * corr b G :=
      mul_le_mul_of_nonneg_right (initial_and_live_path_cost_le C b σ) (corr_nonneg b G)

end DepthThreeLowerBound

end

end Complexity
