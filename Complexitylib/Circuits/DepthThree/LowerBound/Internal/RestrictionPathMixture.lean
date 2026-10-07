/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPathData
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCountSplit
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionMarkerCNF

/-!
# Unrestricted depth-three lower bound: restriction path mixture

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionPathMixture.lean

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

/-- Intermediate clause indices associated with a path prefix. -/
def pathIntermediateIndices (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) : Finset I :=
  intermediateIndices (fun i => (C i).scope) (liveSet σ) b (pathPrefixSet C σ P h)

/-- An intermediate index together with its path position. -/
abbrev PathIntermediateIndex (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) := ↥(pathIntermediateIndices C b σ P h)

/-- The residual clause associated with a path's intermediate index. -/
def pathReducedClause (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (h : Fin P.length) (i : PathIntermediateIndex C b σ P h) :
    Option (Clause (Live σ)) :=
  keptRestrictedClause σ (liveSet σ \ pathFinalSet C σ P)
    (fill σ (pathCenter C σ P)) (C i.val)

theorem pathReducedClause_widthAtMost (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (h : Fin P.length)
    (i : PathIntermediateIndex C b σ P h) (D : Clause (Live σ))
    (hD : pathReducedClause C b σ P h i = some D) : D.width ≤ b := by
  have hd := keptRestrictedClause_width_le hD
  have hs : (C i.val).scope ∩ (liveSet σ \ pathFinalSet C σ P) ⊆
      residual (fun i => (C i).scope) (liveSet σ) (pathPrefixSet C σ P h) i.val := by
    intro v hv
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, ?_⟩
    obtain ⟨ht, hn⟩ := Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2
    exact Finset.mem_sdiff.mpr ⟨ht,
      fun hp => hn (pathPrefixSet_subset_final C σ P h hp)⟩
  have hi := (mem_intermediateIndices (fun i => (C i).scope) (liveSet σ) b
    (pathPrefixSet C σ P h) i.val).mp i.property
  exact hd.trans ((Finset.card_le_card hs).trans hi.2)

omit [Fintype I] in
theorem path_fill_agree_outside_remainder (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) :
    ∀ v ∉ liveSet σ \ pathFinalSet C σ P,
      fill σ x v = fill σ (pathCenter C σ P) v := by
  have hZ := (simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)).mp hx
  intro v hv
  by_cases ht : v ∈ liveSet σ
  · have hz : v ∈ pathFinalSet C σ P := by
      by_contra hz
      exact hv (Finset.mem_sdiff.mpr ⟨ht, hz⟩)
    exact hZ v hz
  · apply fill_agree_outside_live
    intro hσ
    exact ht (by simp [liveSet, hσ])

theorem pathReducedClause_eval_on_support (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized)
    (hc : pathCompatible C σ P) (x : Cube (Live σ))
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) (i : PathIntermediateIndex C b σ P h) :
    residualClauseEval (pathReducedClause C b σ P h i) x = (C i.val).eval (fill σ x) :=
  keptRestrictedClause_eval σ _ _ _ x
    (path_fill_agree_outside_remainder C σ P hn hc x hx)

theorem pathCoveredCount_eq_on_support (C : I → Clause V) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    coveredCount (fun i => (C i).scope) (liveSet σ)
      (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) =
      pathCoveredCount C σ P h := by
  have hZ := (simultaneous_restricted_violation_iff C σ (liveSet σ)
    (by intro v; simp [liveSet]) P x (pathCenter C σ P) hn
    (pathCenter_support C σ P hc)).mp hx
  apply coveredCount_eq_on_larger_cylinder C (liveSet σ) (pathPrefixSet C σ P h)
    (pathFinalSet C σ P) (fill σ x) (fill σ (pathCenter C σ P))
    (pathPrefixSet_subset_final C σ P h) hZ
  intro v hv
  apply fill_agree_outside_live
  intro hσ
  exact hv (by simp [liveSet, hσ])

theorem pathMarkerBad_card (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (x : Cube (Live σ)) (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true)
    (h : Fin P.length) :
    (markerBad (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x).card =
      intermediateCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) := by
  have he : markerBad
      (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x =
      (Finset.univ : Finset (PathIntermediateIndex C b σ P h)).filter
        (fun i => (C i.val).violation (fill σ x) = true) := by
    ext i
    simp only [markerBad, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pathReducedClause_eval_on_support C b σ P hn hc x hx h i,
      Clause.violation_eq_true]
  rw [he]
  exact subtype_filter_card (pathIntermediateIndices C b σ P h)
    (fun i => (C i).violation (fill σ x) = true)

theorem path_easyCount_eq_marker_count (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (hn : ∀ i ∈ P, (C i).Normalized)
    (hc : pathCompatible C σ P) (x : Cube (Live σ))
    (hx : ∀ i ∈ P, (C i).violation (fill σ x) = true) (h : Fin P.length) :
    easyCount (fun i => (C i).scope) (liveSet σ) b
      (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) =
      pathCoveredCount C σ P h +
        (markerBad (fun i z => residualClauseEval (pathReducedClause C b σ P h i) z) x).card := by
  rw [easyCount_eq_covered_add_intermediate,
    pathCoveredCount_eq_on_support C σ P hn hc x hx h,
    pathMarkerBad_card C b σ P hn hc x hx h]

/-- A collection of marker choices along a path. -/
abbrev PathMarkerSample (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (P : List I) :=
  ∀ h : Fin P.length, Equiv.Perm
    (PathIntermediateIndex C b σ P h ⊕ Fin (pathCoveredCount C σ P h))

/-- The CNF obtained from a path and its marker samples. -/
def pathMixtureCNF (C : I → Clause V) (b : ℕ) (σ : Restriction V) (P : List I)
    (K : CNF (Live σ)) (π : PathMarkerSample C b σ P) : CNF (Live σ) :=
  markerCylinderCNF K (pathLiveSet C σ P) (pathCenter C σ P)
    (pathReducedClause C b σ P) (pathCoveredCount C σ P) π

theorem pathMixtureCNF_widthAtMost (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) (P : List I) (K : CNF (Live σ)) (hb : 1 ≤ b)
    (hK : K.WidthAtMost b) (π : PathMarkerSample C b σ P) :
    (pathMixtureCNF C b σ P K π).WidthAtMost b :=
  markerCylinderCNF_widthAtMost K _ _ _ _ π hb hK
    (pathReducedClause_widthAtMost C b σ P)

theorem pathMixture_scaled_average (C : I → Clause V) (b : ℕ)
    (σ : Restriction V) {n : ℕ} {P : List I}
    (hP : P ∈ paths (fun i => (C i).scope) (liveSet σ) b n)
    (hn : ∀ i ∈ P, (C i).Normalized) (hc : pathCompatible C σ P)
    (K : CNF (Live σ)) (x : Cube (Live σ)) :
    pathWeight C σ P *
      finiteAvg (fun π : PathMarkerSample C b σ P =>
        indicator ((pathMixtureCNF C b σ P K π).eval x)) =
      indicator (K.eval x) *
        (if ∀ i ∈ P, (C i).violation (fill σ x) = true then
          ∏ h : Fin P.length,
            (easyCount (fun i => (C i).scope) (liveSet σ) b
              (fun i => (C i).violation (fill σ x)) (pathPrefixSet C σ P h) : ℝ)⁻¹
          else 0) := by
  simp only [pathWeight, pathMixtureCNF]
  rw [markerCylinderCNF_scaled_avg K (pathLiveSet C σ P) (pathCenter C σ P) x
      (pathReducedClause C b σ P) (pathCoveredCount C σ P)
      (pathCoveredCount_pos C b σ hP hc)]
  by_cases hx : ∀ i ∈ P, (C i).violation (fill σ x) = true
  · have hZ := (path_support_iff_live_cylinder C σ P hn hc x).mp hx
    have hev : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x = true :=
      (cylinderCNF_eval_eq_true _ _ _).mpr hZ
    simp only [ite_eq_left hx, hev, indicator_true, mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro h hh
    rw [path_easyCount_eq_marker_count C b σ P hn hc x hx h, Nat.cast_add]
  · have hZ : ¬ ∀ v ∈ pathLiveSet C σ P, x v = pathCenter C σ P v :=
      fun hz => hx ((path_support_iff_live_cylinder C σ P hn hc x).mpr hz)
    have hev : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x = false := by
      cases he : (cylinderCNF (pathLiveSet C σ P) (pathCenter C σ P)).eval x
      · rfl
      · exact (hZ ((cylinderCNF_eval_eq_true _ _ _).mp he)).elim
    simp only [ite_eq_right hx, hev, indicator_false, mul_zero, zero_mul]

end DepthThreeLowerBound

end

end Complexity
