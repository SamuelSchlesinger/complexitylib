/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCylinders
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MarkerMixture
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: restriction marker cnf

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionMarkerCNF.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [Fintype I] [instDecidableEqI : DecidableEq I]

theorem residualCNF_eval_eq_true (L : List (Option (Clause V))) (x : Cube V) :
    (residualCNF L).eval x = true ↔ ∀ C ∈ L, residualClauseEval C x = true := by
  induction L with
  | nil => simp
  | cons C L ih =>
    cases C <;> simp [ih, CNF.eval_cons]

theorem residualCNF_widthAtMost (L : List (Option (Clause V))) {b : ℕ}
    (h : ∀ C, some C ∈ L → C.width ≤ b) : (residualCNF L).WidthAtMost b := by
  intro C hC
  obtain ⟨D, hD, hDC⟩ := List.mem_filterMap.mp hC
  change D = some C at hDC
  subst D
  exact h C hD

/-- The CNF corresponding to a single marker test. -/
def markerCNF (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) : CNF V :=
  residualCNF ((markerSelected c π).toList.map C)

@[simp] theorem markerCNF_eval (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (x : Cube V) :
    (markerCNF C c π).eval x =
      markerSample (fun i x => residualClauseEval (C i) x) c π x := by
  apply Bool.eq_iff_iff.mpr
  rw [markerSample_eq_true]
  simp only [markerCNF, residualCNF_eval_eq_true, List.forall_mem_map,
    Finset.mem_toList]

omit [DecidableEq I] in
theorem markerCNF_widthAtMost
    {V : Type uDepth1}
    {I : Type uDepth2}
    [Fintype I]

    (C : I → Option (Clause V)) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) {b : ℕ}
    (h : ∀ i D, C i = some D → D.width ≤ b) :
    (markerCNF C c π).WidthAtMost b := by
  classical
  apply residualCNF_widthAtMost
  intro D hD
  obtain ⟨i, hi, hiD⟩ := List.mem_map.mp hD
  exact h i D hiD
theorem markerCNF_avg (C : I → Option (Clause V)) {c : ℕ} (hc : 0 < c)
    (x : Cube V) :
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) => indicator ((markerCNF C c π).eval x)) =
      (c : ℝ) / ((c : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C i) x) x).card : ℝ)) := by
  simp_rw [markerCNF_eval]
  exact marker_mixture_ratio _ x hc

section Product

variable {H : Type uDepth3} [Fintype H] [instDecidableEqH : DecidableEq H]
    {J : H → Type uDepth4} [∀ h, Fintype (J h)] [insthDecidableEqJh : ∀ h, DecidableEq (J h)]

/-- The CNF corresponding to a product of marker tests. -/
def markerProductCNF (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) : CNF V :=
  (Finset.univ : Finset H).toList.flatMap fun h => markerCNF (C h) (c h) (π h)

omit [DecidableEq H] [(h : H) → DecidableEq (J h)] in
theorem markerProductCNF_eval_eq_true
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]

    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]

    (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) (x : Cube V) :
    (markerProductCNF C c π).eval x = true ↔
      ∀ h, (markerCNF (C h) (c h) (π h)).eval x = true := by
  classical
  simp only [markerProductCNF, CNF.eval_eq_true, List.forall_mem_flatMap,
    Finset.mem_toList, Finset.mem_univ, forall_const]
omit instDecidableEqH insthDecidableEqJh in
theorem markerProductCNF_indicator (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) (x : Cube V) :
    indicator ((markerProductCNF C c π).eval x) =
      ∏ h, indicator ((markerCNF (C h) (c h) (π h)).eval x) := by
  unfold indicator
  rw [Fintype.prod_boole]
  congr 1
  exact propext (markerProductCNF_eval_eq_true C c π x)

omit [DecidableEq H] [(h : H) → DecidableEq (J h)] in
theorem markerProductCNF_widthAtMost
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]

    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]
    (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) {b : ℕ}
    (hC : ∀ h i D, C h i = some D → D.width ≤ b) :
    (markerProductCNF C c π).WidthAtMost b := by
  classical
  intro D hD
  obtain ⟨h, hh, hD⟩ := List.mem_flatMap.mp hD
  exact markerCNF_widthAtMost (C h) (c h) (π h) (hC h) D hD
theorem markerProductCNF_avg (C : ∀ h, J h → Option (Clause V))
    (c : H → ℕ) (hc : ∀ h, 0 < c h) (x : Cube V) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      indicator ((markerProductCNF C c π).eval x)) =
      ∏ h, (c h : ℝ) / ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ)) := by
  simp_rw [markerProductCNF_indicator, markerCNF_eval]
  exact marker_product_mixture_ratio (fun h i x => residualClauseEval (C h i) x) c hc x

variable [instDecidableEqV : DecidableEq V]

/-- Combine marker tests with the path's fixed-coordinate cylinder. -/
def markerCylinderCNF (K : CNF V) (U : Finset V) (pattern : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) : CNF V :=
  (K ++ cylinderCNF U pattern) ++ markerProductCNF C c π

omit instDecidableEqH instDecidableEqV insthDecidableEqJh in
theorem markerCylinderCNF_widthAtMost (K : CNF V) (U : Finset V) (pattern : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ)
    (π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h))) {b : ℕ} (hb : 1 ≤ b)
    (hK : K.WidthAtMost b) (hC : ∀ h i D, C h i = some D → D.width ≤ b) :
    (markerCylinderCNF K U pattern C c π).WidthAtMost b := by
  intro D hD
  rcases List.mem_append.mp hD with hD | hD
  · rcases List.mem_append.mp hD with hD | hD
    · exact hK D hD
    · exact cylinderCNF_widthAtMost U pattern hb D hD
  · exact markerProductCNF_widthAtMost C c π hC D hD

omit [DecidableEq V] in
theorem markerCylinderCNF_avg
    {V : Type uDepth1}
    {H : Type uDepth3}
    [Fintype H]
    [instDecidableEqH : DecidableEq H]
    {J : H → Type uDepth4}
    [(h : H) → Fintype (J h)]
    [insthDecidableEqJh : (h : H) → DecidableEq (J h)]

    (K : CNF V) (U : Finset V) (pattern x : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ) (hc : ∀ h, 0 < c h) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      indicator ((markerCylinderCNF K U pattern C c π).eval x)) =
      indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x) *
        ∏ h, (c h : ℝ) / ((c h : ℝ) +
          ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ)) := by
  classical
  simp only [markerCylinderCNF, CNF.eval_append, indicator_and]
  rw [finiteAvg_const_mul, markerProductCNF_avg C c hc x]
omit instDecidableEqV in
theorem markerCylinderCNF_scaled_avg (K : CNF V) (U : Finset V) (pattern x : Cube V)
    (C : ∀ h, J h → Option (Clause V)) (c : H → ℕ) (hc : ∀ h, 0 < c h) :
    (∏ h, (c h : ℝ)⁻¹) *
      finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
        indicator ((markerCylinderCNF K U pattern C c π).eval x)) =
      indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x) *
        ∏ h, ((c h : ℝ) +
          ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))⁻¹ := by
  rw [markerCylinderCNF_avg K U pattern x C c hc]
  have hprod : (∏ h, (c h : ℝ)⁻¹) *
      (∏ h, (c h : ℝ) / ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))) =
      ∏ h, ((c h : ℝ) +
        ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    have hcn : (c h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hc h))
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hcn, one_mul]
  calc
    _ = (indicator (K.eval x) * indicator ((cylinderCNF U pattern).eval x)) *
        ((∏ h, (c h : ℝ)⁻¹) *
          ∏ h, (c h : ℝ) / ((c h : ℝ) +
            ((markerBad (fun i x => residualClauseEval (C h i) x) x).card : ℝ))) := by ring
    _ = _ := by rw [hprod]

end Product

end DepthThreeLowerBound

end

end Complexity
