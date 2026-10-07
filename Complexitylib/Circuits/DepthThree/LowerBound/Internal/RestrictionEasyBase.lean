/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionPathData
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionMarkerCNF

/-!
# Unrestricted depth-three lower bound: restriction easy base

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionEasyBase.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {I : Type uDepth2} [instFintypeV : Fintype V] [instFintypeI : Fintype I]

/-- Convert an indexed clause family into a CNF list. -/
def indexedCNF (C : I → Clause V) : CNF V :=
  (Finset.univ : Finset I).toList.map C

omit [Fintype V] in
theorem indexedCNF_eval_eq_true
    {V : Type uDepth1}
    {I : Type uDepth2}

    [instFintypeI : Fintype I]
    (C : I → Clause V) (x : Cube V) :
    (indexedCNF C).eval x = true ↔ ∀ i, (C i).eval x = true := by
  simp [indexedCNF, CNF.eval_eq_true]
omit [Fintype V] [Fintype I] in
theorem clauseViolationCount_zero_iff
    {V : Type uDepth1}
    {I : Type uDepth2}


    (C : I → Clause V) (x : Cube V) (S : Finset I) :
    (S.filter (fun i => (C i).violation x = true)).card = 0 ↔
      ∀ i ∈ S, (C i).eval x = true := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    have hn := h hi
    cases he : (C i).eval x
    · exact (hn ((Clause.violation_eq_true (C i) x).mpr he)).elim
    · rfl
  · intro h i hi hv
    have ht := h i hi
    have hf := (Clause.violation_eq_true (C i) x).mp hv
    rw [ht] at hf
    cases hf
omit instFintypeV in
theorem indexedCNF_eval_indicator (C : I → Clause V) (x : Cube V) :
    indicator ((indexedCNF C).eval x) =
      if totalCount (fun i => (C i).violation x) = 0 then (1 : ℝ) else 0 := by
  have he : (indexedCNF C).eval x = true ↔ totalCount (fun i => (C i).violation x) = 0 := by
    rw [indexedCNF_eval_eq_true]
    simp [totalCount]
  unfold indicator
  congr 1
  exact propext he

/-- Indices of the easy clauses retained in the base factor. -/
def easyBaseIndices (C : I → Clause V) (b : ℕ) (σ : Restriction V) : Finset I :=
  Finset.univ.filter fun i => ((C i).scope ∩ liveSet σ).card ≤ b

/-- The clause contributed by one easy-base index. -/
def easyBaseClause (C : I → Clause V) (σ : Restriction V) (i : I) :
    Option (Clause (Live σ)) :=
  keptRestrictedClause σ (liveSet σ) (fill σ (fun _ => false)) (C i)

omit [Fintype I] in
theorem easyBaseClause_eval
    {V : Type uDepth1}
    {I : Type uDepth2}
    [instFintypeV : Fintype V]

    (C : I → Clause V) (σ : Restriction V) (i : I)
    (x : Cube (Live σ)) :
    residualClauseEval (easyBaseClause C σ i) x = (C i).eval (fill σ x) := by
  apply keptRestrictedClause_eval
  intro v hv
  apply fill_agree_outside_live
  intro hσ
  exact hv (by simp [liveSet, hσ])
/-- The CNF formed by the easy-base clauses. -/
def easyBaseCNF (C : I → Clause V) (b : ℕ) (σ : Restriction V) : CNF (Live σ) :=
  residualCNF ((easyBaseIndices C b σ).toList.map (easyBaseClause C σ))

theorem easyBaseCNF_widthAtMost (C : I → Clause V) (b : ℕ) (σ : Restriction V) :
    (easyBaseCNF C b σ).WidthAtMost b := by
  apply residualCNF_widthAtMost
  intro D hD
  obtain ⟨i, hi, hiD⟩ := List.mem_map.mp hD
  have hi' : i ∈ easyBaseIndices C b σ := by simpa using hi
  have hb : ((C i).scope ∩ liveSet σ).card ≤ b := (Finset.mem_filter.mp hi').2
  exact (keptRestrictedClause_width_le hiD).trans hb

theorem easyBaseCNF_eval_iff_all (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    (easyBaseCNF C b σ).eval x = true ↔
      ∀ i ∈ easyBaseIndices C b σ, (C i).eval (fill σ x) = true := by
  change (residualCNF ((easyBaseIndices C b σ).toList.map (easyBaseClause C σ))).eval x = true ↔ _
  rw [residualCNF_eval_eq_true]
  constructor
  · intro h i hi
    have hm : easyBaseClause C σ i ∈
        (easyBaseIndices C b σ).toList.map (easyBaseClause C σ) :=
      List.mem_map.mpr ⟨i, by simpa using hi, rfl⟩
    have hx := h _ hm
    rwa [easyBaseClause_eval] at hx
  · intro h D hD
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hD
    rw [easyBaseClause_eval]
    exact h i (by simpa using hi)

theorem easyBaseCNF_eval_eq_true (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    (easyBaseCNF C b σ).eval x = true ↔
      easyCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) ∅ = 0 := by
  rw [easyBaseCNF_eval_iff_all]
  simp [easyCount, easyBaseIndices, residual]

theorem easyBaseCNF_eval_indicator (C : I → Clause V) (b : ℕ) (σ : Restriction V)
    (x : Cube (Live σ)) :
    indicator ((easyBaseCNF C b σ).eval x) =
      if easyCount (fun i => (C i).scope) (liveSet σ) b
        (fun i => (C i).violation (fill σ x)) ∅ = 0 then (1 : ℝ) else 0 := by
  unfold indicator
  congr 1
  exact propext (easyBaseCNF_eval_eq_true C b σ x)

/-- View a CNF list as a clause family indexed by its positions. -/
def cnfIndexFamily (H : CNF V) (i : Fin H.length) : Clause V := H.get i

omit [Fintype V] in
theorem cnfIndexFamily_normalized
    {V : Type uDepth1}

    {H : CNF V} (hH : H.Normalized)
    (i : Fin H.length) : (cnfIndexFamily H i).Normalized :=
  hH _ (List.get_mem H i)
omit [Fintype V] in
theorem cnfIndexFamily_width
    {V : Type uDepth1}

    {H : CNF V} {k : ℕ} (hH : H.WidthAtMost k)
    (i : Fin H.length) : (cnfIndexFamily H i).width ≤ k :=
  hH _ (List.get_mem H i)
omit instFintypeV in
@[simp] theorem indexedCNF_cnfIndexFamily_eval (H : CNF V) (x : Cube V) :
    (indexedCNF (cnfIndexFamily H)).eval x = H.eval x := by
  apply Bool.eq_iff_iff.mpr
  rw [indexedCNF_eval_eq_true, CNF.eval_eq_true]
  constructor
  · intro h C hC
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hC
    exact h i
  · intro h i
    exact h _ (List.get_mem H i)

end DepthThreeLowerBound

end

end Complexity
