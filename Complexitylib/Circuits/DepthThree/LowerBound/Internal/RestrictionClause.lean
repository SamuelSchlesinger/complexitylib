/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionNormalization
public import Mathlib.Data.List.Basic

/-!
# Unrestricted depth-three lower bound: restriction clause

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionClause.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9

noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V]

/-- The live literals of a clause under a restriction. -/
def liveClause (σ : Restriction V) (C : Clause V) : Clause (Live σ) := by
  classical
  exact Finset.univ.filter fun l => ((l.1 : V), l.2) ∈ C

@[simp] theorem mem_liveClause (σ : Restriction V) (C : Clause V)
    (l : Literal (Live σ)) : l ∈ liveClause σ C ↔ ((l.1 : V), l.2) ∈ C := by
  classical
  simp [liveClause]

theorem liveClause_scope_image_subset (σ : Restriction V) (C : Clause V) :
    (liveClause σ C).scope.image Subtype.val ⊆ C.scope := by
  classical
  let : DecidableEq (Live σ) := Classical.decEq _
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨l, hl, hlw⟩ := Finset.mem_image.mp hw
  have hc : ((l.1 : V), l.2) ∈ C := (mem_liveClause σ C l).mp hl
  have hv : (l.1 : V) ∈ C.scope := Finset.mem_image_of_mem Prod.fst hc
  simpa only [hlw] using hv

theorem liveClause_width_le (σ : Restriction V) (C : Clause V) :
    (liveClause σ C).width ≤ C.width := by
  classical
  calc
    (liveClause σ C).width =
        ((liveClause σ C).scope.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ C.scope.card := Finset.card_le_card (liveClause_scope_image_subset σ C)
    _ = C.width := rfl

theorem liveClause_normalized (σ : Restriction V) {C : Clause V}
    (hC : C.Normalized) : (liveClause σ C).Normalized := by
  intro v hf ht
  exact hC v.val ((mem_liveClause σ C (v, false)).mp hf)
    ((mem_liveClause σ C (v, true)).mp ht)

/-- Simplify a clause after fixing the restricted coordinates. -/
def restrictClause (σ : Restriction V) (C : Clause V) : Option (Clause (Live σ)) := by
  classical
  exact if ∃ l ∈ C, σ l.1 = some l.2 then none else some (liveClause σ C)

/-- Evaluate the remaining part of a clause on its live variables. -/
def residualClauseEval {W : Type uDepth2} (C : Option (Clause W)) (x : Cube W) : Bool :=
  match C with
  | none => true
  | some C => C.eval x

@[simp] theorem residualClauseEval_none {W : Type uDepth3} (x : Cube W) :
    residualClauseEval (none : Option (Clause W)) x = true := rfl

@[simp] theorem residualClauseEval_some {W : Type uDepth4} (C : Clause W) (x : Cube W) :
    residualClauseEval (some C) x = C.eval x := rfl

theorem restrictClause_eval (σ : Restriction V) (C : Clause V)
    (z : Cube (Live σ)) :
    residualClauseEval (restrictClause σ C) z = C.eval (fill σ z) := by
  classical
  by_cases hs : ∃ l ∈ C, σ l.1 = some l.2
  · simp only [restrictClause, ite_eq_left hs, residualClauseEval_none]
    symm
    obtain ⟨l, hl, hlσ⟩ := hs
    exact (Clause.eval_eq_true C (fill σ z)).mpr ⟨l, hl, fill_fixed σ z l.1 l.2 hlσ⟩
  · simp only [restrictClause, ite_eq_right hs, residualClauseEval_some]
    apply Bool.eq_iff_iff.mpr
    rw [Clause.eval_eq_true, Clause.eval_eq_true]
    constructor
    · rintro ⟨⟨v, b⟩, hl, hz⟩
      refine ⟨(v.val, b), (mem_liveClause σ C (v, b)).mp hl, ?_⟩
      exact (fill_live σ z v).trans hz
    · rintro ⟨⟨v, b⟩, hl, hz⟩
      have hv : σ v = none := by
        cases hσ : σ v with
        | none => rfl
        | some c =>
          have hcb : c = b := (fill_fixed σ z v c hσ).symm.trans hz
          have hf : ∃ l ∈ C, σ l.1 = some l.2 :=
            ⟨(v, b), hl, hσ.trans (congrArg some hcb)⟩
          exact (hs hf).elim
      refine ⟨(⟨v, hv⟩, b), (mem_liveClause σ C (⟨v, hv⟩, b)).mpr hl, ?_⟩
      exact (fill_live σ z ⟨v, hv⟩).symm.trans hz

theorem restrictClause_some_eq {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (h : restrictClause σ C = some D) :
    D = liveClause σ C := by
  classical
  unfold restrictClause at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

theorem restrictClause_width_le {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (h : restrictClause σ C = some D) : D.width ≤ C.width := by
  rw [restrictClause_some_eq h]
  exact liveClause_width_le σ C

theorem restrictClause_normalized {σ : Restriction V} {C : Clause V}
    {D : Clause (Live σ)} (hC : C.Normalized)
    (h : restrictClause σ C = some D) : D.Normalized := by
  rw [restrictClause_some_eq h]
  exact liveClause_normalized σ hC

@[simp] theorem restrictClause_empty (σ : Restriction V) :
    restrictClause σ (∅ : Clause V) = some ∅ := by
  classical
  simp [restrictClause, liveClause]

/-- The conjunction of residual clauses after a restriction. -/
def residualCNF {W : Type uDepth5} (H : List (Option (Clause W))) : CNF W :=
  H.filterMap id

@[simp] theorem residualCNF_nil {W : Type uDepth6} :
    residualCNF ([] : List (Option (Clause W))) = [] := rfl

@[simp] theorem residualCNF_cons_none {W : Type uDepth7} (H : List (Option (Clause W))) :
    residualCNF (none :: H) = residualCNF H := rfl

@[simp] theorem residualCNF_cons_some {W : Type uDepth8} (C : Clause W)
    (H : List (Option (Clause W))) :
    residualCNF (some C :: H) = C :: residualCNF H := rfl

theorem residualCNF_eval_cons {W : Type uDepth9} (C : Option (Clause W))
    (H : List (Option (Clause W))) (x : Cube W) :
    (residualCNF (C :: H)).eval x =
      (residualClauseEval C x && (residualCNF H).eval x) := by
  cases C <;> simp

/-- Apply a restriction to every clause in a CNF. -/
def restrictCNF (σ : Restriction V) (H : CNF V) : CNF (Live σ) :=
  H.filterMap (restrictClause σ)

@[simp] theorem restrictCNF_eval (σ : Restriction V) (H : CNF V)
    (z : Cube (Live σ)) : (restrictCNF σ H).eval z = H.eval (fill σ z) := by
  induction H with
  | nil => simp [restrictCNF]
  | cons C H ih =>
    have he := restrictClause_eval σ C z
    unfold restrictCNF at ih
    cases hr : restrictClause σ C with
    | none =>
      simp only [hr, residualClauseEval_none] at he
      simp [restrictCNF, hr, ← he, ih]
    | some D =>
      simp only [hr, residualClauseEval_some] at he
      simp [restrictCNF, hr, ← he, ih]

theorem restrictCNF_widthAtMost (σ : Restriction V) {H : CNF V} {b : ℕ}
    (hH : H.WidthAtMost b) : (restrictCNF σ H).WidthAtMost b := by
  intro D hD
  obtain ⟨C, hC, hCD⟩ := List.mem_filterMap.mp hD
  exact (restrictClause_width_le hCD).trans (hH C hC)

theorem restrictCNF_normalized (σ : Restriction V) {H : CNF V}
    (hH : H.Normalized) : (restrictCNF σ H).Normalized := by
  intro D hD
  obtain ⟨C, hC, hCD⟩ := List.mem_filterMap.mp hD
  exact restrictClause_normalized (hH C hC) hCD

end DepthThreeLowerBound

end

end Complexity
