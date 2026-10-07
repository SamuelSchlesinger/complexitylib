/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionClause

/-!
# Unrestricted depth-three lower bound: restriction keep clause

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionKeepClause.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

open scoped Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1}

/-- Literals retained by the specified coordinate selection. -/
def keptLiterals (R : Finset V) (C : Clause V) : Clause V :=
  C.filter fun l => l.1 ∈ R

@[simp] theorem mem_keptLiterals (R : Finset V) (C : Clause V) (l : Literal V) :
    l ∈ keptLiterals R C ↔ l ∈ C ∧ l.1 ∈ R := by
  simp [keptLiterals]

theorem keptLiterals_scope (R : Finset V) (C : Clause V) :
    (keptLiterals R C).scope = C.scope ∩ R := by
  ext v
  simp only [Clause.scope, Finset.mem_image, Finset.mem_inter, mem_keptLiterals]
  constructor
  · rintro ⟨l, ⟨hl, hR⟩, hv⟩
    exact ⟨⟨l, hl, hv⟩, hv ▸ hR⟩
  · rintro ⟨⟨l, hl, hv⟩, hR⟩
    exact ⟨l, ⟨hl, hv.symm ▸ hR⟩, hv⟩

theorem keptLiterals_width (R : Finset V) (C : Clause V) :
    (keptLiterals R C).width = (C.scope ∩ R).card := by
  rw [Clause.width, keptLiterals_scope]

/-- Retain the selected literals of a clause. -/
def keepClause (R : Finset V) (pattern : Cube V) (C : Clause V) :
    Option (Clause V) :=
  if ∃ l ∈ C, l.1 ∉ R ∧ pattern l.1 = l.2 then none else some (keptLiterals R C)

theorem keepClause_eval (R : Finset V) (pattern x : Cube V) (C : Clause V)
    (hagree : ∀ v ∉ R, x v = pattern v) :
    residualClauseEval (keepClause R pattern C) x = C.eval x := by
  by_cases hs : ∃ l ∈ C, l.1 ∉ R ∧ pattern l.1 = l.2
  · simp only [keepClause, ite_eq_left hs, residualClauseEval_none]
    symm
    obtain ⟨l, hl, hout, hp⟩ := hs
    exact (Clause.eval_eq_true C x).mpr ⟨l, hl, (hagree l.1 hout).trans hp⟩
  · simp only [keepClause, ite_eq_right hs, residualClauseEval_some]
    apply Bool.eq_iff_iff.mpr
    rw [Clause.eval_eq_true, Clause.eval_eq_true]
    constructor
    · rintro ⟨l, hl, hx⟩
      exact ⟨l, ((mem_keptLiterals R C l).mp hl).1, hx⟩
    · rintro ⟨l, hl, hx⟩
      have hR : l.1 ∈ R := by
        by_cases hr : l.1 ∈ R
        · exact hr
        · exact (hs ⟨l, hl, hr, (hagree l.1 hr).symm.trans hx⟩).elim
      exact ⟨l, (mem_keptLiterals R C l).mpr ⟨hl, hR⟩, hx⟩

theorem keepClause_some_eq {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (h : keepClause R pattern C = some D) :
    D = keptLiterals R C := by
  unfold keepClause at h
  split at h
  · cases h
  · exact (Option.some.inj h).symm

theorem keepClause_width {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (h : keepClause R pattern C = some D) :
    D.width = (C.scope ∩ R).card := by
  rw [keepClause_some_eq h, keptLiterals_width]

theorem keepClause_normalized {R : Finset V} {pattern : Cube V}
    {C D : Clause V} (hC : C.Normalized) (h : keepClause R pattern C = some D) :
    D.Normalized := by
  rw [keepClause_some_eq h]
  exact hC.subset (Finset.filter_subset _ _)

section Restrict

variable [Fintype V]

/-- Retain selected literals after applying a restriction. -/
def keptRestrictedClause (σ : Restriction V) (R : Finset V)
    (pattern : Cube V) (C : Clause V) : Option (Clause (Live σ)) :=
  (keepClause R pattern C).bind (restrictClause σ)

theorem residualClauseEval_bind_restrict (σ : Restriction V)
    (C : Option (Clause V)) (x : Cube (Live σ)) :
    residualClauseEval (C.bind (restrictClause σ)) x =
      residualClauseEval C (fill σ x) := by
  cases C with
  | none => rfl
  | some C => exact restrictClause_eval σ C x

theorem keptRestrictedClause_eval (σ : Restriction V) (R : Finset V)
    (pattern : Cube V) (C : Clause V) (x : Cube (Live σ))
    (hagree : ∀ v ∉ R, fill σ x v = pattern v) :
    residualClauseEval (keptRestrictedClause σ R pattern C) x =
      C.eval (fill σ x) := by
  rw [keptRestrictedClause, residualClauseEval_bind_restrict]
  exact keepClause_eval R pattern (fill σ x) C hagree

theorem keptRestrictedClause_width_le {σ : Restriction V} {R : Finset V}
    {pattern : Cube V} {C : Clause V} {D : Clause (Live σ)}
    (h : keptRestrictedClause σ R pattern C = some D) :
    D.width ≤ (C.scope ∩ R).card := by
  unfold keptRestrictedClause at h
  cases he : keepClause R pattern C with
  | none => simp [he] at h
  | some E =>
    have hr : restrictClause σ E = some D := by simpa [he] using h
    rw [← keepClause_width he]
    exact restrictClause_width_le hr

end Restrict

end DepthThreeLowerBound

end

end Complexity
