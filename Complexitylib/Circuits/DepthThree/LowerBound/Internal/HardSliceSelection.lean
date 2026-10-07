/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbabilityBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionTails
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCorrelation
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: hard slice selection

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HardSliceSelection.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} {Ω : Type uDepth2} [Fintype V] [instDecidableEqV : DecidableEq V]
  [Fintype Ω] [Nonempty Ω]

omit [DecidableEq V] in
theorem exists_small_restriction_failure
    {V : Type uDepth1}
    {Ω : Type uDepth2}
    [Fintype V]

    [Fintype Ω]
    [Nonempty Ω]
    {p δ η : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (window : Restriction V → Prop) (good : Ω → Restriction V → Prop)
    (hfixed : ∀ σ, window σ → finiteProb (fun ω => ¬ good ω σ) ≤ δ)
    (hwindow : restrictionAvg p (fun σ => if ¬ window σ then 1 else 0) ≤ η) :
    ∃ ω : Ω,
      restrictionAvg p (fun σ => if ¬ (window σ ∧ good ω σ) then 1 else 0) ≤ η + δ := by
  classical
  have hpoint : ∀ σ : Restriction V,
      finiteAvg (fun ω : Ω => if ¬ (window σ ∧ good ω σ) then (1 : ℝ) else 0) ≤
        (if ¬ window σ then 1 else 0) + δ := by
    intro σ
    by_cases hσ : window σ
    · have hfixed' : finiteAvg (fun ω : Ω => if ¬ good ω σ then (1 : ℝ) else 0) ≤ δ := by
        calc
          _ = finiteProb (fun ω => ¬ good ω σ) := by
            apply finiteAvg_congr
            intro ω
            exact (ite_eq_ite _ _ _).mpr trivial
          _ ≤ δ := hfixed σ hσ
      simpa only [hσ, true_and, not_true_eq_false, ite_false, zero_add] using hfixed'
    · simpa only [hσ, false_and, not_false_eq_true, ite_true, finiteAvg_const]
        using (le_add_of_nonneg_right hδ : (1 : ℝ) ≤ 1 + δ)
  apply finiteAvg_exists_le_of_le
  calc
    _ = restrictionAvg p (fun σ =>
        finiteAvg (fun ω : Ω => if ¬ (window σ ∧ good ω σ) then 1 else 0)) :=
      finiteAvg_restrictionAvg p _
    _ ≤ restrictionAvg p (fun σ => (if ¬ window σ then 1 else 0) + δ) :=
      restrictionAvg_mono hp hp1 hpoint
    _ = restrictionAvg p (fun σ => if ¬ window σ then 1 else 0) + δ := by
      rw [restrictionAvg_add, restrictionAvg_const]
    _ ≤ η + δ := add_le_add_left hwindow δ
/-- The allowed interval for the number of surviving coordinates. -/
def restrictionWindow (p : ℝ) (σ : Restriction V) : Prop :=
  (p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
    (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)

/-- A restriction satisfying the survival and correlation requirements. -/
def goodRestriction (p ε : ℝ) (b : ℕ) (f : Cube V → Bool)
    (σ : Restriction V) : Prop :=
  restrictionWindow p σ ∧ corr b (fun z => sign (f (fill σ z))) ≤ ε

omit [DecidableEq V] in
theorem goodRestriction_corr
    {V : Type uDepth1}
    [Fintype V]

    {p ε : ℝ} {b : ℕ} {f : Cube V → Bool}
    {σ : Restriction V} (h : goodRestriction p ε b f σ) :
    corr b (fun z => sign (f (fill σ z))) ≤ ε := h.2
theorem exists_good_parameter {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : ℕ) (f : Ω → Cube V → Bool)
    (hfixed : ∀ σ : Restriction V, restrictionWindow p σ →
      finiteProb (fun ω =>
        ¬ corr b (fun z => sign (f ω (fill σ z))) ≤
          (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) ≤
        2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) :
    ∃ ω : Ω,
      restrictionAvg p (fun σ => if ¬ goodRestriction p
        ((2 : ℝ) ^ (-(p * Fintype.card V) / 16)) b (f ω) σ then 1 else 0) ≤
      4 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
  have hε : 0 ≤ (2 : ℝ) ^ (-(p * Fintype.card V) / 16) :=
    Real.rpow_nonneg (by norm_num) _
  have hwindow : restrictionAvg p (fun σ : Restriction V =>
      if ¬ restrictionWindow p σ then 1 else 0) ≤
      2 * (2 : ℝ) ^ (-(p * Fintype.card V) / 16) := by
    calc
      _ = restrictionAvg p (fun σ : Restriction V =>
          if ¬ ((p * Fintype.card V) / 2 ≤ (Fintype.card (Live σ) : ℝ) ∧
            (Fintype.card (Live σ) : ℝ) ≤ 2 * (p * Fintype.card V)) then 1 else 0) := by
        apply congrArg (restrictionAvg p)
        funext σ
        exact (ite_eq_ite _ _ _).mpr trivial
      _ ≤ _ := restrictionAvg_outside_window (V := V) p hp hp1
  obtain ⟨ω, hω⟩ := exists_small_restriction_failure hp hp1
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)
    (restrictionWindow p)
    (fun ω σ => corr b (fun z => sign (f ω (fill σ z))) ≤
      (2 : ℝ) ^ (-(p * Fintype.card V) / 16))
    hfixed hwindow
  refine ⟨ω, ?_⟩
  have heq : restrictionAvg p (fun σ => if ¬ goodRestriction p
      ((2 : ℝ) ^ (-(p * Fintype.card V) / 16)) b (f ω) σ then 1 else 0) =
      restrictionAvg p (fun σ => if ¬ (restrictionWindow p σ ∧
        corr b (fun z => sign (f ω (fill σ z))) ≤
          (2 : ℝ) ^ (-(p * Fintype.card V) / 16)) then 1 else 0) := by
    apply congrArg (restrictionAvg p)
    funext σ
    exact (ite_eq_ite _ _ _).mpr trivial
  rw [heq]
  linarith

end DepthThreeLowerBound

end

end Complexity
