/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionCorrelation
public import Mathlib.Tactic.Linarith

/-!
# Unrestricted depth-three lower bound: correlation transfer

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/CorrelationTransfer.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [Fintype V] [instDecidableEqV : DecidableEq V]

omit [DecidableEq V] in
theorem restrictionAvg_mask_le
    {V : Type uDepth1}
    [Fintype V]

    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Restriction V → ℝ) (hW : ∀ σ, 0 ≤ W σ)
    (good : Restriction V → Prop) :
    restrictionAvg p (fun σ => if good σ then W σ else 0) ≤ restrictionAvg p W := by
  classical
  apply restrictionAvg_mono hp hp1
  intro σ
  split_ifs
  · exact le_rfl
  · exact hW σ
omit instDecidableEqV in
theorem restrictionAvg_abs_le_split {p ε δ C : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (q W : Restriction V → ℝ) (good : Restriction V → Prop)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ C)
    (hgood : ∀ σ, good σ → |q σ| ≤ ε * W σ)
    (hunit : ∀ σ, |q σ| ≤ 1)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ δ) :
    |restrictionAvg p q| ≤ ε * C + δ := by
  have hmask : restrictionAvg p (fun σ => if good σ then W σ else 0) ≤ C :=
    (restrictionAvg_mask_le hp hp1 W hW good).trans hmean
  calc
    |restrictionAvg p q| ≤ restrictionAvg p (fun σ => |q σ|) :=
      restrictionAvg_abs_le hp hp1 q
    _ ≤ restrictionAvg p (fun σ =>
        ε * (if good σ then W σ else 0) + (if ¬ good σ then 1 else 0)) := by
      apply restrictionAvg_mono hp hp1
      intro σ
      by_cases h : good σ
      · simpa only [h, ite_true, not_true_eq_false, ite_false, add_zero]
          using hgood σ h
      · simpa only [h, ite_false, not_false_eq_true, ite_true, mul_zero, zero_add]
          using hunit σ
    _ = ε * restrictionAvg p (fun σ => if good σ then W σ else 0) +
        restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) := by
      rw [restrictionAvg_add, restrictionAvg_const_mul]
    _ ≤ ε * C + δ := add_le_add (mul_le_mul_of_nonneg_left hmask hε) hbad

theorem abs_finiteAvg_sign_indicator_le_one {Z : Type uDepth2} [Fintype Z]
    (f J : Cube Z → Bool) :
    |finiteAvg (fun x => sign (f x) * indicator (J x))| ≤ 1 := by
  calc
    _ ≤ finiteAvg (fun x => |sign (f x) * indicator (J x)|) := finiteAvg_abs_le _
    _ ≤ finiteAvg (fun _ : Cube Z => (1 : ℝ)) := by
      apply finiteAvg_mono
      intro x
      cases f x <;> cases J x <;> norm_num [sign, indicator]
    _ = 1 := finiteAvg_const _

theorem restriction_correlation_transfer {p ε δ C : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (f : Cube V → Bool) (H : CNF V) (b : ℕ)
    (good : Restriction V → Prop) (W : Restriction V → ℝ)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ C)
    (hdom : ∀ σ,
      |finiteAvg (fun z : Cube (Live σ) =>
        sign (f (fill σ z)) * indicator (H.eval (fill σ z)))| ≤
        W σ * corr b (fun z => sign (f (fill σ z))))
    (hgood : ∀ σ, good σ → corr b (fun z => sign (f (fill σ z))) ≤ ε)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ δ) :
    |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ ε * C + δ := by
  rw [← restrictionAvg_fill p (fun x => sign (f x) * indicator (H.eval x))]
  apply restrictionAvg_abs_le_split hp hp1 hε _ W good hW hmean
  · intro σ hσ
    calc
      _ ≤ W σ * corr b (fun z => sign (f (fill σ z))) := hdom σ
      _ ≤ W σ * ε := mul_le_mul_of_nonneg_left (hgood σ hσ) (hW σ)
      _ = ε * W σ := mul_comm _ _
  · intro σ
    calc
      _ ≤ finiteAvg (fun z : Cube (Live σ) =>
          |sign (f (fill σ z)) * indicator (H.eval (fill σ z))|) := finiteAvg_abs_le _
      _ ≤ finiteAvg (fun _ : Cube (Live σ) => (1 : ℝ)) := by
        apply finiteAvg_mono
        intro z
        cases f (fill σ z) <;> cases H.eval (fill σ z) <;> norm_num [sign, indicator]
      _ = 1 := finiteAvg_const _
  · exact hbad

theorem restriction_correlation_transfer_six {p ε : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (f : Cube V → Bool) (H : CNF V) (b : ℕ)
    (good : Restriction V → Prop) (W : Restriction V → ℝ)
    (hW : ∀ σ, 0 ≤ W σ) (hmean : restrictionAvg p W ≤ 2)
    (hdom : ∀ σ,
      |finiteAvg (fun z : Cube (Live σ) =>
        sign (f (fill σ z)) * indicator (H.eval (fill σ z)))| ≤
        W σ * corr b (fun z => sign (f (fill σ z))))
    (hgood : ∀ σ, good σ → corr b (fun z => sign (f (fill σ z))) ≤ ε)
    (hbad : restrictionAvg p (fun σ => if ¬ good σ then 1 else 0) ≤ 4 * ε) :
    |finiteAvg (fun x => sign (f x) * indicator (H.eval x))| ≤ 6 * ε := by
  have h := restriction_correlation_transfer hp hp1 hε f H b good W hW hmean
    hdom hgood hbad
  linarith

end DepthThreeLowerBound

end

end Complexity
