/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic.Ring

/-!
# Unrestricted depth-three lower bound: finite probability

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/FiniteProbability.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2 uDepth3 uDepth4 uDepth5 uDepth6 uDepth7 uDepth8 uDepth9 uDepth10 uDepth11
universe uDepth12 uDepth13 uDepth14 uDepth15 uDepth16 uDepth17 uDepth18 uDepth19 uDepth20 uDepth21

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

/-- A partial Boolean assignment; `none` denotes a live variable. -/
abbrev Restriction (V : Type uDepth1) := V → Option Bool
/-- Variables left unfixed by a restriction. -/
abbrev Live {V : Type uDepth2} (σ : Restriction V) := {v : V // σ v = none}

/-- Extend an assignment on live variables by the fixed coordinates. -/
def fill {V : Type uDepth3} (σ : Restriction V) (z : Cube (Live σ)) : Cube V :=
  fun v => if h : σ v = none then z ⟨v, h⟩ else (σ v).getD false

@[simp] theorem fill_live {V : Type uDepth4} (σ : Restriction V) (z : Cube (Live σ))
    (v : Live σ) : fill σ z v.val = z v := by
  simp [fill, v.property]

@[simp] theorem fill_fixed {V : Type uDepth5} (σ : Restriction V) (z : Cube (Live σ))
    (v : V) (b : Bool) (h : σ v = some b) : fill σ z v = b := by
  simp [fill, h]

/-- Uniform average over a finite type, with value zero on the empty type. -/
def finiteAvg {Ω : Type uDepth6} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

section Averages

variable {Ω : Type uDepth7} {Λ : Type uDepth8} [Fintype Ω] [Fintype Λ]

theorem finiteAvg_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    finiteAvg f = finiteAvg g := by
  unfold finiteAvg
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

@[simp] theorem finiteAvg_zero : finiteAvg (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [finiteAvg]

theorem finiteAvg_add (f g : Ω → ℝ) :
    finiteAvg (fun ω => f ω + g ω) = finiteAvg f + finiteAvg g := by
  simp [finiteAvg, Finset.sum_add_distrib, mul_add]

theorem finiteAvg_sub (f g : Ω → ℝ) :
    finiteAvg (fun ω => f ω - g ω) = finiteAvg f - finiteAvg g := by
  simp [finiteAvg, Finset.sum_sub_distrib, mul_sub]

theorem finiteAvg_const_mul (c : ℝ) (f : Ω → ℝ) :
    finiteAvg (fun ω => c * f ω) = c * finiteAvg f := by
  unfold finiteAvg
  rw [← Finset.mul_sum]
  ring

theorem finiteAvg_mul_const (f : Ω → ℝ) (c : ℝ) :
    finiteAvg (fun ω => f ω * c) = finiteAvg f * c := by
  unfold finiteAvg
  rw [← Finset.sum_mul]
  ring

theorem finiteAvg_sum {ι : Type uDepth9} (s : Finset ι) (f : ι → Ω → ℝ) :
    finiteAvg (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, finiteAvg (f i) := by
  classical
  simp only [finiteAvg, Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteAvg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ finiteAvg f := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun ω _ => h ω))

theorem finiteAvg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    finiteAvg f ≤ finiteAvg g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ω _ => h ω))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem finiteAvg_abs_le (f : Ω → ℝ) :
    |finiteAvg f| ≤ finiteAvg (fun ω => |f ω|) := by
  unfold finiteAvg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs f Finset.univ)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

@[simp] theorem finiteAvg_const [Nonempty Ω] (c : ℝ) :
    finiteAvg (fun _ : Ω => c) = c := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAvg, nsmul_eq_mul, hc]

theorem finiteAvg_equiv (e : Ω ≃ Λ) (f : Λ → ℝ) :
    finiteAvg (fun ω => f (e ω)) = finiteAvg f := by
  unfold finiteAvg
  rw [Fintype.card_congr e, e.sum_comp f]

theorem finiteAvg_comm (f : Ω → Λ → ℝ) :
    finiteAvg (fun ω => finiteAvg (f ω)) =
      finiteAvg (fun l => finiteAvg (fun ω => f ω l)) := by
  simp only [finiteAvg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro ω hω
  ring

theorem finiteAvg_product (f : Ω × Λ → ℝ) :
    finiteAvg f = finiteAvg (fun ω => finiteAvg (fun l => f (ω, l))) := by
  simp only [finiteAvg, Fintype.card_prod, Nat.cast_mul, mul_inv,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem finiteAvg_pi_prod {ι : Type uDepth10} [Fintype ι]
    {κ : ι → Type uDepth21} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → ℝ) :
    finiteAvg (fun x : ∀ i, κ i => ∏ i, f i (x i)) =
      ∏ i, finiteAvg (f i) := by
  classical
  unfold finiteAvg
  rw [Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Averages

/-- Weight a live coordinate by `p` and each fixed bit by `(1 - p) / 2`. -/
def restrictionCoordinateWeight (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

/-- Product weight of an independently sampled random restriction. -/
def restrictionWeight {V : Type uDepth11} [Fintype V] (p : ℝ) (σ : Restriction V) : ℝ :=
  ∏ v, restrictionCoordinateWeight p (σ v)

/-- Expectation with respect to the product distribution of restrictions. -/
def restrictionAvg {V : Type uDepth12} [Fintype V] (p : ℝ)
    (F : Restriction V → ℝ) : ℝ :=
  ∑ σ, restrictionWeight p σ * F σ

theorem restrictionCoordinateWeight_sum (p : ℝ) :
    (∑ a : Option Bool, restrictionCoordinateWeight p a) = 1 := by
  simp [Fintype.sum_option, restrictionCoordinateWeight]
  ring

theorem restrictionCoordinateWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Option Bool) : 0 ≤ restrictionCoordinateWeight p a := by
  cases a with
  | none => exact hp
  | some b => exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num)

theorem restrictionWeight_nonneg {V : Type uDepth13} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (σ : Restriction V) :
    0 ≤ restrictionWeight p σ := by
  exact Finset.prod_nonneg (fun v _ => restrictionCoordinateWeight_nonneg hp hp1 (σ v))

@[simp] theorem restrictionWeight_sum {V : Type uDepth14} [Fintype V] (p : ℝ) :
    (∑ σ : Restriction V, restrictionWeight p σ) = 1 := by
  classical
  unfold restrictionWeight
  rw [← Fintype.prod_sum]
  simp only [restrictionCoordinateWeight_sum, Finset.prod_const_one]

@[simp] theorem restrictionAvg_const {V : Type uDepth15} [Fintype V] (p c : ℝ) :
    restrictionAvg p (fun _ : Restriction V => c) = c := by
  simp [restrictionAvg, ← Finset.sum_mul]

theorem restrictionAvg_nonneg {V : Type uDepth16} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {F : Restriction V → ℝ}
    (hF : ∀ σ, 0 ≤ F σ) : 0 ≤ restrictionAvg p F := by
  exact Finset.sum_nonneg (fun σ _ =>
    mul_nonneg (restrictionWeight_nonneg hp hp1 σ) (hF σ))

theorem restrictionAvg_mono {V : Type uDepth17} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) {F G : Restriction V → ℝ}
    (h : ∀ σ, F σ ≤ G σ) : restrictionAvg p F ≤ restrictionAvg p G := by
  exact Finset.sum_le_sum (fun σ _ =>
    mul_le_mul_of_nonneg_left (h σ) (restrictionWeight_nonneg hp hp1 σ))

theorem restrictionAvg_add {V : Type uDepth18} [Fintype V] (p : ℝ)
    (F G : Restriction V → ℝ) :
    restrictionAvg p (fun σ => F σ + G σ) = restrictionAvg p F + restrictionAvg p G := by
  simp [restrictionAvg, mul_add, Finset.sum_add_distrib]

theorem restrictionAvg_const_mul {V : Type uDepth19} [Fintype V] (p c : ℝ)
    (F : Restriction V → ℝ) :
    restrictionAvg p (fun σ => c * F σ) = c * restrictionAvg p F := by
  simp [restrictionAvg, Finset.mul_sum, mul_left_comm]

theorem restrictionAvg_abs_le {V : Type uDepth20} [Fintype V] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (F : Restriction V → ℝ) :
    |restrictionAvg p F| ≤ restrictionAvg p (fun σ => |F σ|) := by
  unfold restrictionAvg
  calc
    _ ≤ ∑ σ, |restrictionWeight p σ * F σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [abs_mul, abs_of_nonneg (restrictionWeight_nonneg hp hp1 σ)]

end DepthThreeLowerBound

end

end Complexity
