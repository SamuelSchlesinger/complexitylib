/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.ReversePathWeights

/-!
# Unrestricted depth-three lower bound: restriction probability

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/RestrictionProbability.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

variable {V : Type uDepth1} [instFintypeV : Fintype V] [instDecidableEqV : DecidableEq V]

/-- The finite set of coordinates left live by a restriction. -/
def liveSet (σ : Restriction V) : Finset V :=
  Finset.univ.filter (fun v => σ v = none)

omit [DecidableEq V] in
@[simp] theorem mem_liveSet
    {V : Type uDepth1}
    [instFintypeV : Fintype V]

    (σ : Restriction V) (v : V) :
    v ∈ liveSet σ ↔ σ v = none := by
  classical
  simp [liveSet]
/-- Build a restriction from a live-coordinate mask and fixed bits. -/
def maskRestriction (T : Finset V) (y : Cube V) : Restriction V :=
  fun v => if v ∈ T then none else some (y v)

omit [Fintype V] in
@[simp] theorem maskRestriction_live
    {V : Type uDepth1}

    [instDecidableEqV : DecidableEq V]
    (T : Finset V) (y : Cube V) (v : V)
    (hv : v ∈ T) : maskRestriction T y v = none := by
  simp [maskRestriction, hv]
omit [Fintype V] in
@[simp] theorem maskRestriction_fixed
    {V : Type uDepth1}

    [instDecidableEqV : DecidableEq V]
    (T : Finset V) (y : Cube V) (v : V)
    (hv : v ∉ T) : maskRestriction T y v = some (y v) := by
  simp [maskRestriction, hv]
@[simp] theorem liveSet_maskRestriction (T : Finset V) (y : Cube V) :
    liveSet (maskRestriction T y) = T := by
  ext v
  by_cases hv : v ∈ T <;> simp [liveSet, maskRestriction, hv]

omit instFintypeV in
@[simp] theorem fill_maskRestriction (T : Finset V) (y : Cube V) :
    fill (maskRestriction T y) (fun v => y v.val) = y := by
  funext v
  by_cases hv : v ∈ T
  · exact fill_live (maskRestriction T y) (fun w => y w.val)
      ⟨v, maskRestriction_live T y v hv⟩
  · exact fill_fixed (maskRestriction T y) (fun w => y w.val) v (y v)
      (maskRestriction_fixed T y v hv)

@[simp] theorem maskRestriction_fill (σ : Restriction V) (z : Cube (Live σ)) :
    maskRestriction (liveSet σ) (fill σ z) = σ := by
  funext v
  cases hv : σ v with
  | none => simp [maskRestriction, hv]
  | some b => simp [maskRestriction, hv]

/-- Decompose a restriction into its mask and fixed assignments. -/
def restrictionCoordinates (s : Σ σ : Restriction V, Cube (Live σ)) :
    Finset V × Cube V :=
  (liveSet s.1, fill s.1 s.2)

theorem restrictionCoordinates_injective :
    Function.Injective (restrictionCoordinates (V := V)) := by
  rintro ⟨σ, z⟩ ⟨τ, w⟩ h
  have hsets : liveSet σ = liveSet τ := congrArg Prod.fst h
  have hfills : fill σ z = fill τ w := congrArg Prod.snd h
  have hστ : σ = τ := by
    calc
      σ = maskRestriction (liveSet σ) (fill σ z) := (maskRestriction_fill σ z).symm
      _ = maskRestriction (liveSet τ) (fill τ w) := by rw [hsets, hfills]
      _ = τ := maskRestriction_fill τ w
  subst τ
  have hzw : z = w := by
    funext v
    simpa only [fill_live] using congrFun hfills v.val
  cases hzw
  rfl

theorem restrictionCoordinates_surjective :
    Function.Surjective (restrictionCoordinates (V := V)) := by
  rintro ⟨T, y⟩
  refine ⟨⟨maskRestriction T y, fun v => y v.val⟩, ?_⟩
  exact Prod.ext (liveSet_maskRestriction T y) (fill_maskRestriction T y)

/-- Identify restrictions with their masks and fixed-coordinate assignments. -/
def restrictionCoordinatesEquiv :
    (Σ σ : Restriction V, Cube (Live σ)) ≃ (Finset V × Cube V) :=
  Equiv.ofBijective restrictionCoordinates
    ⟨restrictionCoordinates_injective, restrictionCoordinates_surjective⟩

@[simp] theorem restrictionCoordinatesEquiv_apply
    (s : Σ σ : Restriction V, Cube (Live σ)) :
    restrictionCoordinatesEquiv s = (liveSet s.1, fill s.1 s.2) := rfl

@[simp] theorem card_live_maskRestriction (T : Finset V) (y : Cube V) :
    Fintype.card (Live (maskRestriction T y)) = T.card := by
  let e : Live (maskRestriction T y) ≃ ↥T :=
    Equiv.subtypeEquivRight (fun v => by
      by_cases hv : v ∈ T <;> simp [maskRestriction, hv])
  exact (Fintype.card_congr e).trans (Fintype.card_coe T)

theorem restrictionWeight_maskRestriction (p : ℝ) (T : Finset V) (y : Cube V) :
    restrictionWeight p (maskRestriction T y) =
      p ^ T.card * ((1 - p) / 2) ^ (Fintype.card V - T.card) := by
  classical
  have hprodLive :
      (∏ v ∈ T, restrictionCoordinateWeight p (maskRestriction T y v)) =
        p ^ T.card := by
    calc
      _ = ∏ _v ∈ T, p := by
        apply Finset.prod_congr rfl
        intro v hv
        simp [maskRestriction, hv, restrictionCoordinateWeight]
      _ = _ := by simp
  have hprodFixed :
      (∏ v ∈ Tᶜ, restrictionCoordinateWeight p (maskRestriction T y v)) =
        ((1 - p) / 2) ^ (Fintype.card V - T.card) := by
    calc
      _ = ∏ _v ∈ Tᶜ, ((1 - p) / 2) := by
        apply Finset.prod_congr rfl
        intro v hv
        have hv' : v ∉ T := Finset.mem_compl.mp hv
        simp [maskRestriction, hv', restrictionCoordinateWeight]
      _ = _ := by simp only [Finset.prod_const, Finset.card_compl]
  unfold restrictionWeight
  rw [← Finset.prod_mul_prod_compl T
    (fun v => restrictionCoordinateWeight p (maskRestriction T y v))]
  rw [hprodLive, hprodFixed]

theorem restriction_mask_joint_weight (p : ℝ) (T : Finset V) (y : Cube V) :
    restrictionWeight p (maskRestriction T y) *
        (Fintype.card (Cube (Live (maskRestriction T y))) : ℝ)⁻¹ =
      bernoulliWeight p T * (Fintype.card (Cube V) : ℝ)⁻¹ := by
  have hcLive : (Fintype.card (Cube (Live (maskRestriction T y))) : ℝ) =
      (2 : ℝ) ^ T.card := by
    simp [Cube]
  have hcV : (Fintype.card (Cube V) : ℝ) =
      (2 : ℝ) ^ Fintype.card V := by
    simp [Cube]
  rw [restrictionWeight_maskRestriction, hcLive, hcV]
  unfold bernoulliWeight
  calc
    _ = (p ^ T.card * (1 - p) ^ (Fintype.card V - T.card)) *
        (((2 : ℝ) ^ (Fintype.card V - T.card))⁻¹ *
          ((2 : ℝ) ^ T.card)⁻¹) := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ = _ := by
      rw [← mul_inv, ← pow_add, Nat.sub_add_cancel T.card_le_univ]

theorem restriction_fill_joint_weight (p : ℝ) (σ : Restriction V)
    (z : Cube (Live σ)) :
    restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹ =
      bernoulliWeight p (liveSet σ) * (Fintype.card (Cube V) : ℝ)⁻¹ := by
  have h := restriction_mask_joint_weight p (liveSet σ) (fill σ z)
  simpa only [maskRestriction_fill] using h

theorem restrictionAvg_fill_coupling (p : ℝ)
    (F : Restriction V → Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F σ (fill σ z))) =
      ∑ T : Finset V, bernoulliWeight p T *
        finiteAvg (fun y : Cube V => F (maskRestriction T y) y) := by
  classical
  unfold restrictionAvg finiteAvg
  calc
    _ = ∑ σ : Restriction V, ∑ z : Cube (Live σ),
        (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
          F σ (fill σ z) := by
      refine Finset.sum_congr ?_ ?_
      · ext σ
        simp only [Finset.mem_univ]
      · intro σ hσ
        dsimp only
        rw [← mul_assoc, Finset.mul_sum]
    _ = ∑ s : (Σ σ : Restriction V, Cube (Live σ)),
        (restrictionWeight p s.1 * (Fintype.card (Cube (Live s.1)) : ℝ)⁻¹) *
          F s.1 (fill s.1 s.2) := by
      exact (Fintype.sum_sigma'
        (fun (σ : Restriction V) (z : Cube (Live σ)) =>
          (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
            F σ (fill σ z))).symm
    _ = ∑ Ty : Finset V × Cube V,
        (bernoulliWeight p Ty.1 * (Fintype.card (Cube V) : ℝ)⁻¹) *
          F (maskRestriction Ty.1 Ty.2) Ty.2 := by
      apply Fintype.sum_equiv (restrictionCoordinatesEquiv (V := V))
      rintro ⟨σ, z⟩
      change (restrictionWeight p σ * (Fintype.card (Cube (Live σ)) : ℝ)⁻¹) *
          F σ (fill σ z) =
        (bernoulliWeight p (liveSet σ) * (Fintype.card (Cube V) : ℝ)⁻¹) *
          F (maskRestriction (liveSet σ) (fill σ z)) (fill σ z)
      rw [restriction_fill_joint_weight p σ z, maskRestriction_fill]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only
      rw [← Finset.mul_sum]
      ring

theorem restrictionAvg_fill_reweight (p : ℝ)
    (F : Restriction V → Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F σ (fill σ z))) =
      finiteAvg (fun y : Cube V =>
        ∑ T : Finset V, bernoulliWeight p T * F (maskRestriction T y) y) := by
  rw [restrictionAvg_fill_coupling, finiteAvg_sum]
  apply Finset.sum_congr rfl
  intro T hT
  exact (finiteAvg_const_mul (bernoulliWeight p T)
    (fun y : Cube V => F (maskRestriction T y) y)).symm

theorem restrictionAvg_fill (p : ℝ) (F : Cube V → ℝ) :
    restrictionAvg p (fun σ => finiteAvg (fun z : Cube (Live σ) => F (fill σ z))) =
      finiteAvg F := by
  calc
    _ = ∑ T : Finset V, bernoulliWeight p T * finiteAvg F :=
      restrictionAvg_fill_coupling p (fun _ y => F y)
    _ = _ := by rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem restrictionAvg_mask_sampler (p : ℝ) (F : Restriction V → ℝ) :
    restrictionAvg p F = ∑ T : Finset V, bernoulliWeight p T *
      finiteAvg (fun y : Cube V => F (maskRestriction T y)) := by
  simpa only [finiteAvg_const] using
    restrictionAvg_fill_coupling p (fun σ _ => F σ)

end DepthThreeLowerBound

end

end Complexity
