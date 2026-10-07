/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HashBool
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbabilityBounds
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.RestrictionProbability
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Unrestricted depth-three lower bound: hash probability

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HashProbability.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators Classical

namespace DepthThreeLowerBound

theorem finiteProb_eq_card_div {Ω : Type uDepth1} [Fintype Ω] (P : Ω → Prop) :
    finiteProb P = (Fintype.card {ω // P ω} : ℝ) / Fintype.card Ω := by
  simp [finiteProb, finiteAvg, Fintype.card_subtype, div_eq_mul_inv, mul_comm]

private theorem finiteProb_eq_card_div_decidable {Ω : Type uDepth2} [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    finiteProb P = (Fintype.card {ω // P ω} : ℝ) / Fintype.card Ω := by
  rw [finiteProb_eq_card_div]
  exact congrArg (fun k : ℕ => (k : ℝ) / Fintype.card Ω)
    (congrArg (@Fintype.card {ω // P ω}) (Subsingleton.elim _ _))

namespace BinaryHash

variable {d r : ℕ}

private theorem normalize_hash_count (hd : 0 < d) (c : ℝ) :
    c * (2 : ℝ) ^ (d - 1) / (2 : ℝ) ^ (d + r - 1) = c / (2 : ℝ) ^ r := by
  have he : d + r - 1 = (d - 1) + r := by omega
  rw [he, pow_add, mul_comm c]
  exact mul_div_mul_left c _ (pow_ne_zero _ (by norm_num))

theorem hashBool_fiber_probability (x : Fin d → Bool)
    (hx : x ≠ fun _ => false) (a : Fin r → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool => hashBool u x = a) =
      ((2 : ℝ) ^ r)⁻¹ := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    exact hx (Subsingleton.elim _ _)
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool => hashBool u x = a), hashBool_fiber_card x hx]
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [one_mul, one_div] using normalize_hash_count (r := r) hd 1

theorem hashBool_collision_probability (x y : Fin d → Bool) (hxy : x ≠ y) :
    finiteProb (fun u : Fin (d + r - 1) → Bool => hashBool u x = hashBool u y) =
      ((2 : ℝ) ^ r)⁻¹ := by
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    subst d
    exact hxy (Subsingleton.elim _ _)
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool => hashBool u x = hashBool u y),
    hashBool_collision_card x y hxy]
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  simpa only [one_mul, one_div] using normalize_hash_count (r := r) hd 1

theorem hashBool_badSeed_probability_le (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)) ≤
        ((2 : ℝ) ^ T.card - 1) / (2 : ℝ) ^ r := by
  by_cases hd0 : d = 0
  · subst d
    have hT : T = ∅ := by
      ext i
      exact Fin.elim0 i
    have hinj (u : Fin (0 + r - 1) → Bool) :
        Set.InjOn (hashBool u) (boolCoordinateCube T rho) := by
      intro x hx y hy hxy
      exact Subsingleton.elim _ _
    simp [finiteProb, hinj, hT]
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hcount := hashBool_badSeed_card_le (r := r) T rho
  have hcast :
      (Fintype.card {u : Fin (d + r - 1) → Bool //
        ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)} : ℝ) ≤
      ((2 : ℕ) ^ T.card - 1 : ℕ) * (2 : ℝ) ^ (d - 1) := by
    exact_mod_cast hcount
  have hpow : 1 ≤ (2 : ℕ) ^ T.card := by
    have hp : 0 < (2 : ℕ) ^ T.card := pow_pos (by decide) _
    omega
  have hsub : (((2 : ℕ) ^ T.card - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ T.card - 1 := by
    rw [Nat.cast_sub hpow]
    simp
  have hc : (Fintype.card (Fin (d + r - 1) → Bool) : ℝ) =
      (2 : ℝ) ^ (d + r - 1) := by simp []
  rw [hsub] at hcast
  rw [finiteProb_eq_card_div_decidable
    (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)), hc]
  calc
    _ ≤ (((2 : ℝ) ^ T.card - 1) * (2 : ℝ) ^ (d - 1)) /
        (2 : ℝ) ^ (d + r - 1) :=
      div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := normalize_hash_count hd _

theorem hashBool_badSeed_probability_le_pow (T : Finset (Fin d))
    (rho : {i : Fin d // i ∉ T} → Bool) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Set.InjOn (hashBool u) (boolCoordinateCube T rho)) ≤
        (2 : ℝ) ^ T.card / (2 : ℝ) ^ r := by
  exact (hashBool_badSeed_probability_le T rho).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- The fixed-coordinate contribution of a restriction to a linear hash. -/
def restrictionFixed (σ : Restriction (Fin d)) :
    {i : Fin d // i ∉ liveSet σ} → Bool :=
  fun i => (σ i.val).getD false

theorem fill_mem_boolCoordinateCube (σ : Restriction (Fin d)) (z : Cube (Live σ)) :
    fill σ z ∈ boolCoordinateCube (liveSet σ) (restrictionFixed σ) := by
  intro i hi
  have hn : σ i ≠ none := fun h => hi ((mem_liveSet σ i).mpr h)
  simp [fill, hn, restrictionFixed]

theorem range_fill_eq_boolCoordinateCube (σ : Restriction (Fin d)) :
    Set.range (fill σ) = boolCoordinateCube (liveSet σ) (restrictionFixed σ) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact fill_mem_boolCoordinateCube σ z
  · intro hx
    refine ⟨fun v => x v.val, ?_⟩
    funext i
    by_cases hi : σ i = none
    · simp [fill, hi]
    · have hnot : i ∉ liveSet σ := fun h => hi ((mem_liveSet σ i).mp h)
      simpa [fill, hi, restrictionFixed] using (hx i hnot).symm

theorem fill_injective (σ : Restriction (Fin d)) : Function.Injective (fill σ) := by
  intro z w h
  funext v
  simpa only [fill_live] using congrFun h v.val

theorem hashBool_fill_injective_iff (σ : Restriction (Fin d))
    (u : Fin (d + r - 1) → Bool) :
    Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z)) ↔
      Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ)) := by
  constructor
  · intro h x hx y hy hxy
    rw [← range_fill_eq_boolCoordinateCube] at hx hy
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact congrArg (fill σ) (h hxy)
  · intro h z w hzw
    apply fill_injective σ
    exact h (fill_mem_boolCoordinateCube σ z) (fill_mem_boolCoordinateCube σ w) hzw

theorem card_liveSet (σ : Restriction (Fin d)) :
    (liveSet σ).card = Fintype.card (Live σ) := by
  let e : Live σ ≃ ↥(liveSet σ) :=
    Equiv.subtypeEquivRight (fun i => (mem_liveSet σ i).symm)
  exact ((Fintype.card_congr e).trans (Fintype.card_coe (liveSet σ))).symm

theorem hashBool_restriction_failure_le (σ : Restriction (Fin d)) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) ≤
        ((2 : ℝ) ^ Fintype.card (Live σ) - 1) / (2 : ℝ) ^ r := by
  have he : finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) =
      finiteProb (fun u : Fin (d + r - 1) → Bool =>
        ¬ Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ))) := by
    apply finiteAvg_congr
    intro u
    by_cases h : Set.InjOn (hashBool u) (boolCoordinateCube (liveSet σ) (restrictionFixed σ))
    · have h' := (hashBool_fill_injective_iff σ u).mpr h
      simp [h, h']
    · have h' := mt (hashBool_fill_injective_iff σ u).mp h
      simp [h, h']
  rw [he]
  simpa only [card_liveSet] using
    hashBool_badSeed_probability_le (r := r) (liveSet σ) (restrictionFixed σ)

theorem hashBool_restriction_failure_le_pow (σ : Restriction (Fin d)) :
    finiteProb (fun u : Fin (d + r - 1) → Bool =>
      ¬ Function.Injective (fun z : Cube (Live σ) => hashBool u (fill σ z))) ≤
        (2 : ℝ) ^ Fintype.card (Live σ) / (2 : ℝ) ^ r := by
  exact (hashBool_restriction_failure_le σ).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

end BinaryHash
end DepthThreeLowerBound

end

end Complexity
