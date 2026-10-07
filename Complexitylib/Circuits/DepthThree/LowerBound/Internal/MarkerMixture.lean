/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.MarkerPermutation
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.FiniteProbability
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.Core
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Bool.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Convert

/-!
# Unrestricted depth-three lower bound: marker mixture

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/MarkerMixture.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

universe uDepth1 uDepth2

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound

universe u v

variable {I : Type u} [Fintype I] [instDecidableEqI : DecidableEq I] {A : Type v}

/-- Determine which clause object is selected by a marker sample. -/
def markerSelected (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c)) : Finset I :=
  Finset.univ.filter fun i =>
    ∀ m : Fin c, permutationRank π (Sum.inl i) < permutationRank π (Sum.inr m)

omit [DecidableEq I] in
@[simp] theorem mem_markerSelected
    {I : Type u}
    [Fintype I]

    (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c)) (i : I) :
    i ∈ markerSelected c π ↔
      ∀ m : Fin c, permutationRank π (Sum.inl i) < permutationRank π (Sum.inr m) := by
  classical
  simp [markerSelected]
/-- Sample a marker from its permutation-based distribution. -/
def markerSample (C : I → A → Bool) (c : ℕ) (π : Equiv.Perm (I ⊕ Fin c))
    (x : A) : Bool :=
  decide (∀ i ∈ markerSelected c π, C i x = true)

@[simp] theorem markerSample_eq_true (C : I → A → Bool) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (x : A) :
    markerSample C c π x = true ↔ ∀ i ∈ markerSelected c π, C i x = true := by
  simp [markerSample]

/-- The event that a marker sample fails the prescribed selection condition. -/
def markerBad (C : I → A → Bool) (x : A) : Finset I :=
  Finset.univ.filter fun i => C i x = false

/-- The event that the sampled marker is active. -/
def markerActive (C : I → A → Bool) (x : A) (c : ℕ) : Finset (I ⊕ Fin c) :=
  (markerBad C x).disjSum Finset.univ

/-- The objects indexed by the marker construction. -/
def markerObjects (c : ℕ) : Finset (I ⊕ Fin c) :=
  (∅ : Finset I).disjSum Finset.univ

omit [DecidableEq I] in
theorem markerActive_nonempty
    {I : Type u}
    [Fintype I]

    {A : Type v}
    (C : I → A → Bool) (x : A) {c : ℕ} (hc : 0 < c) :
    (markerActive C x c).Nonempty := by
  classical
  refine ⟨Sum.inr ⟨0, hc⟩, ?_⟩
  simp [markerActive]
omit [DecidableEq I] in
theorem markerObjects_subset
    {I : Type u}
    [Fintype I]

    {A : Type v}
    (C : I → A → Bool) (x : A) (c : ℕ) :
    markerObjects (I := I) c ⊆ markerActive C x c := by
  classical
  intro s hs
  cases s with
  | inl i => simp [markerObjects] at hs
  | inr m => simp [markerActive]
theorem markerSample_iff_first_marker (C : I → A → Bool) (x : A)
    {c : ℕ} (hc : 0 < c) (π : Equiv.Perm (I ⊕ Fin c)) :
    markerSample C c π x = true ↔
      ∃ s ∈ markerObjects (I := I) c, IsFirst (markerActive C x c) π s := by
  constructor
  · intro hsample
    have hgood := (markerSample_eq_true C c π x).mp hsample
    obtain ⟨s, hs⟩ := exists_isFirst (markerActive C x c)
      (markerActive_nonempty C x hc) π
    cases s with
    | inr m => exact ⟨Sum.inr m, by simp [markerObjects], hs⟩
    | inl i =>
      have hbad : C i x = false := by simpa [markerActive, markerBad] using hs.1
      have hselected : i ∈ markerSelected c π := by
        apply (mem_markerSelected c π i).mpr
        intro m
        have hle := hs.2 (Sum.inr m) (by simp [markerActive])
        apply lt_of_le_of_ne hle
        intro heq
        have hlabels := permutationRank_injective π heq
        cases hlabels
      have htrue := hgood i hselected
      rw [hbad] at htrue
      cases htrue
  · rintro ⟨s, hs, hfirst⟩
    apply (markerSample_eq_true C c π x).mpr
    cases s with
    | inl i => simp [markerObjects] at hs
    | inr m =>
      intro i hi
      by_contra hnot
      have hbad : C i x = false := Bool.eq_false_of_not_eq_true hnot
      have hactive : Sum.inl i ∈ markerActive C x c := by
        simp [markerActive, markerBad, hbad]
      have hle := hfirst.2 (Sum.inl i) hactive
      have hlt := (mem_markerSelected c π i).mp hi m
      exact (not_lt_of_ge hle) hlt

theorem marker_mixture_ratio (C : I → A → Bool) (x : A) {c : ℕ} (hc : 0 < c) :
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) =>
      indicator (markerSample C c π x)) =
      (c : ℝ) / ((c : ℝ) + ((markerBad C x).card : ℝ)) := by
  classical
  calc
    finiteAvg (fun π : Equiv.Perm (I ⊕ Fin c) =>
        indicator (markerSample C c π x)) =
        (∑ π : Equiv.Perm (I ⊕ Fin c),
          if ∃ s ∈ markerObjects (I := I) c, IsFirst (markerActive C x c) π s
          then (1 : ℝ) else 0) / (Fintype.card (Equiv.Perm (I ⊕ Fin c)) : ℝ) := by
      unfold finiteAvg indicator
      simp_rw [markerSample_iff_first_marker C x hc]
      rw [div_eq_mul_inv, mul_comm]
    _ = ((markerObjects (I := I) c).card : ℝ) /
        ((markerActive C x c).card : ℝ) :=
      permutation_first_ratio (markerActive C x c) (markerObjects c)
        (markerActive_nonempty C x hc) (markerObjects_subset C x c)
    _ = (c : ℝ) / ((c : ℝ) + ((markerBad C x).card : ℝ)) := by
      simp [markerObjects, markerActive, Finset.card_disjSum, Nat.cast_add, add_comm]

theorem markerSample_of_all_true (C : I → A → Bool) (x : A) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) (hC : ∀ i, C i x = true) :
    markerSample C c π x = true := by
  apply (markerSample_eq_true C c π x).mpr
  exact fun i _ => hC i

theorem markerSample_of_isEmpty [IsEmpty I] (C : I → A → Bool) (x : A) (c : ℕ)
    (π : Equiv.Perm (I ⊕ Fin c)) : markerSample C c π x = true := by
  apply markerSample_of_all_true
  intro i
  exact isEmptyElim i

theorem marker_product_mixture_ratio {H : Type uDepth1} [Fintype H] [DecidableEq H]
    {J : H → Type uDepth2} [∀ h, Fintype (J h)] [∀ h, DecidableEq (J h)]
    (C : ∀ h, J h → A → Bool) (c : H → ℕ) (hc : ∀ h, 0 < c h) (x : A) :
    finiteAvg (fun π : ∀ h, Equiv.Perm (J h ⊕ Fin (c h)) =>
      ∏ h, indicator (markerSample (C h) (c h) (π h) x)) =
      ∏ h, (c h : ℝ) / ((c h : ℝ) + ((markerBad (C h) x).card : ℝ)) := by
  calc
    _ = ∏ h, finiteAvg (fun π : Equiv.Perm (J h ⊕ Fin (c h)) =>
        indicator (markerSample (C h) (c h) π x)) := by
      convert finiteAvg_pi_prod (fun h (π : Equiv.Perm (J h ⊕ Fin (c h))) =>
        indicator (markerSample (C h) (c h) π x))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro h _
      exact marker_mixture_ratio (C h) x (hc h)

end DepthThreeLowerBound

end

end Complexity
