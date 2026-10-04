/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log

/-!
# Rectangle covers from mergeable summaries

A summary whose fibres are closed under mixing the two sides of an input partition
covers the accepted inputs by one rectangle per summary. This is the finite counting
step used when special circuit gates are checked through their partial aggregates.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open scoped Classical

/-- Replace the coordinates in `U` by those of `x`, retaining those of `y` elsewhere. -/
def mix {n : Nat} (U : Finset (Fin n)) (x y : Fin n → Bool) : Fin n → Bool :=
  glue U (fun i => x i) (fun i => y i)

/-- A finite summary with mixing-closed accepting fibres gives a rectangle cover bound.
Only one side's aggregate needs to be included in the summary. -/
theorem card_accepting_le_of_mixing {n K : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (U : Finset (Fin n))
    {T : Type*} [Fintype T] (key : (Fin n → Bool) → T)
    (closed : ∀ x ∈ accepting f, ∀ y ∈ accepting f, key x = key y →
      f (mix U x y) = true) :
    (accepting f).card ≤ Fintype.card T * (K - 1) * 2 ^ max U.card Uᶜ.card := by
  classical
  let fibre (t : T) := (accepting f).filter fun x => key x = t
  let P (t : T) := (fibre t).image fun x => (fun i : U => x i)
  let Q (t : T) := (fibre t).image fun x => (fun i : ↥Uᶜ => x i)
  have rectangle (t : T) : ∀ p ∈ P t, ∀ q ∈ Q t, f (glue U p q) = true := by
    intro p hp q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    exact closed x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
  have fibre_le (t : T) : (fibre t).card ≤ (P t).card * (Q t).card := by
    have sub : fibre t ⊆ ((P t) ×ˢ (Q t)).image fun z => glue U z.1 z.2 := by
      intro x hx
      apply Finset.mem_image.mpr
      refine ⟨(fun i => x i, fun i => x i), ?_, glue_restrict U x⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans_eq
      (Finset.card_product _ _))
  have p_le (t : T) : (P t).card ≤ 2 ^ U.card := by
    simpa [Fintype.card_bool] using Finset.card_le_univ (P t)
  have q_le (t : T) : (Q t).card ≤ 2 ^ Uᶜ.card := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using
      Finset.card_le_univ (Q t)
  have bound (t : T) : (fibre t).card ≤ (K - 1) * 2 ^ max U.card Uᶜ.card := by
    rcases free U (P t) (Q t) (rectangle t) with hp | hq
    · exact (fibre_le t).trans (Nat.mul_le_mul (by lia)
        ((q_le t).trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))))
    · calc
        (fibre t).card ≤ (P t).card * (Q t).card := fibre_le t
        _ ≤ 2 ^ max U.card Uᶜ.card * (K - 1) :=
          Nat.mul_le_mul
            ((p_le t).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))) (by lia)
        _ = _ := Nat.mul_comm _ _
  have partition : (accepting f).card = ∑ t : T, (fibre t).card := by
    simpa [fibre] using (Finset.card_eq_sum_card_fiberwise
      (s := accepting f) (t := Finset.univ) (f := key) (fun _ _ => Finset.mem_univ _))
  rw [partition]
  calc
    ∑ t : T, (fibre t).card ≤ ∑ _t : T, (K - 1) * 2 ^ max U.card Uᶜ.card :=
      Finset.sum_le_sum fun t _ => bound t
    _ = _ := by simp [Nat.mul_assoc]

/-- A dense rectangle-free function cannot have a balanced partition with a short
mixing summary. The three-bit slack avoids rounding qualifications at small sizes. -/
theorem min_card_lt_of_mixing {n K D : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (dense : 2 ^ (n - 2) ≤ (accepting f).card)
    (U : Finset (Fin n)) {T : Type*} [Fintype T] (key : (Fin n → Bool) → T)
    (short : Fintype.card T ≤ 2 ^ D)
    (closed : ∀ x ∈ accepting f, ∀ y ∈ accepting f, key x = key y →
      f (mix U x y) = true) :
    min U.card Uᶜ.card < D + Nat.clog 2 K + 3 := by
  have count := card_accepting_le_of_mixing free U key closed
  have hK : K - 1 ≤ 2 ^ Nat.clog 2 K :=
    (Nat.sub_le _ _).trans (Nat.le_pow_clog (by decide) _)
  have upper : 2 ^ (n - 2) ≤ 2 ^ (D + Nat.clog 2 K + max U.card Uᶜ.card) := by
    calc
      2 ^ (n - 2) ≤ (accepting f).card := dense
      _ ≤ Fintype.card T * (K - 1) * 2 ^ max U.card Uᶜ.card := count
      _ ≤ 2 ^ D * 2 ^ Nat.clog 2 K * 2 ^ max U.card Uᶜ.card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul short hK)
      _ = _ := by rw [Nat.pow_add, Nat.pow_add]
  have exponent : n - 2 ≤ D + Nat.clog 2 K + max U.card Uᶜ.card :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : Nat))).mp upper
  have cards : U.card + Uᶜ.card = n := by
    simp
  lia

/-- Greedily collecting parts smaller than `r` first reaches `r` before `2r`. -/
theorem exists_subset_sum_interval {ι : Type*} (weight : ι → Nat) {S : Finset ι}
    {r : Nat} (positive : 0 < r) (small : ∀ i ∈ S, weight i < r)
    (large : r ≤ ∑ i ∈ S, weight i) :
    ∃ T ⊆ S, r ≤ ∑ i ∈ T, weight i ∧ (∑ i ∈ T, weight i) < 2 * r := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty] at large; lia
  | @insert i S hi ih =>
    by_cases hS : r ≤ ∑ j ∈ S, weight j
    · obtain ⟨T, hT, hlow, hhigh⟩ := ih
        (fun j hj => small j (Finset.mem_insert_of_mem hj)) hS
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hlow, hhigh⟩
    · refine ⟨insert i S, Finset.Subset.refl _, large, ?_⟩
      rw [Finset.sum_insert hi]
      have := small i (Finset.mem_insert_self _ _)
      lia

/-- If no union of parts is balanced, one part contains all but fewer than `r` items. -/
theorem exists_large_part {ι : Type*} [Fintype ι] (weight : ι → Nat) {n r : Nat}
    (positive : 0 < r) (total : ∑ i, weight i = n) (big : 3 * r ≤ n)
    (unbalanced : ∀ S : Finset ι, min (∑ i ∈ S, weight i) (n - ∑ i ∈ S, weight i) < r) :
    ∃ i, n - r < weight i := by
  classical
  by_contra absent
  push Not at absent
  have small (i : ι) : weight i < r := by
    have := unbalanced {i}
    simp only [Finset.sum_singleton] at this
    have := absent i
    lia
  obtain ⟨S, _, low, high⟩ := exists_subset_sum_interval weight
    (S := Finset.univ) positive (fun i _ => small i) (by lia : r ≤ ∑ i, weight i)
  have := unbalanced S
  lia

end Algebraic.Cutwidth.Aggregate
