/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Rectangle
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log

/-!
# One-way summaries of rectangle-free functions

A one-way summary depends only on one side of an input partition. Equal summaries
give equal function values for every assignment on the other side. Counting its row
classes yields a nearly full-input lower bound on the number of summary bits when
the other side has only logarithmically many coordinates.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open scoped Classical

/-- A summary of the coordinates in `U` determines the function once the remaining
coordinates are known. There is no communication from the other side. -/
structure OneWaySummary {n : Nat} (f : Cslib.BooleanFunction n)
    (U : Finset (Fin n)) (T : Type*) where
  /-- The message computed from the sending party's coordinate assignment. -/
  key : (U → Bool) → T
  /-- Equal messages give identical output rows on the receiving coordinates. -/
  rows_eq : ∀ p p', key p = key p' → ∀ q : ↥Uᶜ → Bool,
    f (glue U p q) = f (glue U p' q)

/-- Rectangle freeness bounds both the large and the small accepting row classes
of a deterministic one-way summary. -/
theorem card_accepting_le_of_oneWay {n K : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (U : Finset (Fin n))
    {T : Type*} [Fintype T] (summary : OneWaySummary f U T) :
    (accepting f).card ≤ Fintype.card T * (K - 1) * 2 ^ Uᶜ.card +
      2 ^ U.card * (K - 1) := by
  classical
  let P (t : T) := Finset.univ.filter fun p => summary.key p = t
  let Q (t : T) := Finset.univ.filter fun q =>
    ∃ p, summary.key p = t ∧ f (glue U p q) = true
  let key (x : Fin n → Bool) := summary.key fun i => x i
  let fibre (t : T) := (accepting f).filter fun x => key x = t
  have rectangle (t : T) : ∀ p ∈ P t, ∀ q ∈ Q t, f (glue U p q) = true := by
    intro p hp q hq
    obtain ⟨p', hp', accepted⟩ := (Finset.mem_filter.mp hq).2
    rw [summary.rows_eq p p' ((Finset.mem_filter.mp hp).2.trans hp'.symm) q]
    exact accepted
  have fibre_le (t : T) : (fibre t).card ≤ (P t).card * (Q t).card := by
    have sub : fibre t ⊆ ((P t) ×ˢ (Q t)).image fun z => glue U z.1 z.2 := by
      intro x hx
      obtain ⟨accepted, same⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_image.mpr
      refine ⟨(fun i => x i, fun i => x i), ?_, glue_restrict U x⟩
      apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, same⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, fun i => x i, same, ?_⟩
        simpa only [glue_restrict] using mem_accepting.mp accepted
    exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans_eq
      (Finset.card_product _ _))
  have q_le (t : T) : (Q t).card ≤ 2 ^ Uᶜ.card := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using
      Finset.card_le_univ (Q t)
  have bound (t : T) : (fibre t).card ≤
      (K - 1) * 2 ^ Uᶜ.card + (P t).card * (K - 1) := by
    rcases free U (P t) (Q t) (rectangle t) with hp | hq
    · exact (fibre_le t).trans ((Nat.mul_le_mul (by lia) (q_le t)).trans
        (Nat.le_add_right _ _))
    · exact (fibre_le t).trans ((Nat.mul_le_mul_left _ (by lia)).trans
        (Nat.le_add_left _ _))
  have partition : (accepting f).card = ∑ t : T, (fibre t).card := by
    simpa [fibre] using (Finset.card_eq_sum_card_fiberwise
      (s := accepting f) (t := Finset.univ) (f := key) (fun _ _ => Finset.mem_univ _))
  have rows : ∑ t : T, (P t).card = 2 ^ U.card := by
    simpa [P, Fintype.card_bool] using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := summary.key)
      (fun _ _ => Finset.mem_univ _)).symm
  rw [partition]
  calc
    ∑ t : T, (fibre t).card ≤
        ∑ t : T, ((K - 1) * 2 ^ Uᶜ.card + (P t).card * (K - 1)) :=
      Finset.sum_le_sum fun t _ => bound t
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, rows]
      simp [Nat.mul_assoc]

/-- A dense rectangle-free function needs almost `n` one-way summary bits if the
receiver holds `clog 2 K + 3` input coordinates. -/
theorem input_le_capacity_of_oneWay {n K B : Nat} {f : Cslib.BooleanFunction n}
    (free : RectangleFree f K) (dense : 2 ^ (n - 2) ≤ (accepting f).card)
    (U : Finset (Fin n)) (right : Uᶜ.card = Nat.clog 2 K + 3)
    {T : Type*} [Fintype T] (summary : OneWaySummary f U T)
    (short : Fintype.card T ≤ 2 ^ B) :
    n ≤ B + 2 * Nat.clog 2 K + 5 := by
  have count := card_accepting_le_of_oneWay free U summary
  have cards : U.card + Uᶜ.card = n := by simp
  have pow_positive (j : Nat) : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have positive : 0 < (accepting f).card := lt_of_lt_of_le (pow_positive _) dense
  obtain ⟨x, hx⟩ := Finset.card_pos.mp positive
  have hK := free.one_lt (mem_accepting.mp hx)
  have smaller : K - 1 < 2 ^ Nat.clog 2 K :=
    lt_of_lt_of_le (by lia) (Nat.le_pow_clog (by decide) K)
  by_contra absent
  have first_exponent : B + Nat.clog 2 K + Uᶜ.card ≤ n - 3 := by lia
  have first : Fintype.card T * (K - 1) * 2 ^ Uᶜ.card < 2 ^ (n - 3) := by
    calc
      Fintype.card T * (K - 1) * 2 ^ Uᶜ.card ≤
          2 ^ B * (K - 1) * 2 ^ Uᶜ.card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ short)
      _ < 2 ^ B * 2 ^ Nat.clog 2 K * 2 ^ Uᶜ.card :=
        Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_left smaller (pow_positive _)) (pow_positive _)
      _ = 2 ^ (B + Nat.clog 2 K + Uᶜ.card) := by rw [Nat.pow_add, Nat.pow_add]
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by decide) first_exponent
  have second : 2 ^ U.card * (K - 1) < 2 ^ (n - 3) := by
    calc
      2 ^ U.card * (K - 1) < 2 ^ U.card * 2 ^ Nat.clog 2 K :=
        Nat.mul_lt_mul_of_pos_left smaller (pow_positive _)
      _ = 2 ^ (U.card + Nat.clog 2 K) := by rw [Nat.pow_add]
      _ = 2 ^ (n - 3) := by congr 1; lia
  have double : 2 ^ (n - 3) + 2 ^ (n - 3) = 2 ^ (n - 2) := by
    have exponent : n - 2 = (n - 3) + 1 := by lia
    rw [exponent, Nat.pow_succ]
    lia
  lia

end Algebraic.Cutwidth.Aggregate
