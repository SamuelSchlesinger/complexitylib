/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Averaging

/-!
# Weighted retention of fixed coordinate witnesses

Double counting all subsets of a specified size retains the exact expected weight
of equally sized witness sets. In particular, triples give a common retention
factor for both two-primary and wide conjunction gates.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Joint

open scoped BigOperators Classical

/-- Some fixed-size subset retains at least the mean weight of fixed-size witnesses. -/
theorem exists_subset_weighted_witnesses {n a d : ℕ} (hda : d ≤ a) (han : a ≤ n)
    {J : Type*} [Fintype J] (witness : J → Finset (Fin n))
    (card : ∀ j, (witness j).card = d) (weight : J → ℝ) :
    ∃ U : Finset (Fin n), U.card = a ∧
      ((n - d).choose (a - d) : ℝ) * (∑ j, weight j) ≤
        (n.choose a : ℝ) * (∑ j, if witness j ⊆ U then weight j else 0) := by
  let sets := (Finset.univ : Finset (Fin n)).powersetCard a
  let score (U : Finset (Fin n)) := ∑ j, if witness j ⊆ U then weight j else 0
  have nonempty : sets.Nonempty := by
    apply Finset.card_pos.mp
    simpa [sets] using Nat.choose_pos han
  obtain ⟨U, hU, maximal⟩ := Finset.exists_max_image sets score nonempty
  refine ⟨U, (Finset.mem_powersetCard.mp hU).2, ?_⟩
  have each (j : J) : (sets.filter fun U => witness j ⊆ U).card =
      (n - d).choose (a - d) := by
    simpa only [sets, card j, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_powersetCard_subset (witness j) Finset.univ a
        (Finset.subset_univ _) (by rw [card]; exact hda)
  have total : ∑ U ∈ sets, score U =
      ((n - d).choose (a - d) : ℝ) * (∑ j, weight j) := by
    unfold score
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, each]
    rw [Finset.mul_sum]
  have bound : ∑ V ∈ sets, score V ≤ sets.card * score U := by
    calc
      ∑ V ∈ sets, score V ≤ ∑ _V ∈ sets, score U :=
        Finset.sum_le_sum fun V hV => maximal V hV
      _ = sets.card * score U := by simp
  rw [total] at bound
  simpa only [sets, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, score] using bound

/-- The exact probability that an `a`-subset retains a designated triple. -/
noncomputable def tripleRetention (n a : ℕ) : ℝ :=
  (a : ℝ) * (a - 1) * (a - 2) / ((n : ℝ) * (n - 1) * (n - 2))

/-- Three-coordinate retention follows directly from weighted witness averaging. -/
theorem exists_subset_weighted_triples {n a : ℕ} (ha : 3 ≤ a) (han : a ≤ n)
    {J : Type*} [Fintype J] (witness : J → Finset (Fin n))
    (card : ∀ j, (witness j).card = 3) (weight : J → ℝ) :
    ∃ U : Finset (Fin n), U.card = a ∧
      tripleRetention n a * (∑ j, weight j) ≤
        ∑ j, if witness j ⊆ U then weight j else 0 := by
  obtain ⟨U, hU, bound⟩ := exists_subset_weighted_witnesses ha han witness card weight
  refine ⟨U, hU, ?_⟩
  have choose_three (m : ℕ) (hm : 3 ≤ m) :
      (m.choose 3 : ℝ) = (m : ℝ) * (m - 1) * (m - 2) / 6 := by
    have h := Nat.descFactorial_eq_factorial_mul_choose m 3
    have hR : (m.descFactorial 3 : ℝ) = 6 * (m.choose 3 : ℝ) := by
      exact_mod_cast h
    rw [show 3 = 2 + 1 from rfl, Nat.descFactorial_succ, Nat.cast_mul,
      Nat.cast_sub (by lia : 2 ≤ m), Nat.cast_ofNat, Nat.cast_descFactorial_two] at hR
    linarith
  have identity : (n.choose a : ℝ) * tripleRetention n a =
      ((n - 3).choose (a - 3) : ℝ) := by
    have h := Nat.choose_mul (n := n) ha
    have hR : (n.choose a : ℝ) * (a.choose 3 : ℝ) =
        (n.choose 3 : ℝ) * ((n - 3).choose (a - 3) : ℝ) := by exact_mod_cast h
    rw [choose_three a ha, choose_three n (by lia)] at hR
    have hn : (2 : ℝ) < n := by exact_mod_cast (by lia : 2 < n)
    unfold tripleRetention
    rw [← mul_div_assoc]
    have denom : 0 < (n : ℝ) * (n - 1) * (n - 2) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    apply (div_eq_iff denom.ne').mpr
    nlinarith [hR]
  have positive : (0 : ℝ) < n.choose a := by exact_mod_cast Nat.choose_pos han
  apply (mul_le_mul_iff_right₀ positive).mp
  rw [← mul_assoc, identity]
  exact bound

end Algebraic.Cutwidth.Aggregate.Geometry.Joint
