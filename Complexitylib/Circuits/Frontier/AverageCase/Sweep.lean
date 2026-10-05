/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.Frontier.Sweep
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Weighted approximate frontier bounds

Coherent sweeps remember that splicing also splices the message trace. This stronger
property holds for networks with unique satisfying assignments and makes state deletion
exact. The disjoint peeling argument was contributed by Sam McGuire.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {α ι U M : Type*}

/-- The sum of a real weight over a finite set. -/
noncomputable def sumOn [Finite α] (w : α → ℝ) (S : Set α) : ℝ :=
  ∑ x ∈ (Set.toFinite S).toFinset, w x

@[simp] theorem sumOn_empty [Finite α] (w : α → ℝ) : sumOn w ∅ = 0 := by
  simp [sumOn]

theorem sumOn_nonneg [Finite α] {w : α → ℝ} (hw : ∀ x, 0 ≤ w x) (S : Set α) :
    0 ≤ sumOn w S := Finset.sum_nonneg fun x _ => hw x

theorem sumOn_sdiff [Finite α] (w : α → ℝ) {S T : Set α} (h : T ⊆ S) :
    sumOn w S = sumOn w T + sumOn w (S \ T) := by
  classical
  unfold sumOn
  rw [Set.Finite.toFinset_sdiff (toFinite S) (toFinite T)]
  exact (Finset.sum_sdiff (Set.Finite.toFinset_mono h)).symm.trans (add_comm _ _)

theorem abs_sumOn_le [Finite α] {w : α → ℝ} {a : ℝ} (hw : ∀ x, |w x| ≤ a) (S : Set α) :
    |sumOn w S| ≤ a * S.ncard := by
  calc |sumOn w S| ≤ ∑ x ∈ (toFinite S).toFinset, |w x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ (toFinite S).toFinset, a := Finset.sum_le_sum fun x _ => hw x
    _ = a * S.ncard := by simp [← ncard_eq_toFinset_card, mul_comm]

/-- A pointwise nonnegative budget controls the signed weight of every thick rectangle. -/
def RectangleBudget [Finite ι] [Finite U] (w cost : (ι → U) → ℝ) (KL KR : ℕ) : Prop :=
  ∀ X A B, KL ≤ A.ncard → KR ≤ B.ncard →
    |sumOn w (rectangle X A B)| ≤ sumOn cost (rectangle X A B)

namespace Sweep

variable {S : Set (ι → U)} (P : Sweep S M)

/-- Splicing inputs through a shared message splices their whole message traces. -/
def Coherent : Prop :=
  ∀ t, ∀ x ∈ S, ∀ y ∈ S, P.message t x = P.message t y →
    ∀ z, EqOn z x (P.revealed t) → EqOn z y (P.revealed t)ᶜ →
      (∀ u, u ≤ t → P.message u z = P.message u x) ∧
      (∀ u, t ≤ u → P.message u z = P.message u y)

/-- A message class in a coherent sweep is exactly its rectangular hull. -/
theorem Coherent.peers_eq_rectangle (hP : P.Coherent) (t : ℕ) (x : ι → U) :
    P.peers t x = rectangle (P.revealed t) (P.pastSide t x) (P.futureSide t x) := by
  apply subset_antisymm
  · intro y hy
    exact ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩
  · rintro z ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
    have hab := ha.2.trans hb.2.symm
    have hza := (domRestrict_eq_domRestrict_iff.mp haz).symm
    have hzb := (domRestrict_eq_domRestrict_iff.mp hbz).symm
    exact ⟨P.splice t a ha.1 b hb.1 hab z hza hzb,
      ((hP t a ha.1 b hb.1 hab z hza hzb).1 t le_rfl).trans ha.2⟩

/-- Deleting a message class preserves a coherent sweep on exactly the remaining inputs. -/
noncomputable def erase (hP : P.Coherent) (t : ℕ) (x : ι → U) :
    Sweep (S \ P.peers t x) M where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message := P.message
  message_length a ha b hb := P.message_length a ha.1 b hb.1
  splice u a ha b hb hab z hza hzb := by
    refine ⟨P.splice u a ha.1 b hb.1 hab z hza hzb, ?_⟩
    intro hz
    have H := hP u a ha.1 b hb.1 hab z hza hzb
    rcases le_total t u with h | h
    · exact ha.2 ⟨ha.1, (H.1 t h).symm.trans hz.2⟩
    · exact hb.2 ⟨hb.1, (H.2 t h).symm.trans hz.2⟩

theorem Coherent.erase (hP : P.Coherent) (t : ℕ) (x : ι → U) :
    (P.erase hP t x).Coherent := by
  intro u a ha b hb hab z hza hzb
  exact hP u a ha.1 b hb.1 hab z hza hzb

theorem transitionCount_erase_le [Finite ι] [Finite U]
    (hP : P.Coherent) (t : ℕ) (x : ι → U) :
    (P.erase hP t x).transitionCount ≤ P.transitionCount := by
  refine Finset.sum_le_sum fun u _ => ?_
  change (P.transition u '' (S \ P.peers t x)).ncard ≤ (P.transition u '' S).ncard
  exact ncard_le_ncard (image_mono sdiff_subset) ((toFinite S).image _)

theorem transitionCount_pos [Finite ι] [Finite U] (hL : 0 < P.length)
    (hS : S.Nonempty) : 0 < P.transitionCount := by
  have hi : 0 < (P.transition 0 '' S).ncard :=
    (ncard_pos (toFinite _)).mpr (hS.image _)
  unfold transitionCount
  exact hi.trans_le (Finset.single_le_sum (f := fun t => (P.transition t '' S).ncard)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))

/-- **Weighted peeling.** A shared nonnegative budget on thick rectangles is paid once;
only the residual thin sweep pays its maximum atom times the transition count. -/
theorem abs_sumOn_le_of_budget [Finite ι] [Finite U] (hP : P.Coherent) (hL : 0 < P.length)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {w cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : RectangleBudget w cost KL KR) :
    |sumOn w S| ≤ sumOn cost S + a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) := by
  classical
  induction hn : S.ncard using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hthick : ∃ t x, x ∈ S ∧ KL ≤ (P.pastSide t x).ncard ∧ KR ≤ (P.futureSide t x).ncard
    · obtain ⟨t, x, hx, hA, hB⟩ := hthick
      let R := P.peers t x
      have hR : R ⊆ S := fun _ hy => hy.1
      have hxR : x ∈ R := ⟨hx, rfl⟩
      have hlt : (S \ R).ncard < n := by
        rw [← hn]
        exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨sdiff_subset,
          fun he => (show x ∈ S \ R from by rw [he]; exact hx).2 hxR⟩)
      have hbudget : |sumOn w R| ≤ sumOn cost R := by
        rw [show R = rectangle (P.revealed t) (P.pastSide t x) (P.futureSide t x) from
          Coherent.peers_eq_rectangle P hP t x]
        exact hrect _ _ _ hA hB
      have hrest := ih _ hlt (P.erase hP t x) (Coherent.erase P hP t x) hL rfl
      have hcount : a * (((KL - 1) * (KR - 1) * (P.erase hP t x).transitionCount : ℕ) : ℝ) ≤
          a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact_mod_cast Nat.mul_le_mul_left _ (P.transitionCount_erase_le hP t x)
      rw [sumOn_sdiff w hR, sumOn_sdiff cost hR]
      exact (abs_add_le _ _).trans (by linarith)
    · have hsmall : ∀ t, ∀ x ∈ S,
          (P.pastSide t x).ncard < KL ∨ (P.futureSide t x).ncard < KR := by
        push Not at hthick
        intro t x hx
        by_cases hA : KL ≤ (P.pastSide t x).ncard
        · exact Or.inr (hthick t x hx hA)
        · exact Or.inl (not_le.mp hA)
      have hcard : S.ncard ≤ (KL - 1) * (KR - 1) * P.transitionCount := by
        by_cases hK : KL ≤ S.ncard
        · exact P.ncard_le_of_small_sides hKL hK hsmall
        · rcases S.eq_empty_or_nonempty with hS | hS
          · simp [hS]
          · have hD := P.transitionCount_pos hL hS
            have hB : 1 ≤ KR - 1 := by lia
            have : KL - 1 ≤ (KL - 1) * (KR - 1) * P.transitionCount := by
              nlinarith [Nat.mul_le_mul_left (KL - 1) hB]
            lia
      have hcardR : a * S.ncard ≤ a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) ha
      exact (abs_sumOn_le hw S).trans (by linarith [sumOn_nonneg hc S])

end Sweep

end Complexity.Frontier
