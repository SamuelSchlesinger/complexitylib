/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Counting below, and the element counted to

A finite set of numbers is enumerated in increasing order by
`Finset.orderEmbOfFin`. An algorithm cannot enumerate; what it can do is count.
This module connects the two: the position of an element in the increasing
enumeration is the number of elements below it, so an algorithm finds the `k`-th
element by looking for the one with `k` elements below it.

## Main definitions

- `Complexity.countBelow` — how many elements of a set lie below a number

## Main results

- `Complexity.countBelow_orderEmbOfFin` — counting below the `i`-th element
  gives `i`
- `Complexity.orderEmbOfFin_eq_of_countBelow` — so the count names the element
- `Complexity.idxOf_eq_countP` — and in a list sorted by a key, the position of
  an entry is the number of entries with a smaller key
-/

@[expose] public section

namespace Complexity

/-- How many elements of `S` lie below `p`. -/
def countBelow (S : Finset ℕ) (p : ℕ) : ℕ := (S.filter (· < p)).card

/-- **Counting below the `i`-th smallest element gives `i`.** -/
theorem countBelow_orderEmbOfFin (S : Finset ℕ) {k : ℕ} (h : S.card = k) (i : Fin k) :
    countBelow S (S.orderEmbOfFin h i) = i.val := by
  classical
  have himg : Finset.image (S.orderEmbOfFin h) Finset.univ = S :=
    S.image_orderEmbOfFin_univ h
  have hfilter : S.filter (· < S.orderEmbOfFin h i)
      = Finset.image (S.orderEmbOfFin h) (Finset.Iio i) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hqS, hqlt⟩
      have hq : q ∈ Finset.image (S.orderEmbOfFin h) Finset.univ := by rw [himg]; exact hqS
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨j, (OrderEmbedding.lt_iff_lt _).mp hqlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨S.orderEmbOfFin_mem h j, (OrderEmbedding.lt_iff_lt _).mpr hj⟩
  rw [countBelow, hfilter, Finset.card_image_of_injective _ (S.orderEmbOfFin h).injective,
    Fin.card_Iio]

/-- **The count names the element.** -/
theorem orderEmbOfFin_eq_of_countBelow {S : Finset ℕ} {k : ℕ} (h : S.card = k) (i : Fin k)
    {p : ℕ} (hp : p ∈ S) (hcount : countBelow S p = i.val) : S.orderEmbOfFin h i = p := by
  classical
  have himg : Finset.image (S.orderEmbOfFin h) Finset.univ = S :=
    S.image_orderEmbOfFin_univ h
  rw [← himg, Finset.mem_image] at hp
  obtain ⟨j, -, hj⟩ := hp
  have hjcount : countBelow S (S.orderEmbOfFin h j) = j.val :=
    countBelow_orderEmbOfFin S h j
  rw [hj, hcount] at hjcount
  rw [← hj]
  exact congrArg _ (Fin.ext hjcount)

/-- **Counting below is strictly monotone along the set.** -/
theorem countBelow_lt_countBelow {S : Finset ℕ} {j c : ℕ} (hj : j ∈ S) (hlt : j < c) :
    countBelow S j < countBelow S c := by
  classical
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, by omega⟩
  · intro hsub
    have hjc : j ∈ S.filter (· < c) := Finset.mem_filter.mpr ⟨hj, hlt⟩
    have := hsub hjc
    rw [Finset.mem_filter] at this
    omega

/-- **An element's position is below the size.** -/
theorem countBelow_lt_card {S : Finset ℕ} {c : ℕ} (hc : c ∈ S) : countBelow S c < S.card := by
  classical
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, ?_⟩
  intro hsub
  have := hsub hc
  rw [Finset.mem_filter] at this
  omega

/-! ### Positions in a sorted list -/

/-- **In a list sorted by a key, an entry's position is the number of entries
with a smaller key.** -/
theorem idxOf_eq_countP {β : Type} [BEq β] [LawfulBEq β] {key : β → ℕ} :
    ∀ {l : List β}, List.Pairwise (fun p q => key p ≤ key q) l →
      (∀ p ∈ l, ∀ q ∈ l, key p = key q → p = q) →
      ∀ {x : β}, x ∈ l → l.idxOf x = l.countP fun q => decide (key q < key x)
  | [], _, _, _, hx => by simp at hx
  | a :: t, hpair, hinj, x, hx => by
      rw [List.pairwise_cons] at hpair
      by_cases hxa : x = a
      · subst hxa
        have hzero : (t.countP fun q => decide (key q < key x)) = 0 := by
          refine List.countP_eq_zero.mpr fun q hq => ?_
          have := hpair.1 q hq
          simp only [decide_eq_true_eq]
          omega
        rw [List.idxOf_cons_self, List.countP_cons, hzero]
        simp
      · have hxt : x ∈ t := by
          rcases List.mem_cons.mp hx with h | h
          · exact absurd h hxa
          · exact h
        have hlt : key a < key x := by
          have hle := hpair.1 x hxt
          have hne : key a ≠ key x := fun h =>
            hxa (hinj x (List.mem_cons_of_mem _ hxt) a List.mem_cons_self h.symm)
          omega
        have hih := idxOf_eq_countP hpair.2
          (fun p hp q hq => hinj p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)) hxt
        rw [List.idxOf_cons_ne _ (Ne.symm hxa), hih, List.countP_cons]
        simp only [decide_eq_true_eq, ite_eq_left hlt]

end Complexity
