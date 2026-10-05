/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Rectangles and rectangle-free sets

An *input* is a function `x : ι → U` from a type of coordinates to an alphabet. A set of
coordinates `X` cuts an input into two *parts*: its restriction to `X` and its restriction
to the complement `X^c`. The *rectangle* with sides `A` and `B` is the set of inputs whose
part on `X` lies in `A` and whose part on `X^c` lies in `B`.

A set of inputs `S` is `K`-*rectangle-free* when every rectangle inside `S`, for every way of
cutting the coordinates, has a side with fewer than `K` elements. This is the only property of
the hard function that the lower bound uses.

The *support lemma* `RectangleFree.pow_ncard_compl_lt` is the only other fact we need about
such sets: a large rectangle-free set depends on all but fewer than `log_|U| K` coordinates.
Indeed, if `S` ignored a set `D` of `log_|U| K` coordinates, then `S` would contain the
rectangle whose side on `D` is everything, so its other side, and hence `S`, would be small.

## Main definitions

* `Frontier.rectangle X A B`: the rectangle with sides `A` on `X` and `B` on `X^c`.
* `Frontier.RectangleFree S K`: every rectangle inside `S` has a side with fewer than `K`
  elements.

## Main results

* `Frontier.RectangleFree.ncard_le_of_dependsOn`: a rectangle-free set that ignores the
  coordinates in `D`, with `K ≤ |U| ^ |D|`, has at most `|U| ^ |D| * (K - 1)` elements.
* `Frontier.RectangleFree.pow_ncard_compl_lt`: the support lemma.
-/

@[expose] public section

namespace Complexity.Frontier

open Set

variable {ι U : Type*}

/-- The *rectangle* with sides `A` and `B` for the cut `X`: the inputs whose part on `X` lies
in `A` and whose part on the complement `X^c` lies in `B`. -/
def rectangle (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) : Set (ι → U) :=
  {x | X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B}

theorem mem_rectangle {X : Set ι} {A : Set (X → U)} {B : Set (↥Xᶜ → U)} {x : ι → U} :
    x ∈ rectangle X A B ↔ X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B :=
  Iff.rfl

/-- A set of inputs `S` is `K`-*rectangle-free* when every rectangle contained in `S`, for
every cut of the coordinates, has a side with fewer than `K` elements. -/
def RectangleFree (S : Set (ι → U)) (K : ℕ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
    rectangle X A B ⊆ S → A.ncard < K ∨ B.ncard < K

/-- An input is determined by its two parts. -/
theorem eq_of_domRestrict_eq {X : Set ι} {x y : ι → U}
    (h₁ : X.domRestrict x = X.domRestrict y) (h₂ : Xᶜ.domRestrict x = Xᶜ.domRestrict y) :
    x = y := by
  rw [domRestrict_eq_domRestrict_iff] at h₁ h₂
  funext i
  by_cases hi : i ∈ X
  · exact h₁ hi
  · exact h₂ hi

/-- Splitting an input into its two parts is injective. -/
theorem domRestrict_prod_injective (X : Set ι) :
    Function.Injective fun x : ι → U => (X.domRestrict x, Xᶜ.domRestrict x) :=
  fun _ _ h => eq_of_domRestrict_eq (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2

section Finite

variable [Finite ι] [Finite U]

/-- A rectangle-free set that does not depend on the coordinates in `D` is small: if `D` alone
carries at least `K` assignments, then `S` has at most `|U| ^ |D| * (K - 1)` elements.

The rectangle whose side on `D` is *every* assignment and whose side on `D^c` is the set of
`D^c`-parts of `S` lies inside `S`. Its first side is large, so its second side is small. -/
theorem RectangleFree.ncard_le_of_dependsOn {S : Set (ι → U)} {K : ℕ} (hS : RectangleFree S K)
    {D : Set ι} (hD : DependsOn (· ∈ S) Dᶜ) (hK : K ≤ Nat.card U ^ D.ncard) :
    S.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := by
  set B : Set (↥Dᶜ → U) := Dᶜ.domRestrict '' S
  have hsub : rectangle D univ B ⊆ S := by
    rintro z ⟨-, y, hy, hyz⟩
    have : (y ∈ S) = (z ∈ S) := hD fun i hi => congrFun hyz ⟨i, hi⟩
    exact this ▸ hy
  have hA : (univ : Set (D → U)).ncard = Nat.card U ^ D.ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
  have hB : B.ncard ≤ K - 1 := by
    rcases hS D univ B hsub with h | h
    · omega
    · omega
  calc S.ncard
      ≤ ((univ : Set (D → U)) ×ˢ B).ncard :=
        ncard_le_ncard_of_injOn _ (fun x hx => ⟨mem_univ _, x, hx, rfl⟩)
          (domRestrict_prod_injective D).injOn
    _ = Nat.card U ^ D.ncard * B.ncard := by rw [ncard_prod, hA]
    _ ≤ Nat.card U ^ D.ncard * (K - 1) := Nat.mul_le_mul_left _ hB

/-- **The support lemma.** A rectangle-free set with at least `|U| * K ^ 2` elements depends on
all but fewer than `log_|U| K` coordinates: if `S` depends only on the coordinates in `R`,
then `|U| ^ |R^c| < K`. -/
theorem RectangleFree.pow_ncard_compl_lt [Nonempty U] {S : Set (ι → U)} {K : ℕ}
    (hS : RectangleFree S K) {R : Set ι} (hR : DependsOn (· ∈ S) R)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ Rᶜ.ncard < K := by
  by_contra! hle
  have hq : 0 < Nat.card U := Nat.card_pos
  -- Some `K` is positive, since a rectangle-free set has a positive threshold.
  have hK : 0 < K := by
    rcases hS univ ∅ ∅ (by simp [rectangle]) with h | h <;> simpa using h
  -- Ignore the fewest coordinates of `R^c` that carry at least `K` assignments.
  have hex : ∃ d, K ≤ Nat.card U ^ d := ⟨_, hle⟩
  obtain ⟨d, hdK, hdmin⟩ : ∃ d, K ≤ Nat.card U ^ d ∧ ∀ d' < d, Nat.card U ^ d' < K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d' hd' => not_le.mp (Nat.find_min hex hd')⟩
  have hdR : d ≤ Rᶜ.ncard := by
    by_contra! h
    exact absurd hle (not_le.mpr (hdmin _ h))
  obtain ⟨D, hDR, rfl⟩ := exists_subset_card_eq hdR
  have hsmall := hS.ncard_le_of_dependsOn (hR.mono (subset_compl_comm.mp hDR)) hdK
  -- Minimality of `|D|` gives `|U| ^ |D| ≤ |U| * (K - 1)` once `D` is nonempty.
  have : Nat.card U ^ D.ncard * (K - 1) < Nat.card U * K ^ 2 := by
    rcases Nat.eq_zero_or_pos D.ncard with hd | hd
    · rw [hd, pow_zero, one_mul]
      calc K - 1 < K := by omega
        _ ≤ Nat.card U * K ^ 2 := by nlinarith
    · have hlt : Nat.card U ^ (D.ncard - 1) < K := hdmin _ (by omega)
      have hpow : Nat.card U ^ D.ncard = Nat.card U * Nat.card U ^ (D.ncard - 1) := by
        rw [← pow_succ']; congr 1; omega
      calc Nat.card U ^ D.ncard * (K - 1)
          ≤ Nat.card U * (K - 1) * (K - 1) := by
            rw [hpow]; gcongr; omega
        _ < Nat.card U * K ^ 2 := by
            have : (K - 1) * (K - 1) < K ^ 2 := by
              rw [sq]; exact Nat.mul_lt_mul'' (by omega) (by omega)
            nlinarith
  omega

end Finite

end Complexity.Frontier
