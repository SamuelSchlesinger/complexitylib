/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Basic

/-!
# Shifted distinctness tests

The counting argument of Victor Lecomte and Prasanna Ramakrishnan,
*Optimal Shallow Circuits for Majority*, arXiv:2609.34029v1, Sections 3 and 4.

A test shifts one weight per group element and checks that all shifted weights
are distinct. The prescribed sum of shifts makes this a one-sided certificate
for the sum of the weights. For each valid weight vector, the accepting shifts
are in bijection with permutations of the group, so there are exactly `|G|!`.

We sample from all `|G| ^ |G|` shifts and reject shifts with the wrong sum.
The paper instead samples only shifts with the prescribed sum. This slightly
weaker success density still gives the same exponential bound and avoids a
conditional sampling space. The argument works for any finite abelian group;
the circuit construction uses `ZMod k`.
-/

@[expose] public section

namespace Complexity.Shallow

open Finset

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Sum of all residues of the finite group. -/
def residueSum (G : Type*) [Fintype G] [AddCommGroup G] : G := ∑ a : G, a

/-- A shifted distinctness test certifying the target sum `t`. -/
def ShiftTest (t : G) (w s : G → G) : Prop :=
  (∑ i, s i) = residueSum G - t ∧ Function.Injective (fun i => w i + s i)

/-- Passing a shifted distinctness test certifies the sum of the weights. -/
theorem ShiftTest.sound {t : G} {w s : G → G} (h : ShiftTest t w s) :
    ∑ i, w i = t := by
  have hb := Finite.injective_iff_bijective.mp h.2
  have hs : ∑ i, (w i + s i) = residueSum G :=
    Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
  rw [sum_add_distrib, h.1] at hs
  exact add_right_cancel (b := residueSum G - t) (by simpa using hs)

/-- For a valid weight vector, choosing a permutation determines the shifts. -/
theorem shiftTest_perm {t : G} (w : G → G) (hw : ∑ i, w i = t)
    (e : Equiv.Perm G) : ShiftTest t w (fun i => e i - w i) := by
  constructor
  · rw [sum_sub_distrib, hw]
    congr 1
    exact Fintype.sum_bijective _ e.bijective _ _ (fun _ => rfl)
  · simpa only [add_sub_cancel] using e.injective

/-- Accepting shifts are precisely permutations translated by the weight vector. -/
noncomputable def acceptingShiftsEquiv {t : G} (w : G → G) (hw : ∑ i, w i = t) :
    {s : G → G // ShiftTest t w s} ≃ Equiv.Perm G where
  toFun s := Equiv.ofBijective (fun i => w i + s.1 i)
    (Finite.injective_iff_bijective.mp s.2.2)
  invFun e := ⟨fun i => e i - w i, shiftTest_perm w hw e⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    simp
  right_inv e := by
    apply Equiv.ext
    intro i
    simp

/-- Exactly `|G|!` shifts accept each weight vector with the target sum. -/
theorem card_acceptingShifts {t : G} (w : G → G) (hw : ∑ i, w i = t) :
    Nat.card {s : G → G // ShiftTest t w s} = (Fintype.card G).factorial := by
  classical
  rw [Nat.card_congr (acceptingShiftsEquiv w hw), Nat.card_eq_fintype_card,
    Fintype.card_perm]

/-- Some test accepts a weight vector exactly when its sum is the target. -/
theorem exists_shiftTest_iff (t : G) (w : G → G) :
    (∃ s, ShiftTest t w s) ↔ ∑ i, w i = t := by
  constructor
  · rintro ⟨s, hs⟩
    exact hs.sound
  · intro hw
    exact ⟨_, shiftTest_perm w hw (Equiv.refl G)⟩

/-- Distinctness is a conjunction of constraints involving only two weights. -/
theorem shiftTest_iff_pairwise (t : G) (w s : G → G) :
    ShiftTest t w s ↔ (∑ i, s i) = residueSum G - t ∧
      ∀ i j, i ≠ j → w i + s i ≠ w j + s j := by
  simp only [ShiftTest, Function.Injective, ne_eq]
  constructor
  · rintro ⟨hs, hi⟩
    exact ⟨hs, fun i j hij h => hij (hi h)⟩
  · rintro ⟨hs, hi⟩
    exact ⟨hs, fun i j h => Classical.byContradiction fun hij => hi i j hij h⟩

end Complexity.Shallow
