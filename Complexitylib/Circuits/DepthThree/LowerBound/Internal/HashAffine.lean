/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.HashFibers
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Function
public import Mathlib.Tactic.Push

/-!
# Unrestricted depth-three lower bound: hash affine

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/HashAffine.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

noncomputable section

open scoped BigOperators

namespace DepthThreeLowerBound.BinaryHash

open BinaryAlgebra

variable {d r : ℕ}

/-- Assignments to coordinates outside a specified set. -/
abbrev OutsideData (T : Finset (Fin d)) := {i : Fin d // i ∉ T} → F2

/-- Assignments restricted to a specified coordinate set. -/
def coordinateCube (T : Finset (Fin d)) (rho : OutsideData T) : Set (Data d) :=
  {x | ∀ i (hi : i ∉ T), x i = rho ⟨i, hi⟩}

/-- A vector is zero outside the specified coordinate set. -/
def SupportedOn (T : Finset (Fin d)) (w : Data d) : Prop :=
  ∀ i, i ∉ T → w i = 0

/-- Extend an assignment on selected coordinates by zero outside them. -/
def coordinateCubeExtend (T : Finset (Fin d)) (rho : OutsideData T)
    (z : T → F2) : Data d :=
  fun i => if hi : i ∈ T then z ⟨i, hi⟩ else rho ⟨i, hi⟩

theorem coordinateCubeExtend_mem (T : Finset (Fin d)) (rho : OutsideData T)
    (z : T → F2) : coordinateCubeExtend T rho z ∈ coordinateCube T rho := by
  intro i hi
  simp [coordinateCubeExtend, hi]

/-- Identify selected-coordinate assignments with their extended vectors. -/
def coordinateCubeEquiv (T : Finset (Fin d)) (rho : OutsideData T) :
    (coordinateCube T rho) ≃ (T → F2) where
  toFun x := fun i => x.val i.val
  invFun z := ⟨coordinateCubeExtend T rho z, coordinateCubeExtend_mem T rho z⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · simp [coordinateCubeExtend, hi]
    · simpa [coordinateCubeExtend, hi] using (x.property i hi).symm
  right_inv z := by
    funext i
    simp [coordinateCubeExtend, i.property]

/-- Identify supported data vectors with assignments on their support. -/
def supportedDataEquiv (T : Finset (Fin d)) :
    {w : Data d // SupportedOn T w} ≃ (T → F2) where
  toFun w := fun i => w.val i.val
  invFun z := ⟨coordinateCubeExtend T 0 z, coordinateCubeExtend_mem T 0 z⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ T
    · simp [coordinateCubeExtend, hi]
    · simpa [coordinateCubeExtend, hi] using (w.property i hi).symm
  right_inv z := by
    funext i
    simp [coordinateCubeExtend, i.property]

@[simp] theorem supportedOn_zero (T : Finset (Fin d)) :
    SupportedOn T (0 : Data d) := by
  intro i hi
  rfl

theorem supportedOn_sub_of_mem {T : Finset (Fin d)} {rho : OutsideData T}
    {x y : Data d} (hx : x ∈ coordinateCube T rho)
    (hy : y ∈ coordinateCube T rho) : SupportedOn T (x - y) := by
  intro i hi
  change x i - y i = 0
  rw [hx i hi, hy i hi, sub_self]

theorem add_mem_coordinateCube {T : Finset (Fin d)} {rho : OutsideData T}
    {x w : Data d} (hx : x ∈ coordinateCube T rho) (hw : SupportedOn T w) :
    x + w ∈ coordinateCube T rho := by
  intro i hi
  change x i + w i = rho ⟨i, hi⟩
  rw [hw i hi, add_zero, hx i hi]

theorem not_injOn_coordinateCube_iff (u : Seed d r) (T : Finset (Fin d))
    (rho : OutsideData T) :
    ¬ Set.InjOn (hashF2 u) (coordinateCube T rho) ↔
      ∃ w : Data d, SupportedOn T w ∧ w ≠ 0 ∧ hashF2 u w = 0 := by
  classical
  constructor
  · intro h
    simp only [Set.InjOn] at h
    push Not at h
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := h
    refine ⟨x - y, supportedOn_sub_of_mem hx hy, sub_ne_zero.mpr hne, ?_⟩
    rw [hashF2_sub_data, hxy, sub_self]
  · rintro ⟨w, hw, hne, hkernel⟩ hinj
    let x : Data d := coordinateCubeExtend T rho 0
    have hx : x ∈ coordinateCube T rho := coordinateCubeExtend_mem T rho 0
    have hxw : x + w ∈ coordinateCube T rho := add_mem_coordinateCube hx hw
    have hhash : hashF2 u (x + w) = hashF2 u x := by
      rw [hashF2_add_data, hkernel, add_zero]
    have heq : x + w = x + 0 := by simpa using hinj hxw hx hhash
    exact hne (add_left_cancel heq)

theorem not_injOn_coordinateCube_iff_of_outside (u : Seed d r)
    (T : Finset (Fin d)) (rho sigma : OutsideData T) :
    (¬ Set.InjOn (hashF2 u) (coordinateCube T rho)) ↔
      ¬ Set.InjOn (hashF2 u) (coordinateCube T sigma) := by
  rw [not_injOn_coordinateCube_iff, not_injOn_coordinateCube_iff]

/-- The finite set of vectors supported on the selected coordinates. -/
def supportedVectors (T : Finset (Fin d)) : Finset (Data d) := by
  classical
  exact Finset.univ.filter (SupportedOn T)

@[simp] theorem mem_supportedVectors (T : Finset (Fin d)) (w : Data d) :
    w ∈ supportedVectors T ↔ SupportedOn T w := by
  classical
  simp [supportedVectors]

theorem supportedVectors_card (T : Finset (Fin d)) :
    (supportedVectors T).card = 2 ^ T.card := by
  classical
  calc
    (supportedVectors T).card = Fintype.card {w : Data d // SupportedOn T w} := by
      simpa [supportedVectors] using (Fintype.card_subtype (SupportedOn T)).symm
    _ = Fintype.card (T → F2) := Fintype.card_congr (supportedDataEquiv T)
    _ = 2 ^ T.card := by
      change Fintype.card (T → ZMod 2) = 2 ^ T.card
      rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]

/-- The nonzero vectors supported on the selected coordinates. -/
def nonzeroSupportedVectors (T : Finset (Fin d)) : Finset (Data d) :=
  (supportedVectors T).erase 0

@[simp] theorem mem_nonzeroSupportedVectors (T : Finset (Fin d)) (w : Data d) :
    w ∈ nonzeroSupportedVectors T ↔ SupportedOn T w ∧ w ≠ 0 := by
  classical
  simp [nonzeroSupportedVectors, and_comm]

theorem nonzeroSupportedVectors_card (T : Finset (Fin d)) :
    (nonzeroSupportedVectors T).card = 2 ^ T.card - 1 := by
  classical
  rw [nonzeroSupportedVectors, Finset.card_erase_of_mem, supportedVectors_card]
  exact (mem_supportedVectors T 0).mpr (supportedOn_zero T)

/-- Seeds whose hash sends the specified vector to zero. -/
def kernelSeeds (w : Data d) : Finset (Seed d r) := by
  classical
  exact Finset.univ.filter (fun u => hashF2 u w = 0)

@[simp] theorem mem_kernelSeeds (w : Data d) (u : Seed d r) :
    u ∈ kernelSeeds w ↔ hashF2 u w = 0 := by
  classical
  simp [kernelSeeds]

theorem kernelSeeds_card (w : Data d) (hw : w ≠ 0) :
    (kernelSeeds (r := r) w).card = 2 ^ (d - 1) := by
  classical
  calc
    (kernelSeeds (r := r) w).card =
        Fintype.card {u : Seed d r // hashF2 u w = 0} := by
      simpa [kernelSeeds] using
        (Fintype.card_subtype (fun u : Seed d r => hashF2 u w = 0)).symm
    _ = 2 ^ (d - 1) := hashF2_fiber_card w hw 0

/-- Seeds admitting a nonzero supported vector in the hash kernel. -/
def badSeeds (T : Finset (Fin d)) (rho : OutsideData T) : Finset (Seed d r) := by
  classical
  exact Finset.univ.filter (fun u => ¬ Set.InjOn (hashF2 u) (coordinateCube T rho))

@[simp] theorem mem_badSeeds (T : Finset (Fin d)) (rho : OutsideData T)
    (u : Seed d r) :
    u ∈ badSeeds T rho ↔ ¬ Set.InjOn (hashF2 u) (coordinateCube T rho) := by
  classical
  simp [badSeeds]

theorem badSeeds_eq_biUnion (T : Finset (Fin d)) (rho : OutsideData T) :
    badSeeds (r := r) T rho =
      (nonzeroSupportedVectors T).biUnion (fun w => kernelSeeds (r := r) w) := by
  classical
  ext u
  simp only [mem_badSeeds, Finset.mem_biUnion, mem_nonzeroSupportedVectors,
    mem_kernelSeeds, and_assoc]
  exact not_injOn_coordinateCube_iff u T rho

theorem badSeeds_eq_of_outside (T : Finset (Fin d)) (rho sigma : OutsideData T) :
    badSeeds (r := r) T rho = badSeeds T sigma := by
  rw [badSeeds_eq_biUnion, badSeeds_eq_biUnion]

theorem badSeeds_card_le (T : Finset (Fin d)) (rho : OutsideData T) :
    (badSeeds (r := r) T rho).card ≤ (2 ^ T.card - 1) * 2 ^ (d - 1) := by
  classical
  rw [badSeeds_eq_biUnion]
  calc
    ((nonzeroSupportedVectors T).biUnion (fun w => kernelSeeds (r := r) w)).card ≤
        ∑ w ∈ nonzeroSupportedVectors T, (kernelSeeds (r := r) w).card :=
      Finset.card_biUnion_le
    _ = ∑ _w ∈ nonzeroSupportedVectors T, 2 ^ (d - 1) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact kernelSeeds_card w ((mem_nonzeroSupportedVectors T w).mp hw).2
    _ = (2 ^ T.card - 1) * 2 ^ (d - 1) := by
      simp [nonzeroSupportedVectors_card]

theorem injOn_coordinateCube_empty (u : Seed d r) (rho : OutsideData (∅ : Finset (Fin d))) :
    Set.InjOn (hashF2 u) (coordinateCube ∅ rho) := by
  intro x hx y hy hxy
  funext i
  exact (hx i (by simp)).trans (hy i (by simp)).symm

@[simp] theorem badSeeds_empty (rho : OutsideData (∅ : Finset (Fin d))) :
    badSeeds (r := r) ∅ rho = ∅ := by
  classical
  ext u
  simp [injOn_coordinateCube_empty]

theorem badSeeds_card_eq_zero_of_card_eq_zero (T : Finset (Fin d))
    (rho : OutsideData T) (hT : T.card = 0) : (badSeeds (r := r) T rho).card = 0 := by
  have h : T = ∅ := Finset.card_eq_zero.mp hT
  subst T
  simp

@[simp] theorem badSeeds_zero_data (T : Finset (Fin 0)) (rho : OutsideData T) :
    badSeeds (r := r) T rho = ∅ := by
  have hT : T = ∅ := Finset.eq_empty_of_isEmpty T
  subst T
  exact badSeeds_empty rho

theorem injOn_coordinateCube_zero_output_iff (u : Seed d 0)
    (T : Finset (Fin d)) (rho : OutsideData T) :
    Set.InjOn (hashF2 u) (coordinateCube T rho) ↔ T = ∅ := by
  classical
  constructor
  · intro hinj
    by_contra hT
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    let w : Data d := fun i => if i = j then 1 else 0
    have hsupport : SupportedOn T w := by
      intro i hi
      have hij : i ≠ j := by
        intro h
        apply hi
        simpa [h] using hj
      simp [w, hij]
    have hnonzero : w ≠ 0 := by
      intro h
      have h10 : (1 : F2) = 0 := by simpa [w] using congrFun h j
      exact one_ne_zero h10
    have hkernel : hashF2 u w = 0 := by
      funext i
      exact Fin.elim0 i
    exact ((not_injOn_coordinateCube_iff u T rho).mpr
      ⟨w, hsupport, hnonzero, hkernel⟩) hinj
  · intro hT
    subst T
    exact injOn_coordinateCube_empty u rho

theorem badSeeds_zero_output (T : Finset (Fin d)) (rho : OutsideData T) :
    badSeeds (r := 0) T rho = if T = ∅ then ∅ else Finset.univ := by
  classical
  ext u
  by_cases hT : T = ∅
  · subst T
    simp
  · simp [mem_badSeeds, injOn_coordinateCube_zero_output_iff, hT]

end DepthThreeLowerBound.BinaryHash

end

end Complexity
