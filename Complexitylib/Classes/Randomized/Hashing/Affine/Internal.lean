/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.Randomized.Hashing.Affine.Defs
import Mathlib.GroupTheory.Index

/-!
# Affine pairwise-independent hashing -- proof internals
-/


public section

namespace Complexity

namespace PairwiseIndependentHash

@[simp] theorem affineRows_affineSeedOfRows_internal
    {domainWidth rangeWidth : ℕ}
    (rows : Fin rangeWidth → BitString (domainWidth + 1)) :
    affineRows (affineSeedOfRows rows) = rows := by
  funext row column
  change Function.uncurry rows
      (finProdFinEquiv.symm (finProdFinEquiv (row, column))) = rows row column
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem affineAugment_castSucc_internal {domainWidth : ℕ}
    (input : BitString domainWidth) (column : Fin domainWidth) :
    affineAugment input column.castSucc = input column := by
  simp [affineAugment]

@[simp] theorem affineAugment_last_internal {domainWidth : ℕ}
    (input : BitString domainWidth) :
    affineAugment input (Fin.last domainWidth) = true := by
  simp [affineAugment]

/-- Affine evaluation is additive in the seed. -/
def affineEvalHom {domainWidth rangeWidth : ℕ}
    (input : BitString domainWidth) :
    BitString (affineSeedWidth domainWidth rangeWidth) →+
      BitString rangeWidth where
  toFun seed := affineEval seed input
  map_zero' := by
    funext row
    change (∑ _column : Fin (domainWidth + 1), false) = false
    rw [Finset.sum_const, nsmul_eq_mul]
    change (_ : Bool) * 0 = 0
    exact mul_zero _
  map_add' first second := by
    funext row
    simp only [affineEval, affineRows, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun column _ => ?_
    show (first (finProdFinEquiv (row, column)) + second (finProdFinEquiv (row, column))) *
        affineAugment input column = _
    ring

/-- The joint outputs on two inputs form an additive map of the seed. -/
def affinePairEvalHom {domainWidth rangeWidth : ℕ}
    (first second : BitString domainWidth) :
    BitString (affineSeedWidth domainWidth rangeWidth) →+
      BitString rangeWidth × BitString rangeWidth :=
  (affineEvalHom first).prod (affineEvalHom second)

private theorem eventProb_fiber_of_surjective_addMonoidHom
    {seedWidth : ℕ} {Output : Type*} [AddGroup Output] [Fintype Output]
    [DecidableEq Output] (map : BitString seedWidth →+ Output)
    (hsurjective : Function.Surjective map) (output : Output) :
    eventProb (Finset.univ.filter fun seed => map seed = output) =
      1 / (Fintype.card Output : ℚ) := by
  classical
  let fiber (value : Output) :=
    Finset.univ.filter fun seed : BitString seedWidth => map seed = value
  have hfibers : ∀ value, (fiber value).card = (fiber output).card := by
    intro value
    exact AddMonoidHom.card_fiber_eq_of_mem_range map
      (hsurjective value) (hsurjective output)
  have hpartition :
      (Finset.univ : Finset (BitString seedWidth)).card =
        ∑ value ∈ (Finset.univ : Finset Output), (fiber value).card := by
    exact Finset.card_eq_sum_card_fiberwise (by simp)
  have htotal :
      2 ^ seedWidth = Fintype.card Output * (fiber output).card := by
    calc
      2 ^ seedWidth =
          (Finset.univ : Finset (BitString seedWidth)).card := by
        simp
      _ = ∑ value ∈ (Finset.univ : Finset Output), (fiber value).card :=
        hpartition
      _ = ∑ _value ∈ (Finset.univ : Finset Output), (fiber output).card := by
        apply Finset.sum_congr rfl
        intro value _
        exact hfibers value
      _ = Fintype.card Output * (fiber output).card := by simp
  obtain ⟨preimage, hpreimage⟩ := hsurjective output
  have hfiberPos : 0 < (fiber output).card := by
    apply Finset.card_pos.mpr
    exact ⟨preimage, by simp [fiber, hpreimage]⟩
  have htotalRat :
      (2 : ℚ) ^ seedWidth =
        (Fintype.card Output : ℚ) * ((fiber output).card : ℚ) := by
    exact_mod_cast htotal
  change ((fiber output).card : ℚ) / (2 : ℚ) ^ seedWidth =
    1 / (Fintype.card Output : ℚ)
  rw [htotalRat]
  field_simp [show (Fintype.card Output : ℚ) ≠ 0 by positivity,
    show ((fiber output).card : ℚ) ≠ 0 by positivity]

theorem affineEvalHom_surjective_internal
    {domainWidth rangeWidth : ℕ} (input : BitString domainWidth) :
    Function.Surjective (affineEvalHom (rangeWidth := rangeWidth) input) := by
  intro output
  let rows : Fin rangeWidth → BitString (domainWidth + 1) :=
    fun row => Fin.snoc (fun _column => (0 : Bool)) (output row)
  refine ⟨affineSeedOfRows rows, ?_⟩
  funext row
  change affineEval (affineSeedOfRows rows) input row = output row
  simp only [affineEval, affineRows_affineSeedOfRows_internal]
  rw [Fin.sum_univ_castSucc]
  simp [rows, affineAugment]
  cases output row <;> rfl

private theorem affineEval_singleRow_internal
    {domainWidth rangeWidth : ℕ} (pivot : Fin domainWidth)
    (slope offset : BitString rangeWidth) (input : BitString domainWidth)
    (row : Fin rangeWidth) :
    affineEval
        (affineSeedOfRows fun currentRow =>
          Fin.snoc
            (fun column => if column = pivot then slope currentRow else (0 : Bool))
            (offset currentRow))
        input row =
      slope row * input pivot + offset row := by
  simp only [affineEval, affineRows_affineSeedOfRows_internal]
  rw [Fin.sum_univ_castSucc]
  simp [affineAugment]
  cases offset row <;> rfl

private theorem affinePair_solution_internal
    (firstBit secondBit firstOutput secondOutput : Bool)
    (hne : firstBit ≠ secondBit) :
    let slope := firstOutput + secondOutput
    let offset := firstOutput + slope * firstBit
    slope * firstBit + offset = firstOutput ∧
      slope * secondBit + offset = secondOutput := by
  cases firstBit <;> cases secondBit <;>
    cases firstOutput <;> cases secondOutput <;> simp_all <;> decide

theorem affinePairEvalHom_surjective_internal
    {domainWidth rangeWidth : ℕ} {first second : BitString domainWidth}
    (hne : first ≠ second) :
    Function.Surjective (affinePairEvalHom (rangeWidth := rangeWidth) first second) := by
  have hdiffer : ∃ pivot : Fin domainWidth, first pivot ≠ second pivot := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨pivot, hpivot⟩ := hdiffer
  rintro ⟨firstOutput, secondOutput⟩
  let slope : BitString rangeWidth :=
    fun row => firstOutput row + secondOutput row
  let offset : BitString rangeWidth :=
    fun row => firstOutput row + slope row * first pivot
  let seed := affineSeedOfRows fun row =>
    Fin.snoc
      (fun column => if column = pivot then slope row else (0 : Bool))
      (offset row)
  refine ⟨seed, ?_⟩
  apply Prod.ext
  · funext row
    change affineEval seed first row = firstOutput row
    rw [show affineEval seed first row =
        slope row * first pivot + offset row by
      exact affineEval_singleRow_internal pivot slope offset first row]
    exact (affinePair_solution_internal
      (first pivot) (second pivot) (firstOutput row) (secondOutput row) hpivot).1
  · funext row
    change affineEval seed second row = secondOutput row
    rw [show affineEval seed second row =
        slope row * second pivot + offset row by
      exact affineEval_singleRow_internal pivot slope offset second row]
    exact (affinePair_solution_internal
      (first pivot) (second pivot) (firstOutput row) (secondOutput row) hpivot).2

theorem affine_uniform_internal {domainWidth rangeWidth : ℕ}
    (input : BitString domainWidth) (output : BitString rangeWidth) :
    eventProb (Finset.univ.filter fun seed :
      BitString (affineSeedWidth domainWidth rangeWidth) =>
        affineEval seed input = output) =
      1 / (2 : ℚ) ^ rangeWidth := by
  have h := eventProb_fiber_of_surjective_addMonoidHom
    (affineEvalHom (rangeWidth := rangeWidth) input)
    (affineEvalHom_surjective_internal (rangeWidth := rangeWidth) input)
    output
  simp only [affineEvalHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, card_finArrowBool,
    Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

theorem affine_pairwise_internal {domainWidth rangeWidth : ℕ}
    {first second : BitString domainWidth} (hne : first ≠ second)
    (firstOutput secondOutput : BitString rangeWidth) :
    eventProb (Finset.univ.filter fun seed :
      BitString (affineSeedWidth domainWidth rangeWidth) =>
        affineEval seed first = firstOutput ∧
          affineEval seed second = secondOutput) =
      1 / (2 : ℚ) ^ (2 * rangeWidth) := by
  have h := eventProb_fiber_of_surjective_addMonoidHom
    (affinePairEvalHom (rangeWidth := rangeWidth) first second)
    (affinePairEvalHom_surjective_internal (rangeWidth := rangeWidth) hne)
    (firstOutput, secondOutput)
  simp only [affinePairEvalHom, affineEvalHom, AddMonoidHom.prod_apply,
    Prod.mk.injEq, Fintype.card_prod, card_finArrowBool, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat] at h
  rw [← pow_add, show rangeWidth + rangeWidth = 2 * rangeWidth by omega] at h
  exact h

end PairwiseIndependentHash

end Complexity
