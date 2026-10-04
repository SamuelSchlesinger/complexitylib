/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Filter
public import Complexitylib.Circuits.SparseSynthesis.Internal.PartialTable
import Complexitylib.Cslib.Circuit.Boolean.Synthesis

/-!
# Partial synthesis after hashing

Choose a representative label for every occupied hash cell, synthesize the
resulting short partial table, and patch the input points whose labels were
lost in collisions. Pairwise independence bounds this last cost.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib.Circuits Cslib.Circuits.Boolean PairwiseIndependentHash

/-- Hash cost, partial-table cost, collision repairs by minterms, and a final XOR. -/
def partialFiniteBudget (n k l K weight : ℕ) : ℕ :=
  hashBudget n (k + l) + partialTableBudget k l K weight +
    (weight * weight / 2 ^ (k + l)) * (2 * n + 2) + 5

theorem exists_partialFinite {n k l : ℕ} (domain : Finset (BitString n))
    (f : BitString n → Bool) (K : ℕ) (positive : 0 < K) :
    ∃ c : Cslib.Circuits.Circuit signature n 1,
      c.ComputesOn interpretation (domain : Set _) (fun x _ => f x) ∧
        c.size ≤ partialFiniteBudget n k l K domain.card := by
  classical
  let hash := affine n (k + l)
  obtain ⟨seed, few⟩ := exists_few_hashCollisions hash domain.offDiag
    (fun xy hxy => (Finset.mem_offDiag.mp hxy).2.2)
  let image := domain.image (hash.eval seed)
  have preimage (y : BitString (k + l)) (hy : y ∈ image) :
      ∃ x ∈ domain, hash.eval seed x = y := Finset.mem_image.mp hy
  choose representative member equal using preimage
  let label (y : BitString (k + l)) : Bool :=
    if hy : y ∈ image then f (representative y hy) else false
  obtain ⟨hc, hhc, hcost⟩ := exists_hashCircuit n (k + l) seed
  obtain ⟨tc, htc, tcost⟩ := exists_partialTable image label K positive
  let approx := tc.comp hc
  have value (x : BitString n) (hx : x ∈ domain) :
      approx.eval interpretation x 0 = label (hash.eval seed x) := by
    have hximage : hash.eval seed x ∈ image := Finset.mem_image_of_mem _ hx
    have h := congrFun (htc hximage) 0
    simpa only [approx, Cslib.Circuits.Circuit.eval_comp, hhc x, hash, affine_eval] using h
  let errors := domain.filter fun x => approx.eval interpretation x 0 ≠ f x
  have subset : errors ⊆ (hashCollisions hash domain.offDiag seed).image Prod.fst := by
    intro x hx
    have info := Finset.mem_filter.mp hx
    have hximage : hash.eval seed x ∈ image := Finset.mem_image_of_mem _ info.1
    let y := representative (hash.eval seed x) hximage
    have hy : y ∈ domain := member _ _
    have same : hash.eval seed y = hash.eval seed x := equal _ _
    have different : x ≠ y := by
      intro eqn
      have correct : approx.eval interpretation x 0 = f y := by
        rw [value x info.1]
        simp only [label, hximage, dite_true, y]
      exact info.2 (eqn ▸ correct)
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨info.1, hy, different⟩, same.symm⟩, rfl⟩
  have errorSize : errors.card ≤ domain.card * domain.card / 2 ^ (k + l) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ ≤ (hashCollisions hash domain.offDiag seed).card * 2 ^ (k + l) :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card subset).trans Finset.card_image_le)
      _ ≤ domain.offDiag.card := few
      _ ≤ domain.card * domain.card := by rw [Finset.offDiag_card]; omega
  have happrox : Synthesis interpretation (inputs n)
      {fun x => approx.eval interpretation x 0} approx.size := by
    apply approx.synthesis.mono Set.Subset.rfl ?_ le_rfl
    rintro q rfl
    exact ⟨0, rfl⟩
  have hpatch := happrox.combine (indicator_synthesis errors)
    (Synthesis.xor_of_mem (f := fun x => approx.eval interpretation x 0)
      (g := fun x => decide (x ∈ errors)) (by simp) (by simp))
  obtain ⟨c, hc, hsize⟩ := hpatch.exists_circuit
  refine ⟨c, ?_, hsize.trans ?_⟩
  · intro x hx
    rw [hc x]
    funext j
    have hx' : x ∈ domain := hx
    simp only [single_apply, errors, Finset.mem_filter, hx', true_and]
    cases approx.eval interpretation x 0 <;> cases f x <;> simp
  · have tableSize : partialTableBudget k l K image.card ≤
        partialTableBudget k l K domain.card := by
      have : image.card / K ≤ domain.card / K := Nat.div_le_div_right Finset.card_image_le
      unfold partialTableBudget
      omega
    have size : approx.size ≤ hashBudget n (k + l) + partialTableBudget k l K domain.card := by
      simpa only [approx, Cslib.Circuits.Circuit.size_comp] using
        Nat.add_le_add hcost (tcost.trans tableSize)
    have correction := Nat.mul_le_mul_right (2 * n + 2) errorSize
    unfold partialFiniteBudget
    omega

end Complexity.CircuitSparseSynthesis.Internal
