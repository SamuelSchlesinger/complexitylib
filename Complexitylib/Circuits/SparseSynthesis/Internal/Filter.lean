/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.HashCircuit
public import Complexitylib.Circuits.SparseSynthesis.Internal.HashCollision
public import Complexitylib.Circuits.SparseSynthesis.Internal.SparseTable
public import Complexitylib.Cslib.Circuit.Synthesis

/-!
# Sparse separating filters

Hash the positive set into a shorter table, synthesize its image, and pull the
result back along the hash. Every positive input survives; few specified
negative inputs survive. Repeated filters reduce the remaining false positives
geometrically.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib.Circuits Cslib.Circuits.Boolean PairwiseIndependentHash

theorem indicator_synthesis {n : ℕ} (s : Finset (BitString n)) :
    Synthesis interpretation (inputs n) {fun x => decide (x ∈ s)}
      (s.card * (2 * n + 2) + 1) := by
  classical
  have h := Synthesis.exists_mem s (fun a x => decide (x = a))
    (fun _ => 2 * n + 1) (fun a _ => synthesis_minterm id a)
  apply h.mono Set.Subset.rfl ?_ (by simp [Nat.add_assoc])
  rintro f rfl
  simp only [Set.mem_singleton_iff]
  funext x
  simp

theorem exists_sparse_filter {n k l : ℕ} (A B : Finset (BitString n))
    (disjoint : Disjoint A B) (K : ℕ) (positive : 0 < K) :
    ∃ f : BitString n → Bool,
      (∀ x ∈ B, f x = true) ∧
      (A.filter fun x => f x = true).card * 2 ^ (k + l) ≤ A.card * B.card ∧
      Synthesis interpretation (inputs n) {f}
        (hashBudget n (k + l) + sparseTableBudget k l K B.card) := by
  classical
  let hash := affine n (k + l)
  obtain ⟨seed, hseed⟩ := exists_few_hashCollisions hash (A ×ˢ B) (by
    intro xy hxy equal
    have mem := Finset.mem_product.mp hxy
    exact Finset.disjoint_left.mp disjoint mem.1 (equal ▸ mem.2))
  let image := B.image (hash.eval seed)
  let f (x : BitString n) := decide (hash.eval seed x ∈ image)
  obtain ⟨hc, hhc, hcost⟩ := exists_hashCircuit n (k + l) seed
  obtain ⟨tc, htc, tcost⟩ := exists_sparseTable image K positive
  have compute : (tc.comp hc).Computes interpretation (fun x _ => f x) := by
    intro x
    rw [Cslib.Circuits.Circuit.eval_comp, hhc x, htc (affineEval seed x)]
    simp only [f, hash, affine_eval]
  have size : (tc.comp hc).size ≤ hashBudget n (k + l) + sparseTableBudget k l K B.card := by
    have mono : sparseTableBudget k l K image.card ≤ sparseTableBudget k l K B.card := by
      unfold sparseTableBudget
      have : image.card / K ≤ B.card / K := Nat.div_le_div_right Finset.card_image_le
      omega
    simpa only [Cslib.Circuits.Circuit.size_comp] using Nat.add_le_add hcost (tcost.trans mono)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro x hx
    exact decide_eq_true (Finset.mem_image_of_mem _ hx)
  · have subset : A.filter (fun x => f x = true) ⊆
        (hashCollisions hash (A ×ˢ B) seed).image Prod.fst := by
      intro x hx
      have info := Finset.mem_filter.mp hx
      have hin : hash.eval seed x ∈ image := of_decide_eq_true info.2
      obtain ⟨y, hy, equal⟩ := Finset.mem_image.mp hin
      exact Finset.mem_image.mpr ⟨(x, y),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨info.1, hy⟩, equal.symm⟩, rfl⟩
    have count := (Finset.card_le_card subset).trans Finset.card_image_le
    exact (Nat.mul_le_mul_right _ count).trans (by simpa using hseed)
  · have h := compute.synthesis
    have single : Set.range (fun _ : Fin 1 => f) = {f} := by simp
    rw [single] at h
    exact h.mono Set.Subset.rfl Set.Subset.rfl size

theorem exists_repeated_filter {n k l p a : ℕ} (A B : Finset (BitString n))
    (disjoint : Disjoint A B) (small : B.card ≤ 2 ^ p) (width : k + l = p + a)
    (K : ℕ) (positive : 0 < K) (steps : ℕ) :
    ∃ f : BitString n → Bool,
      (∀ x ∈ B, f x = true) ∧
      (A.filter fun x => f x = true).card * (2 ^ a) ^ steps ≤ A.card ∧
      Synthesis interpretation (inputs n) {f}
        (steps * (hashBudget n (k + l) + sparseTableBudget k l K (2 ^ p) + 1) + 1) := by
  classical
  induction steps generalizing A with
  | zero => exact ⟨fun _ => true, by simp, by simp, by simpa using Synthesis.const true⟩
  | succ steps ih =>
    obtain ⟨filter, keep, shrink, build⟩ := exists_sparse_filter (k := k) (l := l) A B
      disjoint K positive
    let rest := A.filter fun x => filter x = true
    have disjoint' : Disjoint rest B :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _) disjoint
    obtain ⟨next, keepNext, shrinkNext, buildNext⟩ := ih rest disjoint'
    have shrink' : rest.card * 2 ^ a ≤ A.card := by
      have h := shrink.trans (Nat.mul_le_mul_left A.card small)
      rw [width, pow_add] at h
      apply Nat.le_of_mul_le_mul_left (c := 2 ^ p) ?_ (by positivity)
      simpa only [rest, Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using h
    have equal : A.filter (fun x => (filter x && next x) = true) =
        rest.filter (fun x => next x = true) := by ext x; simp [rest, and_assoc]
    refine ⟨fun x => filter x && next x, fun x hx => by simp [keep x hx, keepNext x hx], ?_, ?_⟩
    · rw [equal, pow_succ]
      calc
        _ = ((rest.filter fun x => next x = true).card * (2 ^ a) ^ steps) * 2 ^ a := by ring
        _ ≤ rest.card * 2 ^ a := Nat.mul_le_mul_right _ shrinkNext
        _ ≤ A.card := shrink'
    · have cost : sparseTableBudget k l K B.card ≤ sparseTableBudget k l K (2 ^ p) := by
        unfold sparseTableBudget
        have := Nat.div_le_div_right small (c := K)
        omega
      exact (build.and buildNext).mono Set.Subset.rfl Set.Subset.rfl (by nlinarith)

end Complexity.CircuitSparseSynthesis.Internal
