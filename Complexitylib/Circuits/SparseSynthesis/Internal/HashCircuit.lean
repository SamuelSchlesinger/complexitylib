/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Classes.Randomized.Hashing.Affine
public import Cslib.Computability.Circuit.Boolean.Complexity
import Mathlib.Tactic

/-!
# De Morgan circuits for affine hashes

Fixed affine maps over the Boolean ring have polynomial circuit size. The
four-gate XOR implementation is shared with the circuit synthesis API.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib.Circuits Cslib.Circuits.Boolean PairwiseIndependentHash
open scoped BigOperators

/-- Gate budget for `m` affine forms on `n` inputs, using four-gate XORs. -/
def hashBudget (n m : ℕ) : ℕ := m * (5 * (n + 1) + 1)

theorem exists_hashCircuit (n m : ℕ) (seed : BitString (affineSeedWidth n m)) :
    ∃ c : Cslib.Circuits.Circuit signature n m,
      c.Computes interpretation (affineEval seed) ∧ c.size ≤ hashBudget n m := by
  have hrow (row : Fin m) : Synthesis interpretation (inputs n)
      {fun x => affineEval seed x row} (5 * (n + 1) + 1) := by
    have term (i : Fin (n + 1)) : Synthesis interpretation (inputs n)
        {fun x => affineRows seed row i * affineAugment x i} 1 := by
      cases hc : affineRows seed row i with
      | false => simpa only [hc, Bool.mul_eq_and, Bool.false_and] using
          (Synthesis.const (n := n) (s := inputs n) false)
      | true =>
        simp only [Bool.mul_eq_and, Bool.true_and]
        induction i using Fin.lastCases with
        | last => simpa [affineAugment] using (Synthesis.const (n := n) (s := inputs n) true)
        | cast i =>
            simpa [affineAugment] using
              (Synthesis.of_mem (I := interpretation) (s := inputs n) ⟨i, rfl⟩).mono
                Set.Subset.rfl Set.Subset.rfl (by omega : 0 ≤ 1)
    have h := Synthesis.finset_fold (fun a b : Bool => a + b) 4
      (fun _ _ => Synthesis.xor_of_mem (by simp) (by simp)) Finset.univ
      (Synthesis.const (n := n) (s := inputs n) false) (fun i _ => term i)
    change Synthesis interpretation (inputs n)
      {fun x => ∑ i : Fin (n + 1), affineRows seed row i * affineAugment x i}
      (5 * (n + 1) + 1)
    apply h.mono Set.Subset.rfl ?_ (by simp [Nat.mul_comm])
    rintro f rfl
    simp only [Set.mem_singleton_iff]
    funext x
    exact Finset.sum_eq_fold _ _
  simpa [hashBudget] using
    (Synthesis.family (fun row x => affineEval seed x row)
      (fun _ => 5 * (n + 1) + 1) hrow).exists_circuit_outputs

end Complexity.CircuitSparseSynthesis.Internal
