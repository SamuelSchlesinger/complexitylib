/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis.Internal.Filter

/-!
# Exact synthesis after repeated filtering

Intersect the hash filters and remove their residual false positives by
minterms. The remaining estimate has explicit, finite parameters.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis.Internal

open Cslib.Circuits Cslib.Circuits.Boolean

/-- Repeated hash filters, conjunctions, and minterms removing their residual false positives. -/
def sparseFiniteBudget (n k l K p a steps : ℕ) : ℕ :=
  steps * (hashBudget n (k + l) + sparseTableBudget k l K (2 ^ p) + 1) +
    (2 ^ n / (2 ^ a) ^ steps) * (2 * n + 2) + 4

theorem sparseFinite_synthesis {n k l p a : ℕ} (B : Finset (BitString n))
    (small : B.card ≤ 2 ^ p) (width : k + l = p + a)
    (K : ℕ) (positive : 0 < K) (steps : ℕ) :
    Synthesis interpretation (inputs n) {fun x => decide (x ∈ B)}
      (sparseFiniteBudget n k l K p a steps) := by
  classical
  let A := Finset.univ \ B
  obtain ⟨f, keep, shrink, build⟩ := exists_repeated_filter (k := k) (l := l) A B
    (Finset.disjoint_left.mpr fun _ hx hy => (Finset.mem_sdiff.mp hx).2 hy)
    small width K positive steps
  let residual := A.filter fun x => f x = true
  have residualSize : residual.card ≤ 2 ^ n / (2 ^ a) ^ steps := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    exact shrink.trans (card_le_pow A)
  have correction := (indicator_synthesis residual).not
  have result := build.and correction
  apply result.mono Set.Subset.rfl ?_ ?_
  · rintro q rfl
    simp only [Set.mem_singleton_iff]
    funext x
    by_cases hx : x ∈ B
    · simp [hx, residual, A, keep x hx]
    · cases hf : f x <;> simp [hx, residual, A, hf]
  · unfold sparseFiniteBudget
    have := Nat.mul_le_mul_right (2 * n + 2) residualSize
    omega

theorem exists_sparseFinite {n k l p a : ℕ} (B : Finset (BitString n))
    (small : B.card ≤ 2 ^ p) (width : k + l = p + a)
    (K : ℕ) (positive : 0 < K) (steps : ℕ) :
    ∃ c : Cslib.Circuits.Circuit signature n 1,
      c.Computes interpretation (fun x _ => decide (x ∈ B)) ∧
        c.size ≤ sparseFiniteBudget n k l K p a steps :=
  (sparseFinite_synthesis B small width K positive steps).exists_circuit

end Complexity.CircuitSparseSynthesis.Internal
