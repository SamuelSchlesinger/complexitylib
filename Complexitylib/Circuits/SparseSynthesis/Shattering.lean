/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Circuits.SparseSynthesis
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Interpolating arbitrary samples with small circuits

At `2 * p` input bits, every sample of at most `2 ^ p` points is shattered
by circuits of size at most `⌊(1 + ε) * 2 ^ p / p⌋`, for all sufficiently
large `p`. Labels are prescribed only on the sample. The circuit supports
form a set family in Mathlib's shattering and VC-dimension API.
-/

@[expose] public section

namespace Complexity.CircuitSparseSynthesis

open Cslib.Circuits Cslib.Circuits.Boolean Correction

/-- Supports of scalar Boolean functions computable with at most `budget` gates. -/
noncomputable def circuitSupports (n budget : ℕ) : Finset (Finset (Fin n → Bool)) := by
  classical
  exact Finset.univ.filter fun s =>
    complexity interpretation (indicator (n := n) (s : Set _)) ≤ budget

/-- Every labeling of a square-root-sized sample has a circuit of the partial-synthesis size. -/
theorem exists_interpolating_circuit (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ domain : Finset (Fin (2 * p) → Bool), domain.card ≤ 2 ^ p →
      ∀ labels : domain → Bool, ∃ c : Circuit signature (2 * p) 1,
        (c.size : ℝ) ≤ (1 + ε) * 2 ^ p / p ∧
          ∀ x : domain, c.eval interpretation x.1 0 = labels x := by
  classical
  obtain ⟨p₀, after⟩ := complexityOn_le ε positive
  refine ⟨p₀, fun p hp domain small labels => ?_⟩
  let f : (Fin (2 * p) → Bool) → Bool :=
    fun x => if hx : x ∈ domain then labels ⟨x, hx⟩ else false
  obtain ⟨c, correct, size⟩ := exists_computesOn_size_eq_complexityOn
    (I := interpretation) (S := (domain : Set _)) (f := fun x (_ : Fin 1) => f x)
  refine ⟨c, ?_, ?_⟩
  · rw [size]
    exact after p hp domain small f
  · intro x
    simpa [f, x.property] using congrFun (correct x.property) 0

/-- Every sample of the allowed size is shattered, with no geometric condition on its points. -/
theorem circuitSupports_shatters (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ domain : Finset (Fin (2 * p) → Bool), domain.card ≤ 2 ^ p →
      (circuitSupports (2 * p) ⌊(1 + ε) * 2 ^ p / p⌋₊).Shatters domain := by
  classical
  obtain ⟨p₀, after⟩ := exists_interpolating_circuit ε positive
  refine ⟨p₀, fun p hp domain small t subset => ?_⟩
  obtain ⟨c, size, correct⟩ := after p hp domain small (fun x => decide (x.1 ∈ t))
  let support := Finset.univ.filter fun x => c.eval interpretation x 0 = true
  have computes : c.Computes interpretation (indicator (n := 2 * p) (support : Set _)) := by
    intro x
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    apply Bool.eq_iff_iff.mpr
    simp [indicator, support]
  refine ⟨support, ?_, ?_⟩
  · simp only [circuitSupports, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (complexity_le_of_computes c computes).trans (Nat.le_floor size)
  · ext x
    by_cases hx : x ∈ domain
    · have h := correct ⟨x, hx⟩
      simp [support, hx, h]
    · have ht : x ∉ t := fun h => hx (subset h)
      simp [hx, ht]

/-- At this gate budget the circuit class has VC dimension at least `2 ^ p`. -/
theorem le_vcDim_circuitSupports (ε : ℝ) (positive : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀,
      2 ^ p ≤ (circuitSupports (2 * p) ⌊(1 + ε) * 2 ^ p / p⌋₊).vcDim := by
  classical
  obtain ⟨p₀, after⟩ := circuitSupports_shatters ε positive
  refine ⟨p₀, fun p hp => ?_⟩
  have available : 2 ^ p ≤ (Finset.univ : Finset (Fin (2 * p) → Bool)).card := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : p ≤ 2 * p)
  obtain ⟨domain, _, card⟩ := Finset.exists_subset_card_eq available
  simpa [card] using (after p hp domain card.le).card_le_vcDim

end Complexity.CircuitSparseSynthesis
