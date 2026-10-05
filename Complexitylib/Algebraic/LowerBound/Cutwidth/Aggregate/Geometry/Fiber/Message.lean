/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Fiber.Defs

/-!
# Removing frozen coordinates from a complete message

On the majority event, the designated message bits are all false. The remaining
message therefore retains the full key's fiber bound on that event. No independence
of the remaining messages is assumed.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber

open scoped Classical

/-- On a restricted event, a key determining the original key preserves its fiber bound. -/
theorem card_fiber_le_of_refines_on {X Y Z : Type*} [Fintype X]
    (event : Finset X) (key : X → Y) (residual : X → Z)
    (refines : ∀ x ∈ event, ∀ y ∈ event, residual x = residual y → key x = key y)
    {K : ℕ} (fibers : ∀ y, (Finset.univ.filter fun x => key x = y).card ≤ K)
    (z : Z) : (event.filter fun x => residual x = z).card ≤ K := by
  by_cases nonempty : (event.filter fun x => residual x = z).Nonempty
  · obtain ⟨a, ha⟩ := nonempty
    have subset : (event.filter fun x => residual x = z) ⊆
        Finset.univ.filter fun x => key x = key a := by
      intro x hx
      obtain ⟨xe, xz⟩ := Finset.mem_filter.mp hx
      obtain ⟨ae, az⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, refines x xe a ae (xz.trans az.symm)⟩
    exact (Finset.card_le_card subset).trans (fibers (key a))
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [empty]

/-- A rare selected message implies its chosen two-coordinate conjunction. -/
theorem key_eq_false_of_majority {I V : Type*} [Fintype V]
    (key : (V → Bool) → I → Bool) (S : Finset I) (edge : S → Entropy.SignedEdge V)
    (forced : ∀ x i, key x i.val = true → (edge i).eval x = true)
    {x : V → Bool} (hx : x ∈ majorityInputs edge) (i : S) : key x i.val = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have majority := (Finset.mem_filter.mp hx).2 i
  exact Bool.noConfusion ((forced x i h).symm.trans majority)

/-- Deleting the frozen coordinates preserves the fiber bound on the majority event. -/
theorem card_residual_fiber_le {I V : Type*} [Fintype V]
    (key : (V → Bool) → I → Bool) (S : Finset I) (edge : S → Entropy.SignedEdge V)
    (forced : ∀ x i, key x i.val = true → (edge i).eval x = true)
    {K : ℕ} (fibers : ∀ y, (Finset.univ.filter fun x => key x = y).card ≤ K)
    (y : {i : I // i ∉ S} → Bool) :
    ((majorityInputs edge).filter fun x => (fun i : {i : I // i ∉ S} => key x i.val) = y).card
      ≤ K := by
  let event := (majorityInputs edge).filter fun x =>
    (fun i : {i : I // i ∉ S} => key x i.val) = y
  change event.card ≤ K
  by_cases nonempty : event.Nonempty
  · obtain ⟨a, ha⟩ := nonempty
    have subset : event ⊆ Finset.univ.filter fun x => key x = key a := by
      intro x hx
      obtain ⟨xa, xy⟩ := Finset.mem_filter.mp hx
      obtain ⟨aa, ay⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      funext i
      by_cases hi : i ∈ S
      · rw [key_eq_false_of_majority key S edge forced xa ⟨i, hi⟩,
          key_eq_false_of_majority key S edge forced aa ⟨i, hi⟩]
      · exact congrFun (xy.trans ay.symm) ⟨i, hi⟩
    exact (Finset.card_le_card subset).trans (fibers (key a))
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    simp [empty]

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber
