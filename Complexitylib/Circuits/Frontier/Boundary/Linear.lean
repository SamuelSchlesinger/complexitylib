/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexitylib.Mathlib.SetNcard
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# Linear boundary states

For a split linear system `L x + R y = 0`, the extendable syndromes are precisely
`range L ∩ range R`. Two extendable left assignments have the same right completions
exactly when their syndromes agree. Thus this is an exact boundary code, not just an upper
bound obtained by counting its coordinates. Its dimension is the familiar matroid
connectivity expression; see Kashyap, *Matroid Pathwidth and Code Trellis Complexity*.
-/

@[expose] public section

namespace Complexity.Frontier.LinearBoundary

open Set Module

variable {F V Z W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup Z] [Module F Z] [AddCommGroup W] [Module F W]
  (L : V →ₗ[F] W) (R : Z →ₗ[F] W)

/-- Right completions of a left assignment in a split homogeneous linear system. -/
def completions (x : V) : Set Z := {y | L x + R y = 0}

theorem completions_nonempty_iff (x : V) :
    (completions L R x).Nonempty ↔ L x ∈ LinearMap.range R := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨-y, by simpa using (eq_neg_of_add_eq_zero_left hy).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨-y, by simp [completions, hy]⟩

/-- Distinct feasible syndromes have distinct completion sets. -/
theorem completions_eq_iff {x x' : V} (hx : (completions L R x).Nonempty) :
    completions L R x = completions L R x' ↔ L x = L x' := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hx
    have hy' : y ∈ completions L R x' := h ▸ hy
    exact add_right_cancel (hy.trans hy'.symm)
  · intro h
    ext y
    simp only [completions, mem_ofPred_eq, h]

/-- The feasible boundary code is the intersection of the two syndrome spaces. -/
theorem syndromes_eq :
    L '' {x | (completions L R x).Nonempty} =
      (↑(LinearMap.range L ⊓ LinearMap.range R) : Set W) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (completions_nonempty_iff L R x).mp hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, (completions_nonempty_iff L R x).mpr hx, rfl⟩

/-- The dimension of the boundary code is the connectivity of the two column spaces. -/
theorem finrank_states [FiniteDimensional F W] :
    finrank F (LinearMap.range L ⊓ LinearMap.range R : Submodule F W) =
      finrank F (LinearMap.range L) + finrank F (LinearMap.range R) -
        finrank F (LinearMap.range L ⊔ LinearMap.range R : Submodule F W) := by
  have H := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range L) (LinearMap.range R)
  lia

/-- Over a finite field the exact number of feasible syndromes is `q^λ`. The `Nat.card`
identity also makes sense over infinite fields; only the finite case is a counting bound. -/
theorem ncard_syndromes [FiniteDimensional F W] :
    (L '' {x | (completions L R x).Nonempty}).ncard =
      Nat.card F ^ (finrank F (LinearMap.range L) + finrank F (LinearMap.range R) -
        finrank F (LinearMap.range L ⊔ LinearMap.range R : Submodule F W)) := by
  rw [syndromes_eq, ← Nat.card_coe_set_eq]
  change Nat.card ↥(LinearMap.range L ⊓ LinearMap.range R) = _
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_states L R]

/-- This many states are necessary as well as sufficient: any exact classifier of right
completion sets must separate all feasible syndromes. -/
theorem ncard_syndromes_le_states [Finite V] {D : Type*} (code : V → D)
    (hcode : ∀ x, (completions L R x).Nonempty → ∀ x',
      (completions L R x').Nonempty → code x = code x' →
        completions L R x = completions L R x') :
    (L '' {x | (completions L R x).Nonempty}).ncard ≤
      (code '' {x | (completions L R x).Nonempty}).ncard :=
  ncard_image_le_ncard_image_of_determines (toFinite _) _ _ fun x hx x' hx' h =>
    (completions_eq_iff L R hx).mp (hcode x hx x' hx' h)

end Complexity.Frontier.LinearBoundary
