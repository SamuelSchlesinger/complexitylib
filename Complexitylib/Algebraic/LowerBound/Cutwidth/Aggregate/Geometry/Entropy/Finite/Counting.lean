/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite.Uniform

/-!
# Counting events that fix selected independent coordinates

Forcing `k` distinct Boolean coordinates leaves at most a `2⁻ᵏ` fraction of the
cube. The proof injects the event into the unused coordinate assignments.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped Classical

/-- An event fixing every selected coordinate occupies at most one corresponding cube fibre. -/
theorem pow_card_mul_card_le_of_forces_coordinates {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (e : I ↪ V) (bits : I → Bool) (P : (V → Bool) → Prop) [DecidablePred P]
    (forced : ∀ x, P x → x ∘ e = bits) :
    2 ^ Fintype.card I * Fintype.card {x // P x} ≤ 2 ^ Fintype.card V := by
  let rest : {x // P x} → ({v // v ∉ Set.range e} → Bool) :=
    fun x => (coordinateSplit e x.val).2
  have injective : Function.Injective rest := by
    intro x y same
    apply Subtype.ext
    apply (coordinateSplit e).injective
    apply Prod.ext
    · rw [coordinateSplit_fst, coordinateSplit_fst, forced x.val x.property,
        forced y.val y.property]
    · exact same
  have small := Fintype.card_le_of_injective rest injective
  have size := Fintype.card_congr (coordinateSplit e)
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool] at size
  calc
    2 ^ Fintype.card I * Fintype.card {x // P x} ≤
        2 ^ Fintype.card I * Fintype.card ({v // v ∉ Set.range e} → Bool) :=
      Nat.mul_le_mul_left _ small
    _ = 2 ^ Fintype.card V := by simpa only [Fintype.card_fun, Fintype.card_bool] using size.symm

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
