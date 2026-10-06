/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Multioutput.Rank.Defs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

/-!
# The direction subspace of an affine flat

In prime-field coordinates, every affine flat of the Boolean cube is a translate
`a + U` of a subspace `U` with exactly as many points as the flat. This turns the
size of a flat into the dimension of its direction space.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth

variable {N : ℕ}

/-- Read a prime-field vector as Boolean coordinates. -/
def boolVector (v : Fin N → ZMod 2) : Fin N → Bool := fun i => decide (v i = 1)

private theorem bitValue_decide : ∀ t : ZMod 2, bitValue (decide (t = 1)) = t := by decide

private theorem decide_bitValue : ∀ b : Bool, decide (bitValue b = 1) = b := by decide

/-- Boolean coordinates of a prime-field vector recover that vector. -/
@[simp] theorem bitVector_boolVector (v : Fin N → ZMod 2) : bitVector (boolVector v) = v :=
  funext fun i => bitValue_decide (v i)

/-- Prime-field coordinates of a Boolean point recover that point. -/
@[simp] theorem boolVector_bitVector (x : Fin N → Bool) : boolVector (bitVector x) = x :=
  funext fun i => decide_bitValue (x i)

/-- Prime-field coordinates convert ternary XOR into addition. -/
theorem bitVector_xorThree (x y z : Fin N → Bool) :
    bitVector (xorThree x y z) = bitVector x + bitVector y + bitVector z := by
  funext i
  simp only [bitVector, xorThree, xorInput, Pi.add_apply]
  cases x i <;> cases y i <;> cases z i <;> decide

private theorem add_self_vector (v : Fin N → ZMod 2) : v + v = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (v i)

private theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- Every affine flat is a translate of a prime-field subspace with as many points. -/
theorem AffineFlat.exists_direction (S : AffineFlat N) :
    ∃ (a : Fin N → ZMod 2) (U : Submodule (ZMod 2) (Fin N → ZMod 2)),
      2 ^ Module.finrank (ZMod 2) U = S.carrier.card ∧
      ∀ u ∈ U, ∃ x ∈ S.carrier, bitVector x = a + u := by
  classical
  obtain ⟨x₀, hx₀⟩ := S.nonempty
  let a := bitVector x₀
  have shift (u w : Fin N → ZMod 2) : a + u + a + (a + w) = a + (u + w) := by
    have := add_self_vector a
    calc
      a + u + a + (a + w) = (a + a) + (a + (u + w)) := by abel
      _ = a + (u + w) := by rw [this, zero_add]
  let U : Submodule (ZMod 2) (Fin N → ZMod 2) :=
    { carrier := {d | boolVector (a + d) ∈ S.carrier}
      zero_mem' := by
        change boolVector (a + 0) ∈ S.carrier
        simpa [a] using hx₀
      add_mem' := by
        intro u w hu hw
        change boolVector (a + (u + w)) ∈ S.carrier
        have closed := S.closed _ hu x₀ hx₀ _ hw
        have same : xorThree (boolVector (a + u)) x₀ (boolVector (a + w)) =
            boolVector (a + (u + w)) := by
          rw [← boolVector_bitVector (xorThree _ _ _), bitVector_xorThree,
            bitVector_boolVector, bitVector_boolVector, shift]
        rwa [same] at closed
      smul_mem' := by
        intro c d hd
        change boolVector (a + c • d) ∈ S.carrier
        rcases zmod_two_cases c with rfl | rfl
        · simpa [a] using hx₀
        · simpa using hd }
  have back (x : Fin N → Bool) : a + (bitVector x + a) = bitVector x := by
    rw [add_comm (bitVector x), ← add_assoc, add_self_vector, zero_add]
  let points : U ≃ S.carrier :=
    { toFun := fun d => ⟨boolVector (a + d), d.2⟩
      invFun := fun x => ⟨bitVector x.1 + a, by
        change boolVector (a + (bitVector x.1 + a)) ∈ S.carrier
        rw [back, boolVector_bitVector]
        exact x.2⟩
      left_inv := by
        rintro ⟨d, hd⟩
        apply Subtype.ext
        change bitVector (boolVector (a + d)) + a = d
        rw [bitVector_boolVector, add_comm a d, add_assoc, add_self_vector, add_zero]
      right_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change boolVector (a + (bitVector x + a)) = x
        rw [back, boolVector_bitVector] }
  refine ⟨a, U, ?_, ?_⟩
  · rw [← Fintype.card_coe S.carrier, ← Nat.card_eq_fintype_card, ← Nat.card_congr points,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  · intro u hu
    exact ⟨boolVector (a + u), hu, bitVector_boolVector _⟩

end Algebraic.Aggregate.Geometry
