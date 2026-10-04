/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Affine.Basic
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Polarity

/-!
# Affine flats are XOR cosets

Translating a ternary-XOR-closed nonempty set by any of its points gives an
XOR-closed set of the same size. The checked sumset-disperser obstruction therefore
applies directly to our original Boolean-coordinate affine flats.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth
open scoped Classical

variable {n : Nat}

/-- Boolean translation is its own inverse. -/
private theorem xorInput_left_left (a x : Fin n → Bool) : xorInput a (xorInput a x) = x := by
  funext i
  simp only [xorInput]
  cases a i <;> cases x i <;> rfl

/-- A nonempty ternary-XOR-closed flat is a translate of an XOR-closed set. -/
theorem AffineFlat.exists_xorCoset (S : AffineFlat n) :
    ∃ (a : Fin n → Bool) (V : Finset (Fin n → Bool)),
      (∀ x ∈ V, ∀ y ∈ V, xorInput x y ∈ V) ∧
      V.image (xorInput a) = S.carrier ∧ V.card = S.carrier.card := by
  classical
  obtain ⟨a, ha⟩ := S.nonempty
  let V := S.carrier.image (xorInput a)
  have inj : Function.Injective (xorInput a) := by
    intro x y same
    have := congrArg (xorInput a) same
    simpa only [xorInput_left_left] using this
  refine ⟨a, V, ?_, ?_, Finset.card_image_of_injective _ inj⟩
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    refine Finset.mem_image.mpr ⟨xorThree u a v, S.closed u hu a ha v hv, ?_⟩
    funext i
    simp only [xorInput, xorThree]
    cases u i <;> cases a i <;> cases v i <;> rfl
  · simp only [V, Finset.image_image, Function.comp_def, xorInput_left_left]
    exact Finset.image_id'

/-- A monochromatic affine flat is smaller than the sumset-disperser threshold. -/
theorem AffineFlat.card_lt_of_constant (S : AffineFlat n) {f : Cslib.BooleanFunction n}
    {K : Nat} (disperse : FlatSumsetDisperser f K) (mono : ConstantOn S f) :
    S.carrier.card < K := by
  obtain ⟨a, V, closed, image, card⟩ := S.exists_xorCoset
  obtain ⟨b, hb⟩ := mono
  rw [← card]
  apply disperse.card_lt_of_monochromatic_coset V closed a b
  intro x hx
  apply hb
  rw [← image]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

end Algebraic.Aggregate.Geometry
