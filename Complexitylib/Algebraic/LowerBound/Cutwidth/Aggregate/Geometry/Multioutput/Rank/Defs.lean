/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Independent nonlinear output components

Boolean functions are viewed as vectors over the two-element field. Affine primary
functions form a submodule; independence modulo this submodule records that no
nonzero linear combination of output coordinates is affine in the original inputs.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

/-- A Boolean value in the two-element field. -/
def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The original input bits in prime-field coordinates. -/
def bitVector {n : ℕ} (x : Fin n → Bool) : Fin n → ZMod 2 := fun i => bitValue (x i)

/-- The submodule of affine functions of the original input coordinates. -/
def affineFunctions (n : ℕ) : Submodule (ZMod 2) ((Fin n → Bool) → ZMod 2) where
  carrier := {f | ∃ (b : ZMod 2) (L : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2),
    f = fun x => b + L (bitVector x)}
  zero_mem' := ⟨0, 0, by ext; simp⟩
  add_mem' := by
    rintro f g ⟨a, L, rfl⟩ ⟨b, M, rfl⟩
    refine ⟨a + b, L + M, ?_⟩
    ext x
    simp only [Pi.add_apply, LinearMap.add_apply]
    exact add_add_add_comm _ _ _ _
  smul_mem' := by
    rintro a f ⟨b, L, rfl⟩
    refine ⟨a * b, a • L, ?_⟩
    ext x
    simp [mul_add]

/-- Every nonzero linear combination of output bits is nonaffine in the primary bits. -/
def NonaffineComponents {n m : ℕ} (F : (Fin n → Bool) → (Fin m → Bool)) : Prop :=
  ∀ w : Fin m → ZMod 2,
    (fun x => ∑ i, w i * bitValue (F x i)) ∈ affineFunctions n → w = 0

/-- Number of conjunction operations, including signed and constant conjunctions. -/
def conjunctionCount {n g : ℕ} (p : Program signature n g) : ℕ :=
  (Finset.univ.filter fun gate => (p.lines gate).op.isConjunction = true).card

end Algebraic.Aggregate.Geometry
