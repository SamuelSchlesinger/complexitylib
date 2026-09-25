/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.MassProduction.BinaryEncoding
public import Complexitylib.Algebraic.MassProduction.SortingNetwork

/-!
# Power-of-two candidate/request/slot layouts

Independent powers of two flatten into one exact sorting-network capacity.
Candidate identifiers are hardwired binary ranks and therefore injective.
-/

@[expose] public section

namespace Algebraic.MassProduction.Nonuniform.PowerLayout

open Sorting

/-- A row-major triple of power-of-two indices is one sorting-network record. -/
def points (menuDepth requestDepth slotDepth : Nat) :
    (Fin (networkRecords menuDepth) × Fin (networkRecords requestDepth) × Fin (2 ^ slotDepth)) ≃
      Fin (networkRecords (menuDepth + requestDepth + slotDepth)) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by simp only [networkRecords_eq_two_pow, pow_add, Nat.mul_assoc]))

/-- Fixed candidate identifiers fit in exactly the menu sorting depth. -/
noncomputable def codes (menuDepth : Nat) (candidate : Fin (networkRecords menuDepth)) : Fin menuDepth → Bool :=
  lexBitVectorAt (Fin.cast (networkRecords_eq_two_pow menuDepth) candidate)

/-- The fixed candidate identifiers are distinct. -/
theorem codes_injective (menuDepth : Nat) : Function.Injective (codes menuDepth) := by
  intro left right equal
  have sameCast := lexBitVectorAt_injective equal
  exact (Fin.cast_injective _ sameCast)

end Algebraic.MassProduction.Nonuniform.PowerLayout
