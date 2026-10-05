/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.MultiOutput.TotallyRegular

/-!
# An explicit Cauchy family in characteristic zero

The natural nodes `0, ..., N-1` and `N, ..., 2N-1` are distinct in every
characteristic-zero field. Their Cauchy matrix is therefore totally regular.
The same rational entries give the family over the rationals, reals, and complexes.
-/

@[expose] public section

namespace Algebraic.Cutwidth.MultiOutput

/-- The rational-node Cauchy family, interpreted in any field. -/
def cauchyCharZero (F : Type*) [Field F] (N : ℕ) : Matrix (Fin N) (Fin N) F :=
  cauchy (fun i => ((i : ℕ) : F)) (fun j => ((N + j : ℕ) : F))

/-- Each coefficient is the reciprocal of the indicated nonzero integer difference. -/
theorem cauchyCharZero_apply (F : Type*) [Field F] (N : ℕ) (i j : Fin N) :
    cauchyCharZero F N i j = (((i : ℕ) : F) - ((N + j : ℕ) : F))⁻¹ := rfl

/-- All square minors of the natural-node Cauchy family are nonsingular. -/
theorem totallyRegular_cauchyCharZero (F : Type*) [Field F] [CharZero F] (N : ℕ) :
    TotallyRegular (cauchyCharZero F N) := by
  apply totallyRegular_cauchy
  · intro i j h
    exact Fin.ext (Nat.cast_injective h)
  · intro i j h
    exact Fin.ext (Nat.add_left_cancel (Nat.cast_injective h))
  · intro i j h
    have equality : (i : ℕ) = N + j := Nat.cast_injective h
    have := i.isLt
    lia

/-- The entries in every characteristic-zero field are the same explicit rational numbers. -/
theorem cauchyCharZero_eq_map_rat (F : Type*) [Field F] [CharZero F] (N : ℕ) :
    cauchyCharZero F N = (cauchyCharZero ℚ N).map (Rat.castHom F) := by
  ext i j
  simp [cauchyCharZero, cauchy]

end Algebraic.Cutwidth.MultiOutput
