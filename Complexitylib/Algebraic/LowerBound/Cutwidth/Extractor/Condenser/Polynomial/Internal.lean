/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Polynomial.Defs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.CharP.Lemmas

/-!
# Modular iteration and source linearity of the polynomial condenser map

The induction reduces after each squaring, so the degree bound is independent
of the potentially exponential exponent. Characteristic two makes each
squaring additive; remaindering and evaluation preserve that additivity.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem modularFrobenius_eq_pow_modByMonic {F : Type*} [CommRing F]
    (E f : Polynomial F) (j : Nat) :
    modularFrobenius E j f = f ^ (2 ^ j) %ₘ E := by
  induction j with
  | zero => simp [modularFrobenius]
  | succ j ih =>
      rw [modularFrobenius, ih, show 2 ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
      simpa only [pow_two] using
        (Polynomial.mul_modByMonic (f ^ (2 ^ j)) (f ^ (2 ^ j)) E).symm

theorem modularFrobenius_degree_lt {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (j : Nat) :
    (modularFrobenius E j f).degree < E.degree := by
  rw [modularFrobenius_eq_pow_modByMonic]
  exact Polynomial.degree_modByMonic_lt _ monic

theorem modularFrobenius_zero {F : Type*} [CommRing F]
    (E : Polynomial F) (j : Nat) : modularFrobenius E j 0 = 0 := by
  induction j with
  | zero => simp [modularFrobenius]
  | succ j ih => simp [modularFrobenius, ih]

theorem modularFrobenius_add {F : Type*} [CommRing F] [CharP F 2]
    (E f g : Polynomial F) (j : Nat) :
    modularFrobenius E j (f + g) = modularFrobenius E j f + modularFrobenius E j g := by
  induction j with
  | zero => exact Polynomial.add_modByMonic f g
  | succ j ih =>
      simp only [modularFrobenius, ih, add_pow_char, Polynomial.add_modByMonic]

theorem polynomialCondenser_apply {F : Type*} [CommRing F]
    (E f : Polynomial F) (r m : Nat) (y : F) (i : Fin m) :
    polynomialCondenser E r m f y i = (f ^ ((2 ^ r) ^ i.val) %ₘ E).eval y := by
  simp only [polynomialCondenser, modularFrobenius_eq_pow_modByMonic, pow_mul]

theorem polynomialCondenser_zero_coordinate {F : Type*} [CommRing F] [Nontrivial F]
    (E f : Polynomial F) (monic : E.Monic) (source : f.degree < E.degree)
    (r m : Nat) (y : F) : polynomialCondenser E r (m + 1) f y 0 = f.eval y := by
  simp only [polynomialCondenser, Fin.val_zero, Nat.mul_zero, modularFrobenius]
  rw [(Polynomial.modByMonic_eq_self_iff monic).mpr source]

theorem polynomialCondenser_zero {F : Type*} [CommRing F]
    (E : Polynomial F) (r m : Nat) (y : F) : polynomialCondenser E r m 0 y = 0 := by
  funext i
  simp only [polynomialCondenser, modularFrobenius_zero, Polynomial.eval_zero, Pi.zero_apply]

theorem polynomialCondenser_add {F : Type*} [CommRing F] [CharP F 2]
    (E f g : Polynomial F) (r m : Nat) (y : F) :
    polynomialCondenser E r m (f + g) y =
      polynomialCondenser E r m f y + polynomialCondenser E r m g y := by
  funext i
  simp only [polynomialCondenser, modularFrobenius_add, Polynomial.eval_add, Pi.add_apply]

theorem polynomialCondenser_smul {F : Type*} [CommRing F] [CharP F 2]
    [Module (ZMod 2) F] (E f : Polynomial F) (r m : Nat) (y : F) (c : ZMod 2) :
    polynomialCondenser E r m (c • f) y = c • polynomialCondenser E r m f y := by
  let map : Polynomial F →+ (Fin m → F) :=
    { toFun := fun g => polynomialCondenser E r m g y
      map_zero' := polynomialCondenser_zero E r m y
      map_add' := fun g h => polynomialCondenser_add E g h r m y }
  exact ZMod.map_smul map c f

end Algebraic.Cutwidth.Extractor.Internal
