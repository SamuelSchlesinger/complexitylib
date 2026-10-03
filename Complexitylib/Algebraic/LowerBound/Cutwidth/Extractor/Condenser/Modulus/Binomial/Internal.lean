/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension

/-!
# Binomial irreducibility and finite-field noncubes

Mathlib's odd-prime-power binomial irreducibility theorem gives the modulus
family. Cauchy's theorem gives a nontrivial cube root of unity when three
divides the unit-group order. Cubing is then noninjective and hence
nonsurjective on the finite field.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem binomialModulus_monic {F : Type*} [Ring F] (a : F) (s : Nat) :
    (binomialModulus a s).Monic :=
  Polynomial.monic_X_pow_sub_C a (pow_ne_zero _ (by decide))

theorem binomialModulus_natDegree {F : Type*} [Ring F] [Nontrivial F] (a : F) (s : Nat) :
    (binomialModulus a s).natDegree = 3 ^ s :=
  Polynomial.natDegree_X_pow_sub_C

theorem binomialModulus_irreducible {F : Type*} [Field F] (a : F) (s : Nat)
    (noncube : ∀ b : F, b ^ 3 ≠ a) : Irreducible (binomialModulus a s) :=
  X_pow_sub_C_irreducible_of_prime_pow_of_ne_two (by decide) (by decide) s noncube

theorem exists_noncube {F : Type*} [Field F] [Fintype F]
    (divisible : 3 ∣ Fintype.card F - 1) : ∃ a : F, ∀ b : F, b ^ 3 ≠ a := by
  classical
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have units : 3 ∣ Fintype.card Fˣ := by simpa only [Fintype.card_units] using divisible
  obtain ⟨u, order⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) 3 units
  have cube : (u : F) ^ 3 = (1 : F) ^ 3 := by
    have unitCube : u ^ 3 = 1 := order ▸ pow_orderOf_eq_one u
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow]
      using congrArg Units.val unitCube
  by_contra none
  push Not at none
  have injective : Function.Injective (fun b : F => b ^ 3) :=
    Finite.injective_iff_surjective.mpr none
  have equal : u = 1 := Units.ext (injective cube)
  simp [equal] at order

theorem three_dvd_card_sub_one_of_even_exponent {F : Type*} [Fintype F] {b : Nat}
    (cardinality : Fintype.card F = 2 ^ b) (even : Even b) :
    3 ∣ Fintype.card F - 1 := by
  rw [cardinality]
  simpa using Nat.pow_sub_one_dvd_pow_sub_one (x := 2) even.two_dvd

theorem binomialModulus_natDegree_clog_bounds {F : Type*} [Ring F] [Nontrivial F]
    (a : F) {n : Nat} (positive : 0 < n) :
    n ≤ (binomialModulus a (Nat.clog 3 n)).natDegree ∧
      (binomialModulus a (Nat.clog 3 n)).natDegree < 3 * n := by
  rw [binomialModulus_natDegree]
  refine ⟨Nat.le_pow_clog (by decide) n, ?_⟩
  by_cases small : n ≤ 1
  · have equal : n = 1 := by lia
    simp [equal]
  · have bigger : 1 < n := by lia
    have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 3) bigger
    have exponent : (Nat.clog 3 n).pred + 1 = Nat.clog 3 n :=
      Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide) bigger)
    calc
      3 ^ Nat.clog 3 n = 3 ^ (Nat.clog 3 n).pred * 3 := by
        rw [← pow_succ, exponent]
      _ < 3 * n := by nlinarith

end Algebraic.Cutwidth.Extractor.Internal
