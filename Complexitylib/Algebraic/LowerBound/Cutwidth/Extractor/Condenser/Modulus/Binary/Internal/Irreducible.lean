/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension

/-!
# Irreducibility by the four-element field and binomial composition

A simple root of the base quadratic generates a field of cardinality four.
Its generator is neither zero nor one, whereas every nonzero cube is one.
Kummer irreducibility and Mathlib's irreducible-composition theorem then give
the entire binary trinomial family.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem simpleRoot_noncube {L : Type*} [Field L] [Algebra (ZMod 2) L]
    (x : L) (minimal : minpoly (ZMod 2) x = binaryModulus 0) :
    ∀ b : IntermediateField.adjoin (ZMod 2) {x},
      b ^ 3 ≠ IntermediateField.AdjoinSimple.gen (ZMod 2) x := by
  have integral : IsIntegral (ZMod 2) x := minpoly.ne_zero_iff.mp (by
    rw [minimal]
    exact (binaryModulus_monic 0).ne_zero)
  let A := IntermediateField.adjoin (ZMod 2) {x}
  let : Module.Finite (ZMod 2) A := IntermediateField.adjoin.finiteDimensional integral
  have cardinality : Nat.card A = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      IntermediateField.adjoin.finrank integral, minimal, binaryModulus_natDegree]
    norm_num
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [cardinality]; decide)
  let : Fintype A := Fintype.ofFinite A
  have degree : (minpoly (ZMod 2)
      (IntermediateField.AdjoinSimple.gen (ZMod 2) x)).natDegree = 2 := by
    rw [IntermediateField.minpoly_gen, minimal, binaryModulus_natDegree]
    norm_num
  have nonzero : IntermediateField.AdjoinSimple.gen (ZMod 2) x ≠ 0 := by
    intro equal
    rw [equal, minpoly.zero, Polynomial.natDegree_X] at degree
    contradiction
  have nonone : IntermediateField.AdjoinSimple.gen (ZMod 2) x ≠ 1 := by
    intro equal
    rw [equal, minpoly.one, ← Polynomial.C_1, Polynomial.natDegree_X_sub_C] at degree
    contradiction
  intro b cube
  have bNonzero : b ≠ 0 := by
    intro equal
    apply nonzero
    rw [← cube, equal, zero_pow (by decide)]
  have cubeOne : b ^ 3 = 1 := by
    have bound := FiniteField.pow_card_sub_one_eq_one b bNonzero
    rw [← Nat.card_eq_fintype_card] at bound
    change b ^ (Nat.card A - 1) = 1 at bound
    simpa only [cardinality] using bound
  exact nonone (cube.symm.trans cubeOne)

theorem binaryModulus_irreducible (s : Nat) : Irreducible (binaryModulus s) := by
  have composition :
      (binaryModulus 0).comp (Polynomial.X ^ (3 ^ s)) = binaryModulus s := by
    simp only [binaryModulus, pow_zero, mul_one, pow_one, Polynomial.add_comp,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.one_comp]
    rw [← pow_mul, Nat.mul_comm]
  rw [← composition]
  apply Polynomial.irreducible_comp (binaryModulus_monic 0)
    (Polynomial.monic_X_pow _) binaryModulus_zero_irreducible
  intro L _ _ x minimal
  simpa only [Polynomial.map_pow, Polynomial.map_X, binomialModulus] using
    binomialModulus_irreducible (IntermediateField.AdjoinSimple.gen (ZMod 2) x) s
      (simpleRoot_noncube x minimal)

end Algebraic.Cutwidth.Extractor.Internal
