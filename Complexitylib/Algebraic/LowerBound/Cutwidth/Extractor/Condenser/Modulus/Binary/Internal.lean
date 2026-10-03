/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Defs
public import Mathlib.RingTheory.AdjoinRoot
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Internal.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Internal.Irreducible
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.Tactic.Ring

/-!
# Binary quotient size and the noncube root

The monic power basis gives the quotient cardinality. Cubing in the defining
polynomial passes from `M_s` to `M_(s+1)`. A cube root of the quotient root
would therefore have minimal polynomial degree larger than the quotient's
dimension, contradicting the finite-module degree bound.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem card_adjoinRoot_binaryModulus (s : Nat) :
    Nat.card (AdjoinRoot (binaryModulus s)) = 2 ^ (2 * 3 ^ s) := by
  let pb := AdjoinRoot.powerBasis (binaryModulus_monic s).ne_zero
  let : Module.Finite (ZMod 2) (AdjoinRoot (binaryModulus s)) := pb.finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    PowerBasis.finrank pb, AdjoinRoot.powerBasis_dim, binaryModulus_natDegree]

theorem binaryModulus_comp_cube (s : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ 3) = binaryModulus (s + 1) := by
  simp only [binaryModulus, Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp, ← pow_mul]
  rw [Nat.pow_succ]
  congr 2 <;> congr 1 <;> ring

theorem root_binaryModulus_noncube (s : Nat) :
    ∀ b : AdjoinRoot (binaryModulus s), b ^ 3 ≠ AdjoinRoot.root (binaryModulus s) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  let pb := AdjoinRoot.powerBasis (binaryModulus_monic s).ne_zero
  let : Module.Finite (ZMod 2) (AdjoinRoot (binaryModulus s)) := pb.finite
  intro b cube
  have annihilates : Polynomial.aeval b (binaryModulus (s + 1)) = 0 := by
    rw [← binaryModulus_comp_cube, Polynomial.aeval_comp]
    simp only [map_pow, Polynomial.aeval_X]
    rw [cube, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have minimal := minpoly.eq_of_irreducible_of_monic
    (binaryModulus_irreducible (s + 1)) annihilates (binaryModulus_monic (s + 1))
  have rank : Module.finrank (ZMod 2) (AdjoinRoot (binaryModulus s)) = 2 * 3 ^ s := by
    rw [PowerBasis.finrank pb, AdjoinRoot.powerBasis_dim, binaryModulus_natDegree]
  have bound := minpoly.natDegree_le (A := ZMod 2) b
  rw [← minimal, binaryModulus_natDegree, rank, Nat.pow_succ] at bound
  have positive : 0 < 3 ^ s := by positivity
  lia

end Algebraic.Cutwidth.Extractor.Internal
