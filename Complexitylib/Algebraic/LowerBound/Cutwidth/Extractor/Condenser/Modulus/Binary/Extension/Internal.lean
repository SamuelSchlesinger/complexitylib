/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binomial
import Mathlib.Tactic.Ring

/-!
# Flattening a binomial tower into one binary quotient

Polynomial composition multiplies the power-of-three exponents. Mathlib's
`AdjoinRoot.compAlgEquiv` then supplies the tower equivalence and its generator
laws, with only equality transports on the two defining polynomials.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem binaryModulus_comp_pow_three (s v : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ (3 ^ v)) = binaryModulus (s + v) := by
  simp only [binaryModulus, Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp, ← pow_mul, Nat.pow_add]
  congr 2 <;> congr 1 <;> ring

theorem extensionModulus_monic (s v : Nat) : (extensionModulus s v).Monic :=
  binomialModulus_monic _ v

theorem extensionModulus_natDegree (s v : Nat) :
    (extensionModulus s v).natDegree = 3 ^ v := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  exact binomialModulus_natDegree _ v

theorem extensionModulus_irreducible (s v : Nat) : Irreducible (extensionModulus s v) := by
  let : Fact (Irreducible (binaryModulus s)) := ⟨binaryModulus_irreducible s⟩
  exact binomialModulus_irreducible _ v (root_binaryModulus_noncube s)

private theorem mapped_pow_sub_root (s v : Nat) :
    (Polynomial.X ^ (3 ^ v) : Polynomial (ZMod 2)).map (AdjoinRoot.of (binaryModulus s)) -
      Polynomial.C (AdjoinRoot.root (binaryModulus s)) = extensionModulus s v := by
  simp only [extensionModulus, binomialModulus, Polynomial.map_pow, Polynomial.map_X]

/-- Transport Mathlib's composition equivalence along the two polynomial identities. -/
noncomputable def binaryExtensionEquiv (s v : Nat) :
    AdjoinRoot (binaryModulus (s + v)) ≃ₐ[ZMod 2] AdjoinRoot (extensionModulus s v) :=
  (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (binaryModulus_comp_pow_three s v).symm).trans
    ((AdjoinRoot.compAlgEquiv (binaryModulus s) (Polynomial.X ^ (3 ^ v))).trans
      (AdjoinRoot.algEquivOfEq (ZMod 2) _ _ (mapped_pow_sub_root s v)))

theorem binaryExtensionEquiv_root (s v : Nat) :
    binaryExtensionEquiv s v (AdjoinRoot.root (binaryModulus (s + v))) =
      AdjoinRoot.root (extensionModulus s v) := by
  simp only [binaryExtensionEquiv, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
    AdjoinRoot.compAlgEquiv_root]

theorem binaryExtensionEquiv_symm_root (s v : Nat) :
    (binaryExtensionEquiv s v).symm (AdjoinRoot.root (extensionModulus s v)) =
      AdjoinRoot.root (binaryModulus (s + v)) :=
  (binaryExtensionEquiv s v).symm_apply_eq.mpr (binaryExtensionEquiv_root s v).symm

theorem root_extensionModulus_pow (s v : Nat) :
    AdjoinRoot.root (extensionModulus s v) ^ (3 ^ v) =
      AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s)) := by
  have vanishes := AdjoinRoot.mk_self (f := extensionModulus s v)
  change AdjoinRoot.mk (extensionModulus s v)
    (Polynomial.X ^ (3 ^ v) - Polynomial.C (AdjoinRoot.root (binaryModulus s))) = 0 at vanishes
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] using vanishes

theorem binaryExtensionEquiv_symm_of_root (s v : Nat) :
    (binaryExtensionEquiv s v).symm
      (AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s))) =
        AdjoinRoot.root (binaryModulus (s + v)) ^ (3 ^ v) := by
  rw [← root_extensionModulus_pow, map_pow, binaryExtensionEquiv_symm_root]

theorem binaryExtensionEquiv_mk (s v : Nat) (p : Polynomial (ZMod 2)) :
    binaryExtensionEquiv s v (AdjoinRoot.mk (binaryModulus (s + v)) p) =
      Polynomial.aeval (AdjoinRoot.root (extensionModulus s v)) p := by
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, binaryExtensionEquiv_root]

theorem binaryExtensionEquiv_symm_of_mk (s v : Nat) (p : Polynomial (ZMod 2)) :
    (binaryExtensionEquiv s v).symm
      (AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.mk (binaryModulus s) p)) =
        Polynomial.aeval (AdjoinRoot.root (binaryModulus (s + v)) ^ (3 ^ v)) p := by
  let φ := (binaryExtensionEquiv s v).symm.toAlgHom.comp
    (AdjoinRoot.ofAlgHom (ZMod 2) (extensionModulus s v))
  change φ (AdjoinRoot.mk (binaryModulus s) p) = _
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply]
  exact congrArg (fun x => Polynomial.aeval x p) (binaryExtensionEquiv_symm_of_root s v)

theorem binaryExtensionEquiv_symm_mk (s v : Nat)
    (p : Polynomial (AdjoinRoot (binaryModulus s))) :
    (binaryExtensionEquiv s v).symm (AdjoinRoot.mk (extensionModulus s v) p) =
      p.eval₂ ((binaryExtensionEquiv s v).symm.toRingHom.comp
        (AdjoinRoot.of (extensionModulus s v))) (AdjoinRoot.root (binaryModulus (s + v))) := by
  rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
  change (binaryExtensionEquiv s v).symm.toRingHom
    (p.eval₂ (AdjoinRoot.of (extensionModulus s v)) (AdjoinRoot.root (extensionModulus s v))) = _
  rw [Polynomial.hom_eval₂]
  exact congrArg
    (p.eval₂ ((binaryExtensionEquiv s v).symm.toRingHom.comp (AdjoinRoot.of (extensionModulus s v))))
    (binaryExtensionEquiv_symm_root s v)

end Algebraic.Cutwidth.Extractor.Internal
