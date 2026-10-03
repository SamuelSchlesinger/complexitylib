/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Extension.Internal

/-!
# A binomial extension is one larger binary quotient

Write `t` for the root of the binary modulus `M_s`. Adjoining `u` with
`u^(3^v) = t` gives the same binary algebra as the quotient by `M_(s+v)`.
The equivalence sends the larger binary root to `u`; its inverse sends an
embedded base polynomial `p(t)` to `p(u^(3^v))`. The polynomial image laws
identify coefficient packing and evaluation in these two representations.

The construction reuses Mathlib's `AdjoinRoot.compAlgEquiv`, with equality
transports on the supplied defining polynomials:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/AdjoinRoot.html.
Irreducibility uses the binary root's proved noncube property and the Kummer
result documented in `Binomial`. These are semantic algebraic identifications;
no runtime claim on abstract quotient objects or global field instances is added.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Substitution by a power of three stays within the explicit binary family. -/
theorem binaryModulus_comp_pow_three (s v : Nat) :
    (binaryModulus s).comp (Polynomial.X ^ (3 ^ v)) = binaryModulus (s + v) :=
  Internal.binaryModulus_comp_pow_three s v

/-- The extension modulus is monic, including its linear case at `v = 0`. -/
theorem extensionModulus_monic (s v : Nat) : (extensionModulus s v).Monic :=
  Internal.extensionModulus_monic s v

/-- The extension degree is exactly the selected power of three. -/
theorem extensionModulus_natDegree (s v : Nat) :
    (extensionModulus s v).natDegree = 3 ^ v :=
  Internal.extensionModulus_natDegree s v

/-- The binary quotient's named noncube root makes the extension irreducible. -/
theorem extensionModulus_irreducible (s v : Nat) : Irreducible (extensionModulus s v) :=
  Internal.extensionModulus_irreducible s v

/-- The explicit binary quotient and the binomial tower are the same binary algebra. -/
noncomputable def binaryExtensionEquiv (s v : Nat) :
    AdjoinRoot (binaryModulus (s + v)) ≃ₐ[ZMod 2] AdjoinRoot (extensionModulus s v) :=
  Internal.binaryExtensionEquiv s v

/-- The larger binary generator maps to the extension generator. -/
theorem binaryExtensionEquiv_root (s v : Nat) :
    binaryExtensionEquiv s v (AdjoinRoot.root (binaryModulus (s + v))) =
      AdjoinRoot.root (extensionModulus s v) :=
  Internal.binaryExtensionEquiv_root s v

/-- The extension generator maps back to the larger binary generator. -/
theorem binaryExtensionEquiv_symm_root (s v : Nat) :
    (binaryExtensionEquiv s v).symm (AdjoinRoot.root (extensionModulus s v)) =
      AdjoinRoot.root (binaryModulus (s + v)) :=
  Internal.binaryExtensionEquiv_symm_root s v

/-- The defining extension relation identifies its generator power with the base root. -/
theorem root_extensionModulus_pow (s v : Nat) :
    AdjoinRoot.root (extensionModulus s v) ^ (3 ^ v) =
      AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s)) :=
  Internal.root_extensionModulus_pow s v

/-- The embedded base generator corresponds to the larger generator raised to `3^v`. -/
theorem binaryExtensionEquiv_symm_of_root (s v : Nat) :
    (binaryExtensionEquiv s v).symm
      (AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.root (binaryModulus s))) =
        AdjoinRoot.root (binaryModulus (s + v)) ^ (3 ^ v) :=
  Internal.binaryExtensionEquiv_symm_of_root s v

/-- Every binary polynomial class maps to its evaluation at the extension generator. -/
theorem binaryExtensionEquiv_mk (s v : Nat) (p : Polynomial (ZMod 2)) :
    binaryExtensionEquiv s v (AdjoinRoot.mk (binaryModulus (s + v)) p) =
      Polynomial.aeval (AdjoinRoot.root (extensionModulus s v)) p :=
  Internal.binaryExtensionEquiv_mk s v p

/-- Embedded base coefficients evaluate at the corresponding power of the larger root. -/
theorem binaryExtensionEquiv_symm_of_mk (s v : Nat) (p : Polynomial (ZMod 2)) :
    (binaryExtensionEquiv s v).symm
      (AdjoinRoot.of (extensionModulus s v) (AdjoinRoot.mk (binaryModulus s) p)) =
        Polynomial.aeval (AdjoinRoot.root (binaryModulus (s + v)) ^ (3 ^ v)) p :=
  Internal.binaryExtensionEquiv_symm_of_mk s v p

/-- An arbitrary extension polynomial evaluates in the larger binary quotient
after transporting each coefficient along the same equivalence. -/
theorem binaryExtensionEquiv_symm_mk (s v : Nat)
    (p : Polynomial (AdjoinRoot (binaryModulus s))) :
    (binaryExtensionEquiv s v).symm (AdjoinRoot.mk (extensionModulus s v) p) =
      p.eval₂ ((binaryExtensionEquiv s v).symm.toRingHom.comp
        (AdjoinRoot.of (extensionModulus s v))) (AdjoinRoot.root (binaryModulus (s + v))) :=
  Internal.binaryExtensionEquiv_symm_mk s v p

end Algebraic.Cutwidth.Extractor
