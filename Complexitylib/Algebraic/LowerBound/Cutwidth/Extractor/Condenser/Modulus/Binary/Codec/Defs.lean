/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary
public import Complexitylib.Encoding.BitPolynomial.Defs

/-!
# Fixed-width semantic representations of binary quotient elements

Decoding interprets low-to-high coefficient bits and takes their quotient class.
Encoding reads the coefficients of the unique remainder of degree below the
binary modulus, retaining exactly `2 * 3^s` bits. These functions relate the
semantic quotient to bit lists; they assert no runtime bound on abstract
quotient objects and introduce no global field or finiteness instances.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor.BinaryFieldCodec

/-- Canonical-width coefficient lists for the `s`th binary quotient. -/
abbrev Bits (s : Nat) := {bits : List Bool // bits.length = 2 * 3 ^ s}

/-- Interpret a coefficient list and then pass to its binary quotient class. -/
noncomputable def decode (s : Nat) (bits : List Bool) : AdjoinRoot (binaryModulus s) :=
  AdjoinRoot.mk (binaryModulus s) (Complexity.BitPolynomial.ofBits bits)

/-- Read every coefficient below the modulus degree, retaining high zero bits. -/
noncomputable def encode (s : Nat) (x : AdjoinRoot (binaryModulus s)) : List Bool :=
  List.ofFn fun i : Fin (2 * 3 ^ s) =>
    decide ((AdjoinRoot.modByMonicHom (binaryModulus_monic s) x).coeff i.val = 1)

end Algebraic.Cutwidth.Extractor.BinaryFieldCodec
