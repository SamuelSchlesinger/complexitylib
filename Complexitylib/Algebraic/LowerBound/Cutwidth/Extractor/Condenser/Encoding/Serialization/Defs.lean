/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec.Defs
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs

/-!
# Fixed-width serialization of condenser coordinates

Coordinates are written in increasing index order, each using the canonical
binary field width `2 * 3^s`. Decoding reads the same consecutive blocks.
Zero coordinates give an empty encoding. These semantic codec operations
relate coordinate vectors to the runtime program's existing output layout;
they introduce no separate runtime algorithm.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- Concatenate the canonical field encodings in coordinate order. -/
noncomputable def encodeCondenserOutput (s m : Nat)
    (coords : Fin m → AdjoinRoot (binaryModulus s)) : List Bool :=
  (List.ofFn fun i : Fin m => BinaryFieldCodec.encode s (coords i)).flatten

/-- Decode consecutive coordinate blocks; absent input bits use the existing block convention. -/
noncomputable def decodeCondenserOutput (s m : Nat) (bits : List Bool) :
    Fin m → AdjoinRoot (binaryModulus s) :=
  fun i => BinaryFieldCodec.decode s
    (Complexity.BitPolynomial.coefficientBlock bits (2 * 3 ^ s) i.val)

end Algebraic.Cutwidth.Extractor
