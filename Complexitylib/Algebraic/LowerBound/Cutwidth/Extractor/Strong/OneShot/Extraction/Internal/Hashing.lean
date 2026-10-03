/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Serialization

/-!
# Universality after exact coordinate serialization

Serializing the whole coordinate vector and embedding the resulting word in
a sufficiently wide binary field preserves distinctness. Multiplication and
truncation in that field therefore give a universal hash on coordinate
vectors. No injectivity of the actual condenser is used.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem serializedBinaryHash_universal {s t m ell : Nat}
    [Fintype (AdjoinRoot (binaryModulus t))]
    (capacity : m * (2 * 3 ^ s) ≤ 2 * 3 ^ t) (width : ell ≤ 2 * 3 ^ t) :
    UniversalHashFamily (fun coords : Fin m → AdjoinRoot (binaryModulus s) =>
      binaryFieldHash t ell (BinaryFieldCodec.decode t (encodeCondenserOutput s m coords))) := by
  apply (binaryFieldHash_universal width).comp_injective
  intro a b same
  apply encodeCondenserOutput_injective s m
  exact binaryField_decode_inj_of_length t _ capacity _ _
    (encodeCondenserOutput_length s m a) (encodeCondenserOutput_length s m b) same

end Algebraic.Cutwidth.Extractor.Internal
