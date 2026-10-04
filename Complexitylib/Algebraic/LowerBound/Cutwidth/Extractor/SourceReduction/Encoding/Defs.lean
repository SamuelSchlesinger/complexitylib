/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Mathlib.NatBits
public import Mathlib.Data.List.OfFn

/-!
# Concrete indices and advice for the source reduction

Enumerate Boolean words by their fixed-width little-endian binary codes.
The advice for a sampler position concatenates its outer and candidate
codes. These are the actual computable encodings used by the reduction;
no arbitrary equivalence between finite types is chosen.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- The fixed-width little-endian word at a finite enumeration index. -/
def sourceReductionIndexWord (width : Nat) (index : Fin (2 ^ width)) (j : Fin width) : Bool :=
  (Nat.toBitsLE width index.val)[j.val]?.getD false

/-- The exact finite index of a Boolean word under little-endian enumeration. -/
def sourceReductionWordIndex (width : Nat) (word : Fin width → Bool) : Fin (2 ^ width) :=
  ⟨Nat.fromBitsLE (List.ofFn word), by
    simpa only [List.length_ofFn] using Nat.fromBitsLE_lt_pow_length (List.ofFn word)⟩

/-- Concatenate the outer and candidate codes to give unique equal-length advice. -/
def sourceReductionAdvice (outerBits candidateBits : Nat)
    (position : Fin (2 ^ outerBits) × Fin (2 ^ candidateBits)) : List Bool :=
  Nat.toBitsLE outerBits position.1.val ++ Nat.toBitsLE candidateBits position.2.val

end Algebraic.Cutwidth.Extractor
