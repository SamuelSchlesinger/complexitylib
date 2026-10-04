/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding.Internal

/-!
# Exact enumeration and advice for the actual source reduction

Little-endian coding is a bijection between the finite enumeration range
and Boolean words. Concatenating the outer and candidate codes assigns
distinct advice of one fixed length to every actual sampler position.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Enumerated Boolean words serialize to the actual fixed-width binary encoder. -/
theorem sourceReductionIndexWord_ofFn (width : Nat) (index : Fin (2 ^ width)) :
    List.ofFn (sourceReductionIndexWord width index) = Nat.toBitsLE width index.val :=
  Internal.sourceReductionIndexWord_ofFn width index

/-- Decoding an enumerated word recovers its index. -/
theorem sourceReductionWordIndex_indexWord (width : Nat) (index : Fin (2 ^ width)) :
    sourceReductionWordIndex width (sourceReductionIndexWord width index) = index :=
  Internal.sourceReductionWordIndex_indexWord width index

/-- Re-encoding a decoded word recovers every coordinate. -/
theorem sourceReductionIndexWord_wordIndex (width : Nat) (word : Fin width → Bool) :
    sourceReductionIndexWord width (sourceReductionWordIndex width word) = word :=
  Internal.sourceReductionIndexWord_wordIndex width word

/-- The concrete little-endian enumeration is an equivalence, including at width zero. -/
@[expose] def sourceReductionIndexEquiv (width : Nat) : Fin (2 ^ width) ≃ (Fin width → Bool) where
  toFun := sourceReductionIndexWord width
  invFun := sourceReductionWordIndex width
  left_inv := sourceReductionWordIndex_indexWord width
  right_inv := sourceReductionIndexWord_wordIndex width

/-- Every actual position receives advice of the same total width. -/
theorem sourceReductionAdvice_length (outerBits candidateBits : Nat)
    (position : Fin (2 ^ outerBits) × Fin (2 ^ candidateBits)) :
    (sourceReductionAdvice outerBits candidateBits position).length = outerBits + candidateBits :=
  Internal.sourceReductionAdvice_length outerBits candidateBits position

/-- Distinct outer/candidate positions receive distinct advice words. -/
theorem sourceReductionAdvice_injective (outerBits candidateBits : Nat) :
    Function.Injective (sourceReductionAdvice outerBits candidateBits) :=
  Internal.sourceReductionAdvice_injective outerBits candidateBits

end Algebraic.Cutwidth.Extractor
