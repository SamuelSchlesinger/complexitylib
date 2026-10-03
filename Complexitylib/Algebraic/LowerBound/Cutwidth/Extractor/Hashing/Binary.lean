/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Hashing.Binary.Internal

/-!
# A uniform linear binary hash and its strong extraction guarantee

Multiplication modulo the explicit binary trinomial followed by coefficient
truncation is universal at every output width within the field width. The
actual bit-list evaluator computes that same map and belongs to FP uniformly
in its source, seed, modulus half-degree, and requested output width.

For every fixed input length within field capacity, decoding is injective.
The retained-seed leftover-hash lemma therefore applies directly to the
computed output on flat sources. The seed has one field element's width;
this is a building block for shorter-seed constructions. Source credits for
the standard multiplication and truncation method are in Hashing.Field.Defs.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- Every coefficient vector shorter than the modulus degree is represented. -/
theorem binaryCoefficientPrefix_surjective {s m : Nat} (width : m ≤ 2 * 3 ^ s) :
    Function.Surjective (binaryCoefficientPrefix s m) :=
  Internal.binaryCoefficientPrefix_surjective width

/-- Every fixed-seed binary field hash preserves source addition. -/
theorem binaryFieldHash_add (s m : Nat) (a b seed : AdjoinRoot (binaryModulus s)) :
    binaryFieldHash s m (a + b) seed = binaryFieldHash s m a seed + binaryFieldHash s m b seed :=
  Internal.binaryFieldHash_add s m a b seed

/-- Every fixed-seed binary field hash sends zero to zero. -/
theorem binaryFieldHash_zero (s m : Nat) (seed : AdjoinRoot (binaryModulus s)) :
    binaryFieldHash s m 0 seed = 0 :=
  Internal.binaryFieldHash_zero s m seed

open scoped Classical in
/-- Distinct field inputs collide on exactly a reciprocal-output fraction of seeds. -/
theorem binaryFieldHash_collision_count {s m : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))] (width : m ≤ 2 * 3 ^ s)
    {a b : AdjoinRoot (binaryModulus s)} (distinct : a ≠ b) :
    (Finset.univ.filter fun seed => binaryFieldHash s m a seed =
      binaryFieldHash s m b seed).card * 2 ^ m = 2 ^ (2 * 3 ^ s) :=
  Internal.binaryFieldHash_collision_count width distinct

/-- Coefficient-prefix multiplication is a universal family. -/
theorem binaryFieldHash_universal {s m : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))] (width : m ≤ 2 * 3 ^ s) :
    UniversalHashFamily (binaryFieldHash s m) :=
  Internal.binaryFieldHash_universal width

/-- Decoding is injective on each fixed source length within field capacity. -/
theorem binaryField_decode_inj_of_length (s n : Nat) (capacity : n ≤ 2 * 3 ^ s)
    (a b : List Bool) (ha : a.length = n) (hb : b.length = n)
    (same : BinaryFieldCodec.decode s a = BinaryFieldCodec.decode s b) : a = b :=
  Internal.binaryField_decode_inj_of_length s n capacity a b ha hb same

/-- The actual multiply/reduce/take program computes the binary field hash. -/
theorem binaryHashBits_correct (s : Nat) (source seed halfDegree outputCount : List Bool)
    (half : halfDegree.length = 3 ^ s) :
    Polynomial.toFn outputCount.length (ofBits (binaryHashBits source seed halfDegree outputCount)) =
      binaryFieldHash s outputCount.length (BinaryFieldCodec.decode s source)
        (BinaryFieldCodec.decode s seed) :=
  Internal.binaryHashBits_correct s source seed halfDegree outputCount half

/-- The decoded program at a canonical field seed is the semantic hash. -/
theorem decodedBinaryHash_eq (s m : Nat) (source : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) :
    decodedBinaryHash s m source seed = binaryFieldHash s m (BinaryFieldCodec.decode s source) seed :=
  Internal.decodedBinaryHash_eq s m source seed

/-- The actual decoded hash preserves padded source XOR, including unequal lengths. -/
theorem decodedBinaryHash_addBits (s m : Nat) (a b : List Bool)
    (seed : AdjoinRoot (binaryModulus s)) :
    decodedBinaryHash s m (addBits a b) seed =
      decodedBinaryHash s m a seed + decodedBinaryHash s m b seed :=
  Internal.decodedBinaryHash_addBits s m a b seed

/-- The actual program is universal on fixed-length sources within capacity. -/
theorem decodedBinaryHash_universal {s m n : Nat}
    [Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : n ≤ 2 * 3 ^ s) (width : m ≤ 2 * 3 ^ s) :
    UniversalHashFamily (fun bits : {bits : List Bool // bits.length = n} =>
      decodedBinaryHash s m bits.val) :=
  Internal.decodedBinaryHash_universal capacity width

/-- The actual program strongly extracts whenever the sharp leftover-hash budget holds. -/
theorem decodedBinaryHash_flatStrongSeededExtractor {s m n K : Nat} {ε : ℝ}
    [Fintype (AdjoinRoot (binaryModulus s))]
    (capacity : n ≤ 2 * 3 ^ s) (width : m ≤ 2 * 3 ^ s)
    (positive : 0 < K) (error : 0 ≤ ε) (budget : (2 : ℝ) ^ m ≤ 4 * ε ^ 2 * K) :
    FlatStrongSeededExtractor (fun bits : {bits : List Bool // bits.length = n} =>
      decodedBinaryHash s m bits.val) K ε :=
  Internal.decodedBinaryHash_flatStrongSeededExtractor capacity width positive error budget

/-- A valid field modulus gives the requested prefix, capped at the field width. -/
theorem binaryHashBits_length (s : Nat) (source seed halfDegree outputCount : List Bool)
    (half : halfDegree.length = 3 ^ s) :
    (binaryHashBits source seed halfDegree outputCount).length =
      min outputCount.length (2 * 3 ^ s) :=
  Internal.binaryHashBits_length s source seed halfDegree outputCount half

/-- The evaluator reads the four runtime words from their paired encoding. -/
theorem binaryHashEval_pair (source seed halfDegree outputCount : List Bool) :
    binaryHashEval (pair (pair source seed) (pair halfDegree outputCount)) =
      binaryHashBits source seed halfDegree outputCount :=
  Internal.binaryHashEval_pair source seed halfDegree outputCount

/-- Even malformed paired inputs have output length at most the input length. -/
theorem binaryHashEval_length_le (z : List Bool) : (binaryHashEval z).length ≤ z.length :=
  Internal.binaryHashEval_length_le z

/-- Runtime binary hashing is uniformly polynomial-time in all four operands. -/
@[polytime] theorem binaryHashBits_mem_FP {source seed halfDegree outputCount : List Bool → List Bool}
    (hsource : source ∈ FP) (hseed : seed ∈ FP)
    (hhalf : halfDegree ∈ FP) (hcount : outputCount ∈ FP) :
    (fun z => binaryHashBits (source z) (seed z) (halfDegree z) (outputCount z)) ∈ FP :=
  Internal.binaryHashBits_mem_FP hsource hseed hhalf hcount

/-- A single polynomial-time machine computes the paired runtime hash. -/
@[polytime] theorem binaryHashEval_mem_FP : binaryHashEval ∈ FP :=
  Internal.binaryHashEval_mem_FP

end Algebraic.Cutwidth.Extractor
