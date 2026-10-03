/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Run.Correctness
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Codec
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Boolean
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Modulus.Binary.Codec

/-!
# Exact execution of the complete near-halving extractor

The canonical prefix supplies each internal shared seed. The runtime's
fixed-width slices then recover precisely the final condenser and hash
words, ignoring any later bits. The checked one-shot block evaluator
serializes the same semantic tuple, and the Boolean output equivalence
identifies this word with the flat Boolean-vector extractor.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seeds : NearHalvingBlockSeeds n h Q E) (tail : List Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (encodeNearHalvingBlockSeeds n h Q E seeds ++ tail) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (nearHalvingBlockExtractor n h Q E x seeds i j = 1)).flatten := by
  rw [nearHalvingBlockExtractorBits, encodeNearHalvingBlockSeeds_append]
  simp only [List.append_assoc]
  rw [nearHalvingBlockRun_eq_recursiveBlockMap]
  dsimp only [nearHalvingBlockFinish]
  rw [← BinaryFieldCodec.length_encode _ seeds.2.1,
    ← BinaryFieldCodec.length_encode _ seeds.2.2,
    List.take_left, List.drop_left, List.take_left]
  rw [oneShotBlockExtractorBits_eq_decoded (nearHalvingBlockWidth n h Q E h)
      (nearHalvingBlockLeafLength h Q) E
      (recursiveBlockMap (fun (x : Fin n → Bool) (_ : Unit) (_ : Fin 1) => x)
        (nearHalvingBlockStep n h Q E) h x seeds.1) seeds.2
      (List.replicate (recursiveBlockCount 1 h) true) (by simp)]
  rfl

theorem nearHalvingBlockExtractorBits_eq_nearHalvingBlockExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seeds : NearHalvingBlockSeeds n h Q E) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (encodeNearHalvingBlockSeeds n h Q E seeds) =
      (List.ofFn fun i => List.ofFn fun j =>
        decide (nearHalvingBlockExtractor n h Q E x seeds i j = 1)).flatten := by
  simpa only [List.append_nil] using
    nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockExtractor n h Q E x seeds []

theorem nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockBooleanExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool)
    (tail : List Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (List.ofFn seed ++ tail) = List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) := by
  rw [nearHalvingBlockBooleanExtractor_ofFn]
  have correct := nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockExtractor n h Q E x
    (decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed)) tail
  rw [encode_decodeNearHalvingBlockSeeds n h Q E (List.ofFn seed) List.length_ofFn] at correct
  exact correct

theorem nearHalvingBlockExtractorBits_eq_nearHalvingBlockBooleanExtractor (n h Q E : Nat)
    (x : Fin n → Bool) (seed : Fin (nearHalvingBlockSeedBits n h Q E) → Bool) :
    nearHalvingBlockExtractorBits n h Q E (nearHalvingBlockLeafLength h Q) h (List.ofFn x)
        (List.ofFn seed) = List.ofFn (nearHalvingBlockBooleanExtractor n h Q E x seed) := by
  simpa only [List.append_nil] using
    nearHalvingBlockExtractorBits_append_eq_nearHalvingBlockBooleanExtractor n h Q E x seed []

end Algebraic.Cutwidth.Extractor.Internal
