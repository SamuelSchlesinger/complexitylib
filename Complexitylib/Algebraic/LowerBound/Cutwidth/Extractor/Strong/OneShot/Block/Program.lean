/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Block.Program.Internal

/-!
# Uniform one-shot extraction across all leaf blocks

The actual program applies one-shot extraction to a runtime number of
fixed-width blocks with one shared pair of seed words. It emits exactly
`count.length*ell` bits. On concatenated Boolean tuples and canonical field
seeds, the output is exactly the serialized tuple of decoded one-shot outputs.
This includes empty tuples and zero input or output widths.

The existing one-shot program supplies the condensation and hashing
mechanism. Its shared-seed statistical use follows Chattopadhyay--Goodman--Liao,
Lemma 5.5, <https://eccc.weizmann.ac.il/report/2021/075/>. This module certifies
the uniform runtime leaf stage; it does not assert a polynomial-time evaluator
for the complete variable-depth recursion.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Every requested input block contributes exactly `ell` output bits. -/
theorem oneShotBlockExtractorBits_length (n ell e : Nat)
    (blocks condenserSeed hashSeed count : List Bool) :
    (oneShotBlockExtractorBits n ell e blocks condenserSeed hashSeed count).length =
      count.length * ell :=
  Internal.oneShotBlockExtractorBits_length n ell e blocks condenserSeed hashSeed count

/-- Fixed-width tuple inputs produce their individual one-shot outputs in the same order. -/
theorem oneShotBlockExtractorBits_ofFn (n ell e : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool) (condenserSeed hashSeed count : List Bool)
    (size : count.length = t) :
    oneShotBlockExtractorBits n ell e
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten condenserSeed hashSeed count =
      (List.ofFn (fun i => oneShotExtractorBits n ell e (List.ofFn (blocks i))
        condenserSeed hashSeed)).flatten :=
  Internal.oneShotBlockExtractorBits_ofFn n ell e blocks condenserSeed hashSeed count size

/-- At canonical shared field seeds, the runtime word is the decoded statistical tuple
serialized in block order, with field values `0,1` represented by Boolean bits. -/
theorem oneShotBlockExtractorBits_eq_decoded (n ell e : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool)
    (seeds : AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))
    (count : List Bool) (size : count.length = t) :
    oneShotBlockExtractorBits n ell e
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten
        (BinaryFieldCodec.encode (oneShotCondenserExponent n ell e) seeds.1)
        (BinaryFieldCodec.encode (oneShotHashExponent n ell e) seeds.2) count =
      (List.ofFn (fun i => List.ofFn (fun j =>
        decide (decodedOneShotExtractor n ell e (List.ofFn (blocks i)) seeds j = 1)))).flatten :=
  Internal.oneShotBlockExtractorBits_eq_decoded n ell e blocks seeds count size

open Complexity in
/-- Runtime unary parameters, payload, both seeds, and block count define one uniform FP map. -/
@[polytime] theorem oneShotBlockExtractorBits_mem_FP {n ell e : List Bool → Nat}
    {blocks condenserSeed hashSeed count : List Bool → List Bool}
    (hn : UnaryFn n) (hell : UnaryFn ell) (he : UnaryFn e)
    (hblocks : blocks ∈ FP) (hcondenser : condenserSeed ∈ FP)
    (hhash : hashSeed ∈ FP) (hcount : count ∈ FP) :
    (fun z => oneShotBlockExtractorBits (n z) (ell z) (e z)
      (blocks z) (condenserSeed z) (hashSeed z) (count z)) ∈ FP :=
  Internal.oneShotBlockExtractorBits_mem_FP hn hell he hblocks hcondenser hhash hcount

end Algebraic.Cutwidth.Extractor
