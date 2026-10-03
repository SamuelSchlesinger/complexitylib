/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Correctness.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Defs

/-!
# A binary condenser with parameters selected from the requested bounds

The source-length bound `n`, entropy budget `k`, inverse-error exponent `e`,
and rate parameter `u` determine all dimensions and iteration counts of the
existing runtime program. Its output consists of coordinate bits, without
the seed. The paired evaluator reads the four parameters from word lengths.

The decoded map interprets these same output bits in the selected binary
field. No source-length or parameter promises enter these total definitions;
the statistical guarantees impose their hypotheses separately.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

open Complexity Complexity.BitPolynomial

/-- Run the uniform binary program at the explicitly selected parameters. -/
def explicitCondenserBits (n k e u : Nat) (source seed : List Bool) : List Bool :=
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  let d := explicitCondenserExtensionDegree n k e u
  let r := sparsePowerBits u T
  let m := condenserCoordinates k r
  condenserBits source (List.replicate (3 ^ s) true) (List.replicate d true)
    seed (List.replicate r true) (List.replicate m true)

/-- Codec: `pair (pair source seed) (pair (pair n k) (pair e u))`, with parameters
given by the lengths of their words. -/
def explicitCondenserEval (z : List Bool) : List Bool :=
  let sourceSeed := pairFst z
  let params := pairSnd z
  let sourceBounds := pairFst params
  let quality := pairSnd params
  explicitCondenserBits (pairFst sourceBounds).length (pairSnd sourceBounds).length
    (pairFst quality).length (pairSnd quality).length
    (pairFst sourceSeed) (pairSnd sourceSeed)

/-- The actual scheduled output, interpreted as coordinates in the selected field. -/
noncomputable def decodedExplicitCondenser (n k e u : Nat) (bits : List Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e)))) :
    Fin (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e))) →
      AdjoinRoot (binaryModulus (sparseFieldExponent u (explicitCondenserBudget n k e))) :=
  let T := explicitCondenserBudget n k e
  let s := sparseFieldExponent u T
  fun i => BinaryFieldCodec.decode s
    (coefficientBlock (explicitCondenserBits n k e u bits (BinaryFieldCodec.encode s seed))
      (sparseFieldBits u T) i.val)

end Algebraic.Cutwidth.Extractor
