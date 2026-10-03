/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Pair.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Correctness.Internal

/-!
# The runtime block program computes the checked condense-then-split map

On a concatenated tuple of fixed-width Boolean inputs and a canonical field
seed, the actual one-level program returns exactly the concatenated Boolean
blocks of `condenseSplitMap`. Each pair's first half precedes its second,
and all original pairs remain in input order. No bits are padded or discarded.

The equality also covers zero input width, zero output width, and zero blocks.
It identifies the computational level with the deterministic map used in the
statistical theorem; it adds no new statistical assumptions, loop evaluator,
or polynomial-time claim for a variable number of recursive levels.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual shared-seed block program serializes exactly the deterministic
condense-then-split tuple, with both halves of each block kept consecutively. -/
theorem explicitBlockCondenserBits_eq_condenseSplitMap (n k e u : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool)
    (seed : AdjoinRoot (binaryModulus
      (sparseFieldExponent u (explicitCondenserBudget n k e))))
    (count : List Bool) (size : count.length = t) :
    explicitBlockCondenserBits n k e u
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten
        (BinaryFieldCodec.encode (sparseFieldExponent u (explicitCondenserBudget n k e))
          seed) count =
      (List.ofFn fun i => List.ofFn
        (condenseSplitMap (explicitCondenserPair n k e u) t blocks seed i)).flatten :=
  Internal.explicitBlockCondenserBits_eq_condenseSplitMap n k e u blocks seed count size

end Algebraic.Cutwidth.Extractor
