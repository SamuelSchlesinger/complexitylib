/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Encoding.Explicit.Block.Program.Internal

/-!
# A uniform runtime level of shared-seed block condensation

One polynomial-time map applies the actual scheduled condenser to every
fixed-width input block, reusing the supplied seed and preserving block order.
The width, entropy and error parameters, rate, seed, payload, and unary block
count remain runtime operands. Concatenated Boolean tuples recover exactly
the concatenation of their individual condenser outputs, including zero width
and zero blocks.

The underlying algebraic map and parameter source credits remain in
`Condenser.Polynomial` and `Parameters.Sparse`. This certifies one level only.
`Recursion.Scheduled.Program` iterates the levels under a uniform numerical
schedule (`scheduledBlockExtractorEval_mem_FP`).
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Every requested block contributes one scheduled output of the exact selected width. -/
theorem explicitBlockCondenserBits_length (n k e u : Nat) (blocks seed count : List Bool) :
    (explicitBlockCondenserBits n k e u blocks seed count).length = count.length *
      (condenserCoordinates k (sparsePowerBits u (explicitCondenserBudget n k e)) *
        sparseFieldBits u (explicitCondenserBudget n k e)) :=
  Internal.explicitBlockCondenserBits_length n k e u blocks seed count

/-- Flattening a fixed-width tuple and running the program gives exactly the
individual scheduled outputs in the same order, all with the same seed. -/
theorem explicitBlockCondenserBits_ofFn (n k e u : Nat) {t : Nat}
    (blocks : Fin t → Fin n → Bool) (seed count : List Bool) (size : count.length = t) :
    explicitBlockCondenserBits n k e u
        (List.ofFn (fun i => List.ofFn (blocks i))).flatten seed count =
      (List.ofFn (fun i => explicitCondenserBits n k e u (List.ofFn (blocks i)) seed)).flatten :=
  Internal.explicitBlockCondenserBits_ofFn n k e u blocks seed count size

open Complexity in
/-- Runtime parameters and a runtime unary block count compose into one uniform
polynomial-time level; the result is the raw concatenation of all block outputs. -/
@[polytime] theorem explicitBlockCondenserBits_mem_FP {n k e u : List Bool → Nat}
    {blocks seed count : List Bool → List Bool}
    (hn : UnaryFn n) (hk : UnaryFn k) (he : UnaryFn e) (hu : UnaryFn u)
    (hblocks : blocks ∈ FP) (hseed : seed ∈ FP) (hcount : count ∈ FP) :
    (fun z => explicitBlockCondenserBits (n z) (k z) (e z) (u z)
      (blocks z) (seed z) (count z)) ∈ FP :=
  Internal.explicitBlockCondenserBits_mem_FP hn hk he hu hblocks hseed hcount

end Algebraic.Cutwidth.Extractor
