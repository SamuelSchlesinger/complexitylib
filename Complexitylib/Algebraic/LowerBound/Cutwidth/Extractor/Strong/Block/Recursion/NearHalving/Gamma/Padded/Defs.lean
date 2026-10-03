/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Gamma.Program.Defs

/-!
# The Gamma program with a fixed polylogarithmic seed budget

The input and seed are ordinary Boolean vectors. Run the actual total string
program and read its output coordinates, with the same total false default
used by the bitstring APIs. The seed budget is an explicit cubic polynomial
in the ceiling input logarithm; the extra seed suffix is ignored on valid
sizes while remaining part of the retained seed in statistical tests.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Extractor

/-- A simple uniform seed budget covering the actual selected seed length at valid sizes. -/
def gammaBlockSeedBudget (b : Nat) : Nat := 2 ^ 27 * gammaBlockLog b ^ 3

/-- Read the actual Gamma program on a Boolean source and a fixed-budget Boolean seed. -/
def gammaBlockPaddedExtractor (b : Nat) (x : Fin (8 * b) → Bool)
    (seed : Fin (gammaBlockSeedBudget b) → Bool) (j : Fin b) : Bool :=
  (gammaBlockExtractorRuntime b (List.ofFn x) (List.ofFn seed))[j.val]?.getD false

end Algebraic.Cutwidth.Extractor
