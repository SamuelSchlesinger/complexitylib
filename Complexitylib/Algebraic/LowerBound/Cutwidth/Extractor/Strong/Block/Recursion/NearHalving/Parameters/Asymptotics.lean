/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Asymptotics.Internal

/-!
# Eventual validity of the near-halving parameter guard

The binary logarithm of the target length eventually dominates three
iterated ceiling logarithms plus fifteen. Consequently the finite guard
required by the rounded parameter choice eventually holds. This numeric
fact alone asserts neither extraction nor polynomial-time evaluation.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Every sufficiently large target length satisfies the exact finite size guard. -/
theorem eventually_gammaBlockSizeGuard :
    ∀ᶠ b : Nat in Filter.atTop, GammaBlockSizeGuard b :=
  Internal.eventually_gammaBlockSizeGuard

end Algebraic.Cutwidth.Extractor
