/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Defs
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Linearity.Internal

/-!
# XOR additivity of the specified recursive extractor

For every fixed complete seed tuple, input XOR becomes pointwise addition
of the actual output coordinates in `ZMod 2`. This holds for all numerical
parameters, independently of the statistical entropy and error budgets.

The proof composes the checked source-addition identities of the concrete
condenser, serializer, and one-shot extractor through the recursive program.
It makes explicit the linearity invariant used in the recursive construction
of Chattopadhyay--Goodman--Liao, credited in `Recursion.Linearity`.
No field enumeration or uniform runtime assumption enters this identity.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- At fixed retained seeds, the actual scheduled extractor sends input XOR to output addition. -/
theorem scheduledBlockExtractor_xor (n h Q E ell : Nat) (x x' : Fin n → Bool)
    (seeds : RecursiveSeeds (ScheduledInitialSeed n h Q E) (ScheduledLevelSeed n h Q E) h ×
      ScheduledFinalSeed n h Q E ell) :
    scheduledBlockExtractor n h Q E ell (fun i => Bool.xor (x i) (x' i)) seeds =
      scheduledBlockExtractor n h Q E ell x seeds +
        scheduledBlockExtractor n h Q E ell x' seeds :=
  Internal.scheduledBlockExtractor_xor n h Q E ell x x' seeds

end Algebraic.Cutwidth.Extractor
