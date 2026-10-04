/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds.Defs
public import Mathlib.Basic.Real.Basic
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.BadSeeds.Internal

/-!
# A common small seed test for all low-order parities

There are at most `A^t` nonempty subsets of at most `t` among `A` coordinates.
If each such test and each of `C` candidates excludes at most an `η` fraction
of seeds, their union excludes at most an `A^t * C * η` fraction. This is
the union-bound step of Chattopadhyay and Liao, *Extractors for Sum of Two
Sources* (2021), Lemma 5.4, before equation (5) is used on good sampler outputs.
`SourceReduction.Leakage` supplies the individual seed bounds from the actual
selected affine correlation breaker after paying the complete leakage reserve.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The nonempty subsets of at most `t` coordinates are covered by the
ranges of all `t`-tuples. This also covers zero order and an empty type. -/
theorem card_parityTests_le_pow (ι : Type*) [Fintype ι] (t : Nat) :
    (parityTests ι t).card ≤ Fintype.card ι ^ t :=
  Internal.card_parityTests_le_pow ι t

/-- Union the excluded seeds over every low-order parity and every
candidate position, preserving the full number of candidate choices. -/
theorem card_parityBadSeeds_le {ι Choice Seed : Type*} [Fintype ι] [Fintype Choice]
    [Fintype Seed] (bad : Finset ι → Choice → Finset Seed) (t : Nat)
    {η : ℝ} (hη : 0 ≤ η)
    (bound : ∀ U ∈ parityTests ι t, ∀ z,
      ((bad U z).card : ℝ) ≤ η * Fintype.card Seed) :
    ((parityBadSeeds bad t).card : ℝ) ≤
      (Fintype.card ι : ℝ) ^ t * Fintype.card Choice * η * Fintype.card Seed :=
  Internal.card_parityBadSeeds_le bad t hη bound

end Algebraic.Cutwidth.Extractor
