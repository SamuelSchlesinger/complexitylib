/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Mathlib.Data.Fintype.Pi
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Extraction.Internal.Composition
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Correctness

/-!
# Statistical extraction by the actual one-shot program

The pointwise correctness theorem identifies the emitted coordinates with
the proved statistical composition. Rewriting under the finite test count
therefore transfers the guarantee without changing the source or either
retained seed.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem decodedOneShotExtractor_flat (n ell e : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (P : Finset (List Bool)) (source : ∀ bits ∈ P, bits.length = n)
    (threshold : 2 ^ (ell + 2 * e) ≤ P.card)
    (test : Finset ((AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) × (Fin ell → ZMod 2))) :
    |seededTestProb (fun bits : P => decodedOneShotExtractor n ell e bits.val) test -
      uniformSeededTestProb test| ≤ ((2 : ℝ) ^ e)⁻¹ := by
  change |seededTestProb (fun bits : P => fun seeds =>
    decodedOneShotExtractor n ell e bits.val seeds) test - uniformSeededTestProb test| ≤ _
  simpa only [decodedOneShotExtractor_eq_composition] using
    oneShot_composition_flat n ell e P source threshold test

end Algebraic.Cutwidth.Extractor.Internal
