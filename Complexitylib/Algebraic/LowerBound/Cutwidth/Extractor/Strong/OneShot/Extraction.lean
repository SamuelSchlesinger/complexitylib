/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Defs
public import Mathlib.Data.Fintype.Pi
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Extraction.Internal

/-!
# One round of explicit condensation and strong extraction

The actual one-shot bit program extracts `ell` output bits with error at
most `2^(-e)` from every flat `n`-bit support of size at least
`2^(ell+2*e)`. Every final statistical test retains both independent field
seeds. The program's output is read at canonical seed encodings; these
encodings range over every element of the two proved finite binary fields.

The selected condenser and universal binary hash each contribute error
`2^(-(e+1))`. Their combination uses the finite mixture version of the
condense-then-extract argument of Guruswami--Umans--Vadhan,
Proposition 4.5 and Remark 5.15, together with the retained-seed leftover-hash
lemma in Section 5.1 of
<https://people.seas.harvard.edu/~salil/research/PVcondenser-jacm.pdf>.
The concrete parameter choice and binary runtime identification are proved
in the accompanying Parameters and Correctness modules.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual one-shot evaluator strongly extracts from every qualifying
finite flat support, retaining both independent seeds in every test. -/
theorem decodedOneShotExtractor_flat (n ell e : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (P : Finset (List Bool)) (source : ∀ bits ∈ P, bits.length = n)
    (threshold : 2 ^ (ell + 2 * e) ≤ P.card)
    (test : Finset ((AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
      AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) × (Fin ell → ZMod 2))) :
    |seededTestProb (fun bits : P => decodedOneShotExtractor n ell e bits.val) test -
      uniformSeededTestProb test| ≤ ((2 : ℝ) ^ e)⁻¹ :=
  Internal.decodedOneShotExtractor_flat n ell e P source threshold test

end Algebraic.Cutwidth.Extractor
