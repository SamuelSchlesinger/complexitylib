/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.OneShot.Weighted
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Extraction

/-!
# The one-shot extractor on blocks with shared field seeds

Apply the actual decoded one-shot program to every block, reusing its pair
of independent field seeds across all blocks. At threshold `2^(ell+2*e)`
per source block, the joint seed-output test error is at most `t * 2^(-e)`
against uniform `t`-tuples of `ell`-bit outputs. The seed pair is retained
once in every test.

This supplies a concrete statistical leaf for the shared-seed block
argument of Chattopadhyay--Goodman--Liao, Lemma 5.5, using the checked
one-shot program: <https://eccc.weizmann.ac.il/report/2021/075/>.
`OneShot.Block.Program` supplies the encoded runtime loop and its exact tuple semantics.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- The actual one-shot program extracts from all encoded source blocks
with one shared seed pair and total error at most the sum of the block errors. -/
theorem decodedOneShotExtractor_block (n ell e : Nat) {α : Type*} [Fintype α]
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    (input : α ↪ List Bool) (sourceLength : ∀ x, (input x).length = n)
    {t : Nat} {p : (Fin t → α) → ℝ} (source : IsBlockSource p (2 ^ (ell + 2 * e)))
    (T : Finset ((AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
        AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) ×
      (Fin t → Fin ell → ZMod 2))) :
    |weightedSeededTestProb p
        (fun x seeds i => decodedOneShotExtractor n ell e (input (x i)) seeds) T -
      uniformSeededTestProb T| ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
  (decodedOneShotExtractor_weightedStrongSeededExtractor n ell e input sourceLength).block source T

/-- Arbitrarily dependent blocks of `n` Boolean coordinates share one
one-shot seed pair, with joint test error at most `t * 2^(-e)`. -/
theorem decodedOneShotExtractor_block_ofFn (n ell e : Nat)
    [Fintype (AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)))]
    [Fintype (AdjoinRoot (binaryModulus (oneShotHashExponent n ell e)))]
    {t : Nat} {p : (Fin t → (Fin n → Bool)) → ℝ}
    (source : IsBlockSource p (2 ^ (ell + 2 * e)))
    (T : Finset ((AdjoinRoot (binaryModulus (oneShotCondenserExponent n ell e)) ×
        AdjoinRoot (binaryModulus (oneShotHashExponent n ell e))) ×
      (Fin t → Fin ell → ZMod 2))) :
    |weightedSeededTestProb p
        (fun x seeds i => decodedOneShotExtractor n ell e (List.ofFn (x i)) seeds) T -
      uniformSeededTestProb T| ≤ (t : ℝ) * ((2 : ℝ) ^ e)⁻¹ :=
  (decodedOneShotExtractor_ofFn_weighted n ell e).block source T

end Algebraic.Cutwidth.Extractor
