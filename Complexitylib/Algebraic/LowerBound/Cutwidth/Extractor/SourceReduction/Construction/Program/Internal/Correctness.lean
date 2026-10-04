/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Program.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Construction.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Sampler.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.SourceReduction.Encoding
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.CorrelationBreaker.Affine.Program
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Majority

/-!
# Exact computation of the finite source reduction

Binary enumeration supplies the semantic sampler indices and advice.
Every candidate call is the first bit of the same selected affine breaker.
The two list loops agree with finite-vector XOR and majority in the
specified order. Only the sampler's growing guard is needed for this
execution identity; the affine program discharges its own chooser guards.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

private theorem affineTestBit_runtime (n C a target : Nat) (x : Fin n → Bool)
    (y : Fin (affineTestSeedBits n C a target) → Bool)
    (advice : List Bool) (length : advice.length = a) :
    (affineCorrelationBreakerSelectedRuntime (4 * C - 1) target
      (List.ofFn x) (List.ofFn y) advice)[0]?.getD false =
        affineTestBit n C a target x y advice := by
  subst a
  have program := congrArg (fun bits : List Bool => bits[0]?.getD false)
    (affineCorrelationBreakerSelectedRuntime_eq n (4 * C - 1) target advice x y)
  apply program.trans
  change (List.ofFn (affineTestBreaker n C advice.length target x y advice))[0]?.getD false = _
  have positive : 0 < affineTestOutputBits n C advice.length target :=
    (affineTestFirst n C advice.length target).isLt
  simp only [List.getElem?_ofFn, positive, dite_eq_left, Option.getD_some]
  rfl

theorem sourceReductionCallRuntime_eq (n L : Nat)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool)
    (i : Fin (sourceReductionOuterCount (matchedBlockSeedBits L)))
    (z : Fin (sourceReductionCandidateCount (matchedBlockSeedBits L))) :
    sourceReductionCallRuntime L (sourceReductionCandidateCount (matchedBlockSeedBits L))
        (List.ofFn x) i.val z.val =
      affineTestBit n (sourceReductionCandidateCount (matchedBlockSeedBits L))
        (sourceReductionAdviceLength (matchedBlockSeedBits L))
        (sourceReductionTarget (matchedBlockSeedBits L)) x (sourceReductionSampler n L x i z)
        (sourceReductionAdvice (sourceReductionOuterBits (matchedBlockSeedBits L))
          (sourceReductionCandidateBits (matchedBlockSeedBits L)) (i, z)) := by
  have canonical := amplifiedMatchedSamplerRuntime_eq_amplifiedMatchedSampler n L
    (sourceReductionSeedBits n L) base x
    (sourceReductionIndexWord (sourceReductionOuterBits (matchedBlockSeedBits L)) i)
    (sourceReductionIndexWord (sourceReductionCandidateBits (matchedBlockSeedBits L)) z)
  have reindexed := congrArg₂ (amplifiedMatchedSamplerRuntime L
      (sourceReductionSeedBits n L) (List.ofFn x))
    (sourceReductionIndexWord_ofFn (sourceReductionOuterBits (matchedBlockSeedBits L)) i).symm
    (sourceReductionIndexWord_ofFn (sourceReductionCandidateBits (matchedBlockSeedBits L)) z).symm
  have sample := reindexed.trans canonical
  unfold sourceReductionCallRuntime
  dsimp only
  rw [List.length_ofFn]
  change (affineCorrelationBreakerSelectedRuntime
    (4 * sourceReductionCandidateCount (matchedBlockSeedBits L) - 1)
    (sourceReductionTarget (matchedBlockSeedBits L)) (List.ofFn x)
    (amplifiedMatchedSamplerRuntime L (sourceReductionSeedBits n L) (List.ofFn x)
      (Nat.toBitsLE (sourceReductionOuterBits (matchedBlockSeedBits L)) i.val)
      (Nat.toBitsLE (sourceReductionCandidateBits (matchedBlockSeedBits L)) z.val))
    (sourceReductionAdvice (sourceReductionOuterBits (matchedBlockSeedBits L))
      (sourceReductionCandidateBits (matchedBlockSeedBits L)) (i, z)))[0]?.getD false = _
  rw [sample]
  apply affineTestBit_runtime
  exact sourceReductionAdvice_length _ _ _

private theorem xor_ofFn {N : Nat} (f : Fin N → Bool) :
    (List.ofFn f).foldr Bool.xor false = Complexity.Schnorr.xorBool N f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.ofFn_succ, List.foldr_cons, ih]
    rfl

theorem sourceReductionCandidatesRuntime_eq (n L : Nat)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool)
    (i : Fin (sourceReductionOuterCount (matchedBlockSeedBits L))) :
    sourceReductionCandidatesRuntime L (sourceReductionCandidateCount (matchedBlockSeedBits L))
        (List.ofFn x) i.val =
      List.ofFn fun z => affineTestBit n
        (sourceReductionCandidateCount (matchedBlockSeedBits L))
        (sourceReductionAdviceLength (matchedBlockSeedBits L))
        (sourceReductionTarget (matchedBlockSeedBits L)) x (sourceReductionSampler n L x i z)
        (sourceReductionAdvice (sourceReductionOuterBits (matchedBlockSeedBits L))
          (sourceReductionCandidateBits (matchedBlockSeedBits L)) (i, z)) := by
  apply List.ext_getElem
  · simp only [sourceReductionCandidatesRuntime, List.length_map, List.length_range,
      List.length_ofFn]
  · intro j hj hk
    simp only [sourceReductionCandidatesRuntime, List.getElem_map, List.getElem_range,
      List.getElem_ofFn]
    exact sourceReductionCallRuntime_eq n L base x i ⟨j, by simpa using hk⟩

theorem sourceReductionRowsRuntime_eq (n L : Nat)
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionRowsRuntime L (sourceReductionOuterCount (matchedBlockSeedBits L))
        (sourceReductionCandidateCount (matchedBlockSeedBits L)) (List.ofFn x) =
      List.ofFn (sourceReductionOutput n L x) := by
  apply List.ext_getElem
  · simp only [sourceReductionRowsRuntime, List.length_map, List.length_range, List.length_ofFn]
  · intro i hi hj
    simp only [sourceReductionRowsRuntime, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [sourceReductionCandidatesRuntime_eq n L base x ⟨i, by simpa using hj⟩, xor_ofFn]
    rfl

theorem sourceReductionRuntime_eq (n L N C : Nat)
    (outer : N = sourceReductionOuterCount (matchedBlockSeedBits L))
    (candidates : C = sourceReductionCandidateCount (matchedBlockSeedBits L))
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionRuntime L N C (List.ofFn x) = [sourceReductionExtractor n L x] := by
  rw [outer, candidates, sourceReductionRuntime, sourceReductionRowsRuntime_eq n L base x]
  exact majorityEval_toList (sourceReductionOutput n L x)

open Complexity in
theorem sourceReductionEval_eq (n L N C : Nat)
    (outer : N = sourceReductionOuterCount (matchedBlockSeedBits L))
    (candidates : C = sourceReductionCandidateCount (matchedBlockSeedBits L))
    (base : GrowingMatchedBlockRuntimeValid n (sourceReductionSeedBits n L) L 4)
    (x : Fin n → Bool) :
    sourceReductionEval (pair (List.ofFn x) (pair (List.replicate L true)
      (pair (List.replicate N true) (List.replicate C true)))) =
      [sourceReductionExtractor n L x] := by
  simp only [sourceReductionEval, pairFst_pair, pairSnd_pair, List.length_replicate]
  exact sourceReductionRuntime_eq n L N C outer candidates base x

end Algebraic.Cutwidth.Extractor.Internal
