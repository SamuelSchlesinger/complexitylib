/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Frobenius.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Encoding.BitPolynomial.Frobenius.Internal
import Complexitylib.Classes.P.BitPolynomial
import Complexitylib.Classes.P.BitPolynomial.Remainder
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Uniform polynomial-time modular Frobenius

Registered multiplication and remainder certificates implement one guarded
squaring step. A fold runs that step once per runtime count bit. The modulus
is a runtime workspace, and every fold state is bounded by its input length,
including when it represents zero. Thus the proof uses one uniform program
and never expands an unreduced exponentially large power.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

private theorem frobeniusStep_mem_FP :
    (fun z => frobeniusStep (pairFst z) (pairSnd z)) ∈ FP := by
  have computation : (fun z => if significantLength (pairFst z) = 0 then [] else
      remainderEval (pair (mulEval (pair (pairSnd z) (pairSnd z))) (pairFst z))) ∈ FP := by
    polytime
  refine mem_FP_of_eq computation fun z => ?_
  simp only [BitPolynomial.remainderEval_pair, BitPolynomial.mulEval_pair, frobeniusStep]

theorem frobeniusEval_mem_FP : frobeniusEval ∈ FP := by
  have hstep : (fun w =>
      frobeniusStep (pairFst (pairFst w)) (pairSnd (pairFst w))) ∈ FP := by
    have hstep := frobeniusStep_mem_FP
    polytime
  have hinitial : (fun z => if significantLength (pairSnd (pairFst z)) = 0 then [] else
      remainderEval (pairFst z)) ∈ FP := by polytime
  unfold frobeniusEval
  refine recFold_mem_FP_of_bound
    (g := fun z count => frobeniusBits (pairFst (pairFst z)) (pairSnd (pairFst z)) count)
    (w := fun z => pairSnd (pairFst z)) (s := pairSnd)
    (A := fun w => frobeniusStep (pairFst (pairFst w)) (pairSnd (pairFst w)))
    (B := fun w => frobeniusStep (pairFst (pairFst w)) (pairSnd (pairFst w)))
    (E := fun z => if significantLength (pairSnd (pairFst z)) = 0 then [] else
      remainderEval (pairFst z))
    hstep hstep hinitial (by polytime) (by polytime)
    (by intro z; rfl) ?_ ?_ PolyBound.id ?_
  · intro z count
    simp only [frobeniusBits, pairFst_pair, pairSnd_pair]
  · intro z count
    simp only [frobeniusBits, pairFst_pair, pairSnd_pair]
  · intro z count _
    exact (frobeniusBits_length_le _ _ _).trans
      ((pairSnd_length_le (pairFst z)).trans (pairFst_length_le z))

end BitPolynomial.Internal
end Complexity
