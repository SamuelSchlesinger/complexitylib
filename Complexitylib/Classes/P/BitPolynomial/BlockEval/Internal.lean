/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.BlockEval.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Encoding.BitPolynomial.BlockEval.Internal
import Complexitylib.Classes.P.BitPolynomial
import Complexitylib.Classes.P.BitPolynomial.Addition
import Complexitylib.Classes.P.BitPolynomial.Remainder
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Uniform polynomial-time Horner evaluation of flat blocks

The fold carries one remainder state and keeps the original paired input as
workspace. Runtime word lengths specify the block width and count. Each
step slices the next coefficient with a polynomial-time index, multiplies,
adds, and reduces using registered arithmetic certificates. All states are
bounded by the supplied modulus length.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem blockEval_mem_FP : blockEval ∈ FP := by
  let coeffs := fun z => pairFst (pairFst (pairFst z))
  let width := fun z => (pairSnd (pairFst (pairFst z))).length
  let seed := fun z => pairFst (pairSnd (pairFst z))
  let modulus := fun z => pairSnd (pairSnd (pairFst z))
  let step := fun w =>
    let z := pairFst (pairFst w)
    blockEvalStep
      (coefficientBlock (coeffs z) (width z) ((pairSnd z).length - (pairSnd w).length - 1))
      (seed z) (modulus z) (pairSnd (pairFst w))
  have hstep : step ∈ FP := by
    have computation : (fun w =>
        let z := pairFst (pairFst w)
        if significantLength (modulus z) = 0 then [] else
          remainderEval (pair
            (addEval (pair
              (coefficientBlock (coeffs z) (width z)
                ((pairSnd z).length - (pairSnd w).length - 1))
              (mulEval (pair (seed z) (pairSnd (pairFst w)))))) (modulus z))) ∈ FP := by
      dsimp only [coefficientBlock, coeffs, width, seed, modulus]
      polytime
    refine mem_FP_of_eq computation fun w => ?_
    simp only [step, blockEvalStep, BitPolynomial.remainderEval_pair,
      BitPolynomial.addEval_pair, BitPolynomial.mulEval_pair]
  have initial : (fun z => List.replicate (significantLength (modulus z) - 1) false) ∈ FP := by
    dsimp only [modulus]
    polytime
  change (fun z => blockEvalScan (coeffs z) (width z) (seed z) (modulus z)
    (pairSnd z).length (pairSnd z)) ∈ FP
  refine recFold_mem_FP_of_bound
    (g := fun z count => blockEvalScan (coeffs z) (width z) (seed z) (modulus z)
      (pairSnd z).length count)
    (w := id) (s := pairSnd) (A := step) (B := step)
    (E := fun z => List.replicate (significantLength (modulus z) - 1) false)
    hstep hstep initial id_mem_FP (by polytime)
    (by intro z; rfl) ?_ ?_ PolyBound.id ?_
  · intro z count
    simp only [blockEvalScan, step, id_eq, pairFst_pair, pairSnd_pair]
  · intro z count
    simp only [blockEvalScan, step, id_eq, pairFst_pair, pairSnd_pair]
  · intro z count _
    rw [blockEvalScan_length]
    exact (Nat.sub_le _ _).trans ((BitPolynomial.significantLength_le _).trans
      ((pairSnd_length_le (pairSnd (pairFst z))).trans
        ((pairSnd_length_le (pairFst z)).trans (pairFst_length_le z))))

end BitPolynomial.Internal
end Complexity
