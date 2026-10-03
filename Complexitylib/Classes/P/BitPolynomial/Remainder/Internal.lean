/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Remainder.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal
import Complexitylib.Encoding.BitPolynomial.Remainder.Internal.Width
import Complexitylib.Classes.P.Iterate
import Complexitylib.Tactic.PolyTime

/-!
# Uniform polynomial-time binary remainder

A bounded maximum finds the modulus's significant length. Each long-division
step reads and combines individual bits, and a bounded fold runs those steps
from high coefficients to low coefficients. Every state has at most the
modulus's input length, including the degree-zero case.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem significantLength_unary : UnaryFn significantLength := by
  have hbody : UnaryFn fun w =>
      if (pairFst w)[(pairSnd w).length]?.getD false then (pairSnd w).length + 1 else 0 := by
    polytime
  refine ((UnaryFn.length id_mem_FP).bmax hbody).of_eq fun z => ?_
  simp only [significantLength, pairFst_pair, pairSnd_pair, List.length_replicate, id_eq]

private theorem xor_bit_mem_FP {f g : List Bool → Bool}
    (hf : (fun z => [f z]) ∈ FP) (hg : (fun z => [g z]) ∈ FP) :
    (fun z => [Bool.xor (f z) (g z)]) ∈ FP := by
  have hp := FPPred.of_flag hf
  have hq := FPPred.of_flag hg
  refine mem_FP_of_eq ((hp.and hq.not).or (hp.not.and hq)).flag_mem_FP fun z => ?_
  cases f z <;> cases g z <;> simp

private theorem remainderStep_mem_FP (bit : Bool) :
    (fun z => remainderStep (pairFst z) bit (pairSnd z)) ∈ FP := by
  have hwidth := significantLength_unary
  have hlen : UnaryFn fun z => significantLength (pairFst z) - 1 := by polytime
  have hfirst : (fun w =>
      [((bit :: pairSnd (pairFst w))[(pairSnd w).length]?.getD false)]) ∈ FP := by
    polytime
  have htop : (fun w =>
      [((bit :: pairSnd (pairFst w))[significantLength (pairFst (pairFst w)) - 1]?.getD
        false)]) ∈ FP := by polytime
  have hmod : (fun w => [(pairFst (pairFst w))[(pairSnd w).length]?.getD false]) ∈ FP := by
    polytime
  have hand : (fun w =>
      [((bit :: pairSnd (pairFst w))[significantLength (pairFst (pairFst w)) - 1]?.getD false)
        && (pairFst (pairFst w))[(pairSnd w).length]?.getD false]) ∈ FP :=
    mem_FP_of_eq ((FPPred.of_flag htop).and (FPPred.of_flag hmod)).flag_mem_FP
      fun w => by simp
  refine bitwise_mem_FP hlen.mem_FP (xor_bit_mem_FP hfirst hand) ?_
  intro z i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

private theorem remainderScan_mem_FP :
    (fun z => remainderScan (pairSnd z) (pairFst z)) ∈ FP := by
  have hwidth := significantLength_unary
  have hstep (bit : Bool) :
      (fun w => remainderStep (pairFst (pairFst w)) bit (pairSnd (pairFst w))) ∈ FP := by
    have hstep := remainderStep_mem_FP bit
    polytime
  refine recFold_mem_FP_of_bound
    (g := fun z a => remainderScan (pairSnd z) a)
    (w := pairSnd) (s := pairFst)
    (A := fun w => remainderStep (pairFst (pairFst w)) false (pairSnd (pairFst w)))
    (B := fun w => remainderStep (pairFst (pairFst w)) true (pairSnd (pairFst w)))
    (E := fun z => List.replicate (significantLength (pairSnd z) - 1) false)
    (hstep false) (hstep true) (by polytime) (by polytime) (by polytime)
    (by intro z; rfl) ?_ ?_ (PolyBound.id) ?_
  · intro z a
    simp only [remainderScan, pairFst_pair, pairSnd_pair]
  · intro z a
    simp only [remainderScan, pairFst_pair, pairSnd_pair]
  · intro z a _
    rw [remainderScan_length]
    exact (Nat.sub_le _ _).trans ((significantLength_le _).trans (pairSnd_length_le z))

theorem remainderEval_mem_FP : remainderEval ∈ FP := by
  have hwidth := significantLength_unary
  have hscan := remainderScan_mem_FP
  unfold remainderEval remainderBits
  polytime

end BitPolynomial.Internal
end Complexity
