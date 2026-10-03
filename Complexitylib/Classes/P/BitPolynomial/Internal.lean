/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.Pairing
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Classes.P.Range
import Complexitylib.Tactic.PolyTime

/-!
# Uniform polynomial-time carryless multiplication

Each output coefficient counts contributing pairs of input bits and reduces
that count modulo two. The loops run over unary lengths and positions, while
the polynomial coefficients remain binary strings throughout.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

private def coeffCount (a b : List Bool) (k : Nat) : Nat :=
  ((Finset.range a.length).filter fun i =>
    i ≤ k ∧ a[i]?.getD false = true ∧ b[k - i]?.getD false = true).card

private theorem coeffCount_unary :
    UnaryFn fun w => coeffCount (pairFst (pairFst w)) (pairSnd (pairFst w))
      (pairSnd w).length := by
  have ha : (fun v => pairFst (pairFst (pairFst v))) ∈ FP := by polytime
  have hb : (fun v => pairSnd (pairFst (pairFst v))) ∈ FP := by polytime
  have hn : UnaryFn fun w => (pairFst (pairFst w)).length := by polytime
  have hp := (FPPred.le UnaryFn.index UnaryFn.index.lift).and
    ((FPPred.getBit ha UnaryFn.index).and
      (FPPred.getBit hb (UnaryFn.index.lift.sub UnaryFn.index)))
  refine (hn.count hp).of_eq fun w => ?_
  simp only [coeffCount, pairFst_pair, pairSnd_pair, List.length_replicate]

theorem mulEval_mem_FP : mulEval ∈ FP := by
  have hparity := (FPPred.eq (coeffCount_unary.mod (UnaryFn.const 2))
    (UnaryFn.const 1)).flag_mem_FP
  have hlen : UnaryFn fun z => (pairFst z).length + (pairSnd z).length := by polytime
  refine bitwise_mem_FP hlen.mem_FP hparity ?_
  intro x i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate, coeffCount]

end BitPolynomial.Internal
end Complexity
