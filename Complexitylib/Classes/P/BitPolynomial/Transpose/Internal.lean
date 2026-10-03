/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Transpose.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Encoding.BitPolynomial.Transpose
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Polynomial-time binary matrix transposition

Both runtime dimensions are unary lengths. Their product bounds the output,
and division and remainder compute each transposed index in polynomial time.
A bounded bitwise map reads the corresponding input bit, with false past its end.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem transposeEval_mem_FP : transposeEval ∈ FP := by
  have hbits : (fun w => pairFst (pairFst (pairFst w))) ∈ FP := by polytime
  have hindex : UnaryFn fun w =>
      ((pairSnd w).length % (pairSnd (pairFst (pairFst w))).length) *
        (pairSnd (pairFst w)).length +
      (pairSnd w).length / (pairSnd (pairFst (pairFst w))).length := by
    polytime
  have hlen : UnaryFn fun z => (pairSnd (pairFst z)).length * (pairSnd z).length := by
    polytime
  refine bitwise_mem_FP hlen.mem_FP (getBit_mem_FP hbits hindex) ?_
  intro z k
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

theorem transposeBits_mem_FP {rows cols : List Bool → Nat} {bits : List Bool → List Bool}
    (hrows : UnaryFn rows) (hcols : UnaryFn cols) (hbits : bits ∈ FP) :
    (fun z => transposeBits (rows z) (cols z) (bits z)) ∈ FP := by
  have encoded : (fun z => pair (pair (bits z) (List.replicate (rows z) true))
      (List.replicate (cols z) true)) ∈ FP := by
    polytime
  refine mem_FP_of_eq (mem_FP_comp encoded transposeEval_mem_FP) fun z => ?_
  simp only [Function.comp_apply, BitPolynomial.transposeEval_pair, List.length_replicate]

end BitPolynomial.Internal
end Complexity
