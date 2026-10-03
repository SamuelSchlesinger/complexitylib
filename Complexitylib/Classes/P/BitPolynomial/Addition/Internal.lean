/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Addition.Defs
public import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.Range
import Complexitylib.Classes.P.StringAccess
import Complexitylib.Tactic.PolyTime

/-!
# Polynomial-time padded XOR

A bounded bitwise map runs over the larger operand length. Two runtime bit
reads and Boolean connectives implement each output XOR.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem addEval_mem_FP : addEval ∈ FP := by
  have ha : (fun w => pairFst (pairFst w)) ∈ FP := by polytime
  have hb : (fun w => pairSnd (pairFst w)) ∈ FP := by polytime
  have pa := FPPred.getBit ha UnaryFn.index
  have pb := FPPred.getBit hb UnaryFn.index
  have xor := ((pa.and pb.not).or (pa.not.and pb)).flag_mem_FP
  have width : UnaryFn fun z => max (pairFst z).length (pairSnd z).length := by
    polytime
  refine bitwise_mem_FP width.mem_FP xor ?_
  intro z i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  cases (pairFst z)[i]?.getD false <;> cases (pairSnd z)[i]?.getD false <;> rfl

end BitPolynomial.Internal
end Complexity
