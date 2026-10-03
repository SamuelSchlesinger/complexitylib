/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Trinomial.Defs
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
import Complexitylib.Classes.P.Range
import Complexitylib.Tactic.PolyTime

/-!
# Polynomial-time sparse trinomial generation

The output length and three position tests are unary arithmetic functions.
The bitwise closure assembles their flags into the coefficient list.
-/

public section

namespace Complexity
namespace BitPolynomial.Internal

theorem trinomialEval_mem_FP : trinomialEval ∈ FP := by
  have hlen : UnaryFn fun z => 2 * z.length + 1 := by polytime
  have input : UnaryFn fun w => (pairFst w).length := by polytime
  have hbit := ((FPPred.eq UnaryFn.index (UnaryFn.const 0)).or
    ((FPPred.eq UnaryFn.index input).or
      (FPPred.eq UnaryFn.index ((UnaryFn.const 2).mul input)))).flag_mem_FP
  refine bitwise_mem_FP hlen.mem_FP hbit ?_
  intro z i
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]

theorem trinomialBits_mem_FP {d : List Bool → Nat} (hd : UnaryFn d) :
    (fun z => trinomialBits (d z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp hd.mem_FP trinomialEval_mem_FP)
    fun z => by simp only [Function.comp_apply, trinomialEval, List.length_replicate]

theorem roundedTrinomialEval_mem_FP : roundedTrinomialEval ∈ FP :=
  trinomialBits_mem_FP (by polytime)

end BitPolynomial.Internal
end Complexity
