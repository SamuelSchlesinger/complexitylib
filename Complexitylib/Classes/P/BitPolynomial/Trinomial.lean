/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.BitPolynomial.Trinomial
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Trinomial.Internal

/-!
# A uniform polynomial-time generator for sparse binary trinomials

The generator accepts a unary half-degree and writes all coefficients of
`X^(2*d) + X^d + 1`. Its input bit values do not matter. The certificate
does not assume irreducibility and is valid uniformly at every input length.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Generating the sparse coefficient list is uniformly polynomial-time. -/
@[polytime] theorem trinomialEval_mem_FP : trinomialEval ∈ FP :=
  Internal.trinomialEval_mem_FP

/-- A polynomial-time unary half-degree can be used directly by the generator. -/
@[polytime] theorem trinomialBits_mem_FP {d : List Bool → Nat} (hd : UnaryFn d) :
    (fun z => trinomialBits (d z)) ∈ FP :=
  Internal.trinomialBits_mem_FP hd

/-- Rounding the requested half-degree to a power of three preserves polynomial time. -/
@[polytime] theorem roundedTrinomialEval_mem_FP : roundedTrinomialEval ∈ FP :=
  Internal.roundedTrinomialEval_mem_FP

end BitPolynomial
end Complexity
