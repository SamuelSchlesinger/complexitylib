/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Encoding.BitPolynomial.Transpose
public import Complexitylib.Tactic.PolyTime.Init
import Complexitylib.Classes.P.BitPolynomial.Transpose.Internal

/-!
# Uniform polynomial-time coefficient packing by transposition

One evaluator handles runtime binary matrices with two runtime unary dimensions.
Missing input entries are false; excess entries are ignored. Zero dimensions
and malformed paired inputs follow the total list and projection conventions.
Both the encoded evaluator and the rule for computed dimensions and matrices
are registered for polynomial-time composition.
-/

public section

namespace Complexity
namespace BitPolynomial

/-- Matrix transposition with runtime unary dimensions is uniformly polynomial-time. -/
@[polytime] theorem transposeEval_mem_FP : transposeEval ∈ FP :=
  Internal.transposeEval_mem_FP

/-- Polynomial-time unary dimensions and a computed matrix may be supplied directly. -/
@[polytime] theorem transposeBits_mem_FP {rows cols : List Bool → Nat}
    {bits : List Bool → List Bool} (hrows : UnaryFn rows) (hcols : UnaryFn cols)
    (hbits : bits ∈ FP) : (fun z => transposeBits (rows z) (cols z) (bits z)) ∈ FP :=
  Internal.transposeBits_mem_FP hrows hcols hbits

end BitPolynomial
end Complexity
