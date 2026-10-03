/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Defs
public import Complexitylib.Classes.P.Unary.Defs
public import Complexitylib.Tactic.PolyTime.Init
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Unary.Internal

/-!
# Uniform unary generation of the rounded Gamma parameters

Every selected parameter is polynomial-time in its unary input, including
the actual block count `2^depth`. The unconditional bound `2^depth <= b+1`
permits bounded powering on all inputs. The size guard also has a
polynomial-time decision algorithm; none of these certificates assumes it.

These statements generate parameters. They do not certify a recursive
extractor evaluator or generate its recursively varying total seed length.
-/

public section

namespace Algebraic.Cutwidth.Extractor

open Complexity

/-- The selected block count has a unary bound on every input. -/
theorem gammaBlockDepth_pow_le (b : Nat) : 2 ^ gammaBlockDepth b ≤ b + 1 :=
  Internal.gammaBlockDepth_pow_le b

variable {b h : List Bool → Nat}

/-- The ceiling input logarithm can be generated in unary in polynomial time. -/
@[polytime] theorem gammaBlockLog_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockLog (b z) :=
  Internal.gammaBlockLog_unaryFn hb

/-- The total depth formula uses polynomial-time logarithms and subtraction. -/
@[polytime] theorem gammaBlockDepth_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockDepth (b z) :=
  Internal.gammaBlockDepth_unaryFn hb

/-- The actual block count is polynomial-time by bounded powering. -/
@[polytime] theorem gammaBlockDepth_pow_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => 2 ^ gammaBlockDepth (b z) :=
  Internal.gammaBlockDepth_pow_unaryFn hb

/-- The common error exponent is polynomial-time in unary. -/
@[polytime] theorem gammaBlockErrorExponent_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockErrorExponent (b z) :=
  Internal.gammaBlockErrorExponent_unaryFn hb

/-- The complete output quantum is polynomial-time in unary. -/
@[polytime] theorem gammaBlockOutputQuantum_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockOutputQuantum (b z) :=
  Internal.gammaBlockOutputQuantum_unaryFn hb

/-- Ceiling division generates the selected reserve on all inputs. -/
@[polytime] theorem gammaBlockReserve_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockReserve (b z) :=
  Internal.gammaBlockReserve_unaryFn hb

/-- The final leaf output length is polynomial-time in unary. -/
@[polytime] theorem gammaBlockLeafLength_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockLeafLength (b z) :=
  Internal.gammaBlockLeafLength_unaryFn hb

/-- The actual selected input entropy is polynomial-time in unary. -/
@[polytime] theorem gammaBlockInputEntropy_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockInputEntropy (b z) :=
  Internal.gammaBlockInputEntropy_unaryFn hb

/-- The size guard has a total polynomial-time decision algorithm. -/
@[polytime] theorem gammaBlockSizeGuard_fpPred (hb : UnaryFn b) :
    FPPred fun z => GammaBlockSizeGuard (b z) :=
  Internal.gammaBlockSizeGuard_fpPred hb

/-- The rate required by the near-halving schedule is polynomial-time in unary. -/
@[polytime] theorem nearHalvingBlockRate_unaryFn (hh : UnaryFn h) :
    UnaryFn fun z => nearHalvingBlockRate (h z) :=
  Internal.nearHalvingBlockRate_unaryFn hh

end Algebraic.Cutwidth.Extractor
