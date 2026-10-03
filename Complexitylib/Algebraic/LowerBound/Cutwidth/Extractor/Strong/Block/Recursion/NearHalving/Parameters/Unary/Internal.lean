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
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Condenser.Parameters.Explicit.Unary
import Complexitylib.Classes.P.Unary

/-!
# Total unary computation of the rounded Gamma parameters

The selected depth never exceeds the binary floor logarithm. Its power of
two therefore fits the unary bound `b+1`, even when the size guard fails.
Bounded powering and arithmetic certify every parameter without a promise.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Complexity

theorem gammaBlockDepth_pow_le (b : Nat) : 2 ^ gammaBlockDepth b ≤ b + 1 := by
  by_cases zero : b = 0
  · simp [gammaBlockDepth, zero]
  have depth : gammaBlockDepth b ≤ Nat.log 2 b := by
    unfold gammaBlockDepth
    exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  calc
    _ ≤ 2 ^ Nat.log 2 b := Nat.pow_le_pow_right (by decide) depth
    _ ≤ b := Nat.pow_log_le_self 2 zero
    _ ≤ b + 1 := Nat.le_succ b

variable {b h : List Bool → Nat}

theorem gammaBlockLog_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockLog (b z) :=
  (UnaryFn.const 2).clog (hb.add (UnaryFn.const 1))

theorem gammaBlockDepth_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockDepth (b z) :=
  (((UnaryFn.const 2).log hb).sub ((UnaryFn.const 3).mul
    ((UnaryFn.const 2).clog ((gammaBlockLog_unaryFn hb).add (UnaryFn.const 1))))).sub
      (UnaryFn.const 15)

theorem gammaBlockDepth_pow_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => 2 ^ gammaBlockDepth (b z) :=
  (UnaryFn.const 2).pow_of_le (gammaBlockDepth_unaryFn hb) (hb.add (UnaryFn.const 1))
    fun z => gammaBlockDepth_pow_le (b z)

theorem gammaBlockErrorExponent_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockErrorExponent (b z) :=
  (gammaBlockDepth_unaryFn hb).add (UnaryFn.const 4)

theorem gammaBlockOutputQuantum_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockOutputQuantum (b z) :=
  (gammaBlockDepth_pow_unaryFn hb).mul
    (((UnaryFn.const 8).mul (gammaBlockDepth_unaryFn hb)).add (UnaryFn.const 7))

theorem gammaBlockReserve_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockReserve (b z) :=
  condenserCoordinates_unaryFn hb (gammaBlockOutputQuantum_unaryFn hb)

theorem gammaBlockLeafLength_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockLeafLength (b z) :=
  (((UnaryFn.const 8).mul (gammaBlockDepth_unaryFn hb)).add (UnaryFn.const 7)).mul
    (gammaBlockReserve_unaryFn hb)

theorem gammaBlockInputEntropy_unaryFn (hb : UnaryFn b) :
    UnaryFn fun z => gammaBlockInputEntropy (b z) :=
  ((gammaBlockDepth_pow_unaryFn hb).mul
    (((UnaryFn.const 9).mul (gammaBlockDepth_unaryFn hb)).add (UnaryFn.const 8))).mul
      (gammaBlockReserve_unaryFn hb)

theorem gammaBlockSizeGuard_fpPred (hb : UnaryFn b) :
    FPPred fun z => GammaBlockSizeGuard (b z) :=
  FPPred.le (((UnaryFn.const 3).mul
    ((UnaryFn.const 2).clog ((gammaBlockLog_unaryFn hb).add (UnaryFn.const 1)))).add
      (UnaryFn.const 15)) ((UnaryFn.const 2).log hb)

theorem nearHalvingBlockRate_unaryFn (hh : UnaryFn h) :
    UnaryFn fun z => nearHalvingBlockRate (h z) :=
  (UnaryFn.const 16).mul (hh.add (UnaryFn.const 1))

end Algebraic.Cutwidth.Extractor.Internal
