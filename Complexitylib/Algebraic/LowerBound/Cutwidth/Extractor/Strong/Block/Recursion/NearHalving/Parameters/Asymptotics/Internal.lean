/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.NearHalving.Parameters.Explicit.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Recursion.Scheduled.Asymptotics

/-!
# Eventual validity of the rounded depth choice

The existing ceiling-logarithmic depth estimate, with a fixed multiplier
nineteen, absorbs both three iterated logarithms and the fifteen-bit offset.
The resulting guard makes the natural subtraction in the selected depth
exact at all sufficiently large target lengths.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

open Filter

theorem eventually_gammaBlockSizeGuard : ∀ᶠ b : Nat in atTop, GammaBlockSizeGuard b := by
  filter_upwards [eventually_polylogBlockDepth_le 19, eventually_ge_atTop 1]
    with b depth positive
  change 19 * Nat.clog 2 (gammaBlockLog b + 1) ≤ gammaBlockLog b at depth
  have ceiling : gammaBlockLog b ≤ Nat.log 2 b + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide) b)
  have logPositive : 0 < gammaBlockLog b := Nat.clog_pos (by decide) (by lia)
  have iteratedPositive : 0 < Nat.clog 2 (gammaBlockLog b + 1) :=
    Nat.clog_pos (by decide) (by lia)
  unfold GammaBlockSizeGuard
  lia

end Algebraic.Cutwidth.Extractor.Internal
