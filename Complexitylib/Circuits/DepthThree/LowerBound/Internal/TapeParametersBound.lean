/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeParameters
public import Complexitylib.Circuits.DepthThree.LowerBound.Internal.TapeParameterCost

/-!
# Unrestricted depth-three lower bound: tape parameters bound

Adapted from OpenAI's formalization at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Source: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DepthThree/TapeParametersBound.lean

Imports, namespaces, module visibility, documentation, and formatting are adapted
for complexitylib. The source theorem statements and mathematical proofs are retained.
-/

@[expose] public section

namespace Complexity

namespace DepthThreeLowerBound
namespace TapeParameters

theorem cost_le (n : ℕ) : cost n ≤ 600 * (n + 3) ^ 8 := by
  have hd : dataDimension n ≤ n := Nat.div_le_self n 5
  have hbase : (dataDimension n + 3) ^ 8 ≤ (n + 3) ^ 8 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hd 3) 8
  have hc := Nat.le_trans (TapeParameterCost.cube_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hs := Nat.le_trans (TapeParameterCost.sixth_cost (dataDimension n))
    (Nat.mul_le_mul_left 200 hbase)
  have hpbase : (dataDimension n + 1) ^ 7 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n + 1 ≤ n + 3) 7)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 7 ≤ 8))
  have hp := Nat.le_trans (TapeParameterCost.power_cost (by decide : 2 ≤ 6)
    (dataDimension n)) (Nat.mul_le_mul_left 108 hpbase)
  have hn : n ≤ (n + 3) ^ 8 := by
    calc
      n ≤ n + 3 := by omega
      _ = (n + 3) ^ 1 := by simp
      _ ≤ (n + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hd2 : (dataDimension n) ^ 2 ≤ (n + 3) ^ 8 :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega : dataDimension n ≤ n + 3) 2)
      (Nat.pow_le_pow_right (by omega : 0 < n + 3) (by decide : 2 ≤ 8))
  have hpos : 1 ≤ (n + 3) ^ 8 := Nat.pow_pos (by omega)
  unfold cost
  omega

end TapeParameters
end DepthThreeLowerBound

end Complexity
