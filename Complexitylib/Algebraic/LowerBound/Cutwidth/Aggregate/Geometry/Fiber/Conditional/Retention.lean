/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Shared.Parameters

/-!
# Upper bound for the common retention fraction

A receiving side can only discard designated triples. Its exact retention fraction
lies below one, allowing the disjoint-pair savings to use the same multiplier.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional

/-- The common receiving-side retention factor never exceeds one. -/
theorem receiverRetention_le_one {n k : ℕ} (range : k + 4 ≤ n) :
    Shared.receiverRetention n k ≤ 1 := by
  have hn : (3 : ℝ) < n := by exact_mod_cast (by lia : 3 < n)
  have hk : (k : ℝ) + 4 ≤ n := by exact_mod_cast range
  have den : 0 < (n : ℝ) * (n - 1) * (n - 2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  unfold Shared.receiverRetention
  apply (div_le_iff₀ den).mpr
  rw [one_mul]
  gcongr <;> nlinarith

end Algebraic.Cutwidth.Aggregate.Geometry.Fiber.Conditional
