/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Message.Internal
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.OneWay

/-!
# Exact one-way protocols for signed AND/OR/XOR circuits

The public message consists of one partial aggregate per actual gate and one
optional primary-output bit. It determines the output for every complementary input.
-/

@[expose] public section

namespace Algebraic.Aggregate.Geometry

open Algebraic.Cutwidth

/-- The actual Boolean gate summaries form a one-way protocol. -/
noncomputable def circuitOneWaySummary {n : ℕ} (c : Circuit signature n 1)
    (U : Finset (Fin n)) : Cutwidth.Aggregate.OneWaySummary
      (c.outputFunction interpretation 0) U (Fin (c.size + 1) → Bool) where
  key x := outputKey c.program U (c.outputs 0) (glue U x (fun _ => false))
  rows_eq x y same q := by
    have hx : outputKey c.program U (c.outputs 0) (glue U x q) =
        outputKey c.program U (c.outputs 0) (glue U x (fun _ => false)) := by
      apply outputKey_eq_of_inputs_agree
      intro i hi
      simp [glue, hi]
    have hy : outputKey c.program U (c.outputs 0) (glue U y q) =
        outputKey c.program U (c.outputs 0) (glue U y (fun _ => false)) := by
      apply outputKey_eq_of_inputs_agree
      intro i hi
      simp [glue, hi]
    exact trace_eq_of_outputKey_eq c.program U (c.outputs 0) _ _
      (hx.trans (same.trans hy.symm)) (by intro i hi; simp [glue, hi])

end Algebraic.Aggregate.Geometry
