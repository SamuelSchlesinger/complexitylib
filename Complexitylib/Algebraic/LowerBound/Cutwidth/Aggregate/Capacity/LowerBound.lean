/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.OneWay
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Finite capacity lower bounds for unrestricted aggregate circuits

Primary-input summaries let the receiving party reconstruct every gate in order.
One additional bit handles a designated output that is itself a sending-party input.
The number of special gates, their placement, and their fan-in are unrestricted.

This is a deterministic one-way communication argument. The broader gatewise
communication approach is classical; see Roychowdhury, Orlitsky, and Siu,
*Lower Bounds on Threshold and Related Circuits via Communication Complexity* (1994).
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate

open scoped Classical

variable {J : Type} {State : J → Type}
  [∀ j, CommMonoid (State j)] [∀ j, Fintype (State j)] {n : Nat}

open Algebraic.Aggregate.Capacity

/-- Per-gate primary-input summaries and one output bit form a one-way summary. -/
noncomputable def circuitOneWaySummary
    (c : Circuit (Algebraic.Aggregate.signature State) n 1) (U : Finset (Fin n)) :
    OneWaySummary (c.outputFunction Algebraic.Aggregate.interpretation 0) U
      (OutputKey c.program) where
  key p := outputKey c.program U (c.outputs 0) (glue U p (fun _ => false))
  rows_eq p p' same q := by
    let x := glue U p q
    let y := glue U p' q
    have hx : outputKey c.program U (c.outputs 0) x =
        outputKey c.program U (c.outputs 0) (glue U p (fun _ => false)) := by
      apply outputKey_eq_of_inputs_agree
      intro i hi
      simp [x, glue, hi]
    have hy : outputKey c.program U (c.outputs 0) y =
        outputKey c.program U (c.outputs 0) (glue U p' (fun _ => false)) := by
      apply outputKey_eq_of_inputs_agree
      intro i hi
      simp [y, glue, hi]
    have hk : outputKey c.program U (c.outputs 0) x =
        outputKey c.program U (c.outputs 0) y := hx.trans (same.trans hy.symm)
    have outside : ∀ i, i ∉ U → x i = y i := by
      intro i hi
      simp [x, y, glue, hi]
    change c.program.trace Algebraic.Aggregate.interpretation x (c.outputs 0) =
      c.program.trace Algebraic.Aggregate.interpretation y (c.outputs 0)
    exact trace_eq_of_outputKey_eq c.program U (c.outputs 0) x y hk outside

/-- Jointly encoding all summary registers can improve on rounding each register. -/
theorem input_le_summaryBits_of_circuit
    (c : Circuit (Algebraic.Aggregate.signature State) n 1) {K : Nat}
    (free : RectangleFree (c.outputFunction Algebraic.Aggregate.interpretation 0) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting (c.outputFunction Algebraic.Aggregate.interpretation 0)).card) :
    n ≤ Nat.clog 2 (Fintype.card (OutputKey c.program)) + 2 * Nat.clog 2 K + 5 := by
  by_cases large : Nat.clog 2 K + 3 ≤ n
  · obtain ⟨V, _, hV⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (by simpa using large)
    have right : (Vᶜ)ᶜ.card = Nat.clog 2 K + 3 := by simpa using hV
    exact input_le_capacity_of_oneWay free dense Vᶜ right
      (circuitOneWaySummary c Vᶜ) (Nat.le_pow_clog (by decide) _)
  · lia

/-- Every dense rectangle-free output requires nearly `n` bits of aggregate capacity.
The six-bit constant includes the optional primary-output bit. -/
theorem input_le_capacity_of_circuit
    (c : Circuit (Algebraic.Aggregate.signature State) n 1) {K : Nat}
    (free : RectangleFree (c.outputFunction Algebraic.Aggregate.interpretation 0) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting (c.outputFunction Algebraic.Aggregate.interpretation 0)).card) :
    n ≤ capacity c.program + 2 * Nat.clog 2 K + 6 := by
  have h := input_le_summaryBits_of_circuit c free dense
  have bits := Nat.clog_le_of_le_pow (card_outputKey_le c.program)
  lia

/-- The finite bound also charges the exact logarithm of the joint summary space. -/
theorem input_le_logCard_of_circuit
    (c : Circuit (Algebraic.Aggregate.signature State) n 1) {K : Nat}
    (free : RectangleFree (c.outputFunction Algebraic.Aggregate.interpretation 0) K)
    (dense : 2 ^ (n - 2) ≤
      (accepting (c.outputFunction Algebraic.Aggregate.interpretation 0)).card) :
    (n : ℝ) ≤ Real.logb 2 (Fintype.card (Key c.program)) +
      2 * (Nat.clog 2 K : ℝ) + 7 := by
  have positive : 0 < Fintype.card (Key c.program) :=
    Fintype.card_pos_iff.mpr ⟨key c.program ∅ (fun _ => false)⟩
  have outputPositive : 1 ≤ Fintype.card (OutputKey c.program) := by
    simp only [OutputKey, Fintype.card_prod, Fintype.card_bool]
    lia
  have rounded := input_le_summaryBits_of_circuit c free dense
  have rounded' : (n : ℝ) ≤ (Nat.clog 2 (Fintype.card (OutputKey c.program)) : ℝ) +
      2 * (Nat.clog 2 K : ℝ) + 5 := by exact_mod_cast rounded
  have ceiling : (Nat.clog 2 (Fintype.card (OutputKey c.program)) : ℝ) <
      Real.logb 2 (Fintype.card (OutputKey c.program)) + 1 := by
    rw [← Real.natCeil_logb_natCast 2 (Fintype.card (OutputKey c.program))]
    apply Nat.ceil_lt_add_one
    exact Real.logb_nonneg one_lt_two (by exact_mod_cast outputPositive)
  have logarithm : Real.logb 2 (Fintype.card (OutputKey c.program)) =
      Real.logb 2 (Fintype.card (Key c.program)) + 1 := by
    simp only [OutputKey, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.logb_mul (by exact_mod_cast positive.ne') (by norm_num),
      Real.logb_self_eq_one one_lt_two]
  rw [logarithm] at ceiling
  linarith

/-- The finite capacity bound stated for a circuit computing a specified function. -/
theorem input_le_capacity_of_computes
    (c : Circuit (Algebraic.Aggregate.signature State) n 1) {f : Cslib.BooleanFunction n}
    (computes : c.Computes Algebraic.Aggregate.interpretation (fun x _ => f x))
    {K : Nat} (free : RectangleFree f K) (dense : 2 ^ (n - 2) ≤ (accepting f).card) :
    n ≤ capacity c.program + 2 * Nat.clog 2 K + 6 := by
  have heq : c.outputFunction Algebraic.Aggregate.interpretation 0 = f := by
    funext x
    exact congrFun (computes x) 0
  apply input_le_capacity_of_circuit c
  · rwa [heq]
  · rwa [heq]

end Algebraic.Cutwidth.Aggregate
