/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Capacity.Circuit.Count
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact real-valued aggregate capacity

The logarithm of the joint key cardinality charges the real logarithm of each
register size. It incurs no per-register rounding or guessed-output-bit cost.
-/

@[expose] public section

namespace Algebraic.Aggregate.Capacity

variable {J : Type} {State : J → Type} {n g : ℕ}

instance [∀ j, CommMonoid (State j)] (op : Op State) : Nonempty (SummaryRegister op) := by
  cases op <;> dsimp [SummaryRegister] <;> infer_instance

/-- Exact bit capacity, without rounding the logarithms of register sizes. -/
noncomputable def realCapacity [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) : ℝ :=
  ordinaryCount p + ∑ gate : SpecialGate p, Real.logb 2 (Fintype.card (Register p gate))

/-- Binary summary registers have two states; special ones retain their original register. -/
theorem card_summaryRegister_eq [∀ j, Fintype (State j)] (op : Op State) :
    Fintype.card (SummaryRegister op) =
      if op.isSpecial then Fintype.card op.Register else 2 := by
  cases op with
  | binary f => exact (Fintype.card_congr (Equiv.refl Bool)).trans Fintype.card_bool
  | special => rfl

/-- The joint summary cardinality is the exact product of all charged register sizes. -/
theorem card_key_eq [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Fintype.card (Key p) = 2 ^ ordinaryCount p * Fintype.card (Registers p) := by
  rw [Fintype.card_pi, ← Fintype.prod_subtype_mul_prod_subtype
    (fun gate : Fin g => (p.lines gate).op.isSpecial = true)]
  have hs : (∏ gate : SpecialGate p, Fintype.card (SummaryRegister (p.lines gate).op)) =
      Fintype.card (Registers p) := by
    rw [card_registers]
    apply Finset.prod_congr rfl
    intro gate _
    simp [card_summaryRegister_eq, gate.property, Register]
  have hb : (∏ gate : {gate : Fin g // ¬ (p.lines gate).op.isSpecial = true},
      Fintype.card (SummaryRegister (p.lines gate).op)) = 2 ^ ordinaryCount p := by
    calc
      _ = ∏ _ : {gate : Fin g // ¬ (p.lines gate).op.isSpecial = true}, 2 := by
        apply Finset.prod_congr rfl
        intro gate _
        simp [card_summaryRegister_eq, gate.property]
      _ = 2 ^ ordinaryCount p := by
        simp only [Finset.prod_const, Finset.card_univ]
        congr 1
        simpa [ordinaryCount, SpecialGate, specialCount] using
          Fintype.card_subtype_compl (fun gate : Fin g => (p.lines gate).op.isSpecial = true)
  rw [hs, hb, Nat.mul_comm]

/-- The unrounded capacity is exactly the base-two logarithm of the key space. -/
theorem logb_card_key_eq_realCapacity [∀ j, CommMonoid (State j)]
    [∀ j, Fintype (State j)] (p : Program (signature State) n g) :
    Real.logb 2 (Fintype.card (Key p)) = realCapacity p := by
  have hr : 0 < Fintype.card (Registers p) := Fintype.card_pos_iff.mpr ⟨fun _ => 1⟩
  rw [card_key_eq, Nat.cast_mul, Nat.cast_pow,
    Real.logb_mul (by norm_num) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)), Real.logb_pow]
  simp only [Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  unfold realCapacity
  congr 1
  rw [card_registers, Nat.cast_prod, Real.logb_prod]
  intro gate _
  exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))

/-- Bounding all special registers by `states` bounds exact capacity per gate. -/
theorem realCapacity_le_of_register_card [∀ j, CommMonoid (State j)]
    [∀ j, Fintype (State j)] (p : Program (signature State) n g)
    (states : ℕ) (hs : 2 ≤ states)
    (h : ∀ gate : SpecialGate p, Fintype.card (Register p gate) ≤ states) :
    realCapacity p ≤ (g : ℝ) * Real.logb 2 states := by
  have base : (1 : ℝ) < 2 := by norm_num
  have hlog : (1 : ℝ) ≤ Real.logb 2 states := by
    rw [← Real.logb_self_eq_one base]
    apply Real.logb_le_logb_of_le base (by norm_num)
    exact_mod_cast hs
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun gate _ =>
    Real.logb_le_logb_of_le base
      (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (⟨1⟩ : Nonempty (Register p gate))))
      (Nat.cast_le.mpr (h gate)))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  change _ ≤ (specialCount p : ℝ) * Real.logb 2 states at hsum
  have hord : (ordinaryCount p : ℝ) ≤ ordinaryCount p * Real.logb 2 states :=
    le_mul_of_one_le_right (Nat.cast_nonneg _) hlog
  calc
    realCapacity p ≤ ordinaryCount p + specialCount p * Real.logb 2 states :=
      add_le_add le_rfl hsum
    _ ≤ ordinaryCount p * Real.logb 2 states + specialCount p * Real.logb 2 states :=
      add_le_add hord le_rfl
    _ = (g : ℝ) * Real.logb 2 states := by
      rw [← add_mul, ← Nat.cast_add, ordinaryCount_add_specialCount]

/-- Rounding each register logarithm can only increase the exact joint capacity. -/
theorem realCapacity_le_capacity [∀ j, Fintype (State j)]
    (p : Program (signature State) n g) : realCapacity p ≤ capacity p := by
  unfold realCapacity capacity
  push_cast
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro gate _
  rw [← Real.natCeil_logb_natCast 2 (Fintype.card (Register p gate))]
  exact Nat.le_ceil _

end Algebraic.Aggregate.Capacity
