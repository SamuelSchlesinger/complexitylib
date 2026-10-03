/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Conditioning
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Condenser
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Internal.Hybrid
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser.Repair
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Choose

/-!
# Shared-seed block condensation by head/tail induction

Condition on the original head and first correct the conditional tails.
Repairing the head while preserving the latent original value then keeps
the corrected tails as block sources. Exact conditional distance averaging
adds one condenser error per source block.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededCondenser_block {α Seed Ω : Type*}
    [Fintype α] [Fintype Seed] [Fintype Ω]
    {C : α → Seed → Ω} {Kin Kout : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin Kout ε)
    {t : Nat} {p : (Fin t → α) → ℝ} (source : IsBlockSource p Kin) :
    ∃ q : Seed → (Fin t → Ω) → ℝ,
      (∀ y, IsBlockSource (q y) Kout) ∧
        weightDist (weightedSeededOutput p (fun x y i => C (x i) y))
          (seedFamilyWeight q) ≤ (t : ℝ) * ε := by
  classical
  induction t with
  | zero =>
    obtain ⟨q, hq, output⟩ := blockCondenser_zero C p source.probability Kout
    refine ⟨q, hq, ?_⟩
    rw [output, weightDist_self]
    simp
  | succ t ih =>
    obtain ⟨w, tails, hw, cap, sources, factor⟩ := source.exists_head_tail
    choose q hq tailError using fun a => ih (sources a)
    obtain ⟨target, targetProbability, targetCap, headError⟩ := cond w hw cap
    choose r hr headMarginal repairDist using fun y =>
      exists_block_tail_replacement t Kout w (fun a => q a y)
        (fun a => C a y) (target y) hw (fun a => hq a y)
        (targetProbability y) (targetCap y)
    let hybrid : Seed → (Fin (t + 1) → Ω) → ℝ := fun y =>
      mapWeight (fun az : α × (Fin t → Ω) =>
        (Fin.cons (C az.1 y) az.2 : Fin (t + 1) → Ω))
        (fun az => w az.1 * q az.1 y az.2)
    have factor' : p = fun x => w (x 0) * tails (x 0) (Fin.tail x) := by
      funext x
      simpa only [Fin.cons_self_tail] using factor (x 0) (Fin.tail x)
    have hybridError :
        weightDist (weightedSeededOutput p (fun x y i => C (x i) y))
          (seedFamilyWeight hybrid) ≤ (t : ℝ) * ε := by
      rw [factor']
      exact blockCondenser_hybrid_le C w hw tails q tailError
    have repairError : weightDist (seedFamilyWeight hybrid) (seedFamilyWeight r) ≤ ε := by
      calc
        _ = (∑ y, weightDist (hybrid y) (r y)) / (Fintype.card Seed : ℝ) :=
          weightDist_seedFamilyWeight hybrid r
        _ = weightDist (weightedSeededOutput w C) (seedFamilyWeight target) := by
          rw [weightDist_weightedSeededOutput_seedFamilyWeight]
          congr 1
          exact Finset.sum_congr rfl (fun y _ => repairDist y)
        _ ≤ ε := headError
    refine ⟨r, hr, ?_⟩
    have bound := (weightDist_triangle
      (weightedSeededOutput p (fun x y i => C (x i) y))
      (seedFamilyWeight hybrid) (seedFamilyWeight r)).trans
      (add_le_add hybridError repairError)
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using bound

end Algebraic.Cutwidth.Extractor.Internal
