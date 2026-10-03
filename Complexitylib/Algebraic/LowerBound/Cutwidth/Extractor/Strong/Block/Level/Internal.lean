/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Level.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Defs
public import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep.Defs
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Condenser
import
  Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Block.Splitting.Iterated.Family
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Mixture
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability
import Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.SeedStep
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

/-!
# Carrying a joint approximation through one condense-then-split level

Average the block-condensation comparisons over earlier seeds, retaining
the fresh seed inside each comparison. Splitting contracts this error and
adds its own per-block cost. A previous joint approximation also contracts
through the full retained-seed step, so all three errors add.
-/

public section

namespace Algebraic.Cutwidth.Extractor.Internal

theorem weightedStrongSeededCondenser_condenseSplit {Earlier Fresh α β : Type*}
    [Fintype Earlier] [Nonempty Earlier] [Fintype Fresh] [Fintype α] [Fintype β]
    {C : α → Fresh → β × β} {Kin k : Nat} {ε : ℝ}
    (cond : WeightedStrongSeededCondenser C Kin (2 ^ k) ε)
    {t m s e : Nat} {η : ℝ} (p : Earlier → (Fin t → α) → ℝ)
    (actual : Earlier × (Fin t → α) → ℝ)
    (source : ∀ y, IsBlockSource (p y) Kin)
    (close : weightDist actual (seedFamilyWeight p) ≤ η)
    (card : Fintype.card β = 2 ^ m) (width : s ≤ m) (entropy : m + s + e ≤ k) :
    ∃ q : Earlier × Fresh → (Fin (2 * t) → β) → ℝ,
      (∀ sy, IsBlockSource (q sy) (2 ^ s)) ∧
        weightDist (retainedSeedStep (fun _ => condenseSplitMap C t) actual)
          (seedFamilyWeight q) ≤ η + (t : ℝ) * (ε + ((2 : ℝ) ^ e)⁻¹) := by
  classical
  choose r witnesses condensedClose using fun y => cond.block (source y)
  let a : Earlier → Fresh → (Fin t → β × β) → ℝ :=
    fun y z => mapWeight (fun x i => C (x i) z) (p y)
  have condensed :
      weightDist (seedFamilyWeight (fun sy : Earlier × Fresh => a sy.1 sy.2))
        (seedFamilyWeight (fun sy : Earlier × Fresh => r sy.1 sy.2)) ≤ (t : ℝ) * ε := by
    rw [weightDist_seedFamilyWeight_product a r]
    have positive : (0 : ℝ) < Fintype.card Earlier := by
      exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ positive).mpr
    calc
      _ ≤ ∑ _y : Earlier, (t : ℝ) * ε :=
        Finset.sum_le_sum fun y _ => condensedClose y
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  obtain ⟨q, outputSource, splitClose⟩ := exists_split_pow_two_seedFamily
    (fun sy : Earlier × Fresh => r sy.1 sy.2)
    (fun sy => witnesses sy.1 sy.2) card width entropy
  let split : (Earlier × Fresh) × (Fin t → β × β) →
      (Earlier × Fresh) × (Fin (2 * t) → β) :=
    fun syx => (syx.1, splitBlockEquiv β t syx.2)
  have stepIdentity :
      retainedSeedStep (fun _ => condenseSplitMap C t) (seedFamilyWeight p) =
        mapWeight split (seedFamilyWeight (fun sy : Earlier × Fresh => a sy.1 sy.2)) := by
    dsimp only [split]
    rw [retainedSeedStep_seedFamilyWeight,
      mapWeight_seedFamilyWeight
        (fun (_ : Earlier × Fresh) (x : Fin t → β × β) => splitBlockEquiv β t x)]
    congr 1
    funext sy
    exact (mapWeight_comp (p sy.1) (fun x i => C (x i) sy.2) (splitBlockEquiv β t)).symm
  have splitCondensed :
      weightDist (retainedSeedStep (fun _ => condenseSplitMap C t) (seedFamilyWeight p))
        (mapWeight split (seedFamilyWeight (fun sy : Earlier × Fresh => r sy.1 sy.2))) ≤
          (t : ℝ) * ε := by
    rw [stepIdentity]
    exact (weightDist_map_le _ _ split).trans condensed
  have exactInputClose := (weightDist_triangle
    (retainedSeedStep (fun _ => condenseSplitMap C t) (seedFamilyWeight p))
    (mapWeight split (seedFamilyWeight (fun sy : Earlier × Fresh => r sy.1 sy.2)))
    (seedFamilyWeight q)).trans (add_le_add splitCondensed splitClose)
  have previousClose :=
    (retainedSeedStep_dist_le (fun _ => condenseSplitMap C t) actual (seedFamilyWeight p)).trans
      close
  refine ⟨q, outputSource, ?_⟩
  calc
    _ ≤ weightDist (retainedSeedStep (fun _ => condenseSplitMap C t) actual)
          (retainedSeedStep (fun _ => condenseSplitMap C t) (seedFamilyWeight p)) +
        weightDist (retainedSeedStep (fun _ => condenseSplitMap C t) (seedFamilyWeight p))
          (seedFamilyWeight q) := weightDist_triangle _ _ _
    _ ≤ η + ((t : ℝ) * ε + (t : ℝ) * ((2 : ℝ) ^ e)⁻¹) :=
      add_le_add previousClose exactInputClose
    _ = _ := by ring

end Algebraic.Cutwidth.Extractor.Internal
